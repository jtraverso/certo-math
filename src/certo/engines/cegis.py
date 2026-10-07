"""Motor CEGIS: sintesis guiada por contraejemplos.

Reimplementacion del algoritmo de marcelwa/CEGIS, no del codigo. El original
(C++, 9 commits, ejemplo vacio, sin tests) arrastra cuatro fallos que aqui no
se heredan:

  (a) desfase de uno entre el id del contraejemplo y el usado al sustituir,
      que desconectaba las restricciones del contraejemplo de la formula;
  (b) puntero colgante en `(templ % i % id).str().c_str()`;
  (c) `boost::format` reutilizado dentro de un bucle (falla con >1 variable);
  (d) contador de contraejemplos `static`, compartido entre instancias.

Ademas se sustituyen las entradas por sus VALORES concretos en vez de crear
constantes frescas y forzarlas con una igualdad: menos variables, formulas mas
pequenas, y el desfase (a) deja de ser posible por construccion.
"""
from __future__ import annotations

import time

import z3

from .. import z3util
from ..certificate import cegis_certificate, cegis_none_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict, classify_unknown

ENGINE = "cegis/z3:" + z3.get_version_string()


def _remaining_ms(deadline):
    return max(1, int((deadline - time.perf_counter()) * 1000))


def _no_helper_saves(behav, corr, helper_vars):
    """`behav AND forall helpers . NOT corr` -- or, with no helpers, the
    plain `behav AND NOT corr`."""
    if not helper_vars:
        return z3.And(behav, z3.Not(corr))
    return z3.And(behav, z3.ForAll(list(helper_vars), z3.Not(corr)))


def synth(spec, limits: Limits | None = None, on_round=None) -> Result:
    lim = limits or Limits()
    t0 = time.perf_counter()
    deadline = t0 + lim.timeout_ms / 1000.0

    impl_cons, behav, corr = spec.normalized()
    impl_vars = list(spec.impl_vars)
    input_vars = list(spec.input_vars)
    helper_vars = list(spec.helper_vars)

    impl_solver = z3.Solver()
    ce_solver = z3.Solver()
    for s in (impl_solver, ce_solver):
        lim.apply_to(s)
    impl_solver.add(impl_cons)
    # A COUNTEREXAMPLE IS AN INPUT NO HELPER SAVES. The contract is
    # exists impl . forall input . exists helper; with the helpers left free
    # in `behav AND NOT corr` the search found an input where SOME helper
    # failed -- a bad helper, not a bad input -- and a valid formula
    # (h = x) never converged. Sound either way, since "no input fails for
    # any helper" is the stronger statement; complete only with the order
    # of the quantifiers kept.
    ce_solver.add(_no_helper_saves(behav, corr, helper_vars))

    counterexamples = []
    trace = []
    spec_smt2 = {
        "impl_constraints": z3util.smt2(impl_cons),
        "behavior": z3util.smt2(behav),
        "correctness": z3util.smt2(corr),
    }

    domain = str(z3.simplify(behav)).replace("\n", " ")
    if len(domain) > 200:
        domain = domain[:197] + "..."

    def done(status, verdict, detail, cert=None, k=0, impl=None):
        meta = {"iterations": k, "counterexamples": len(counterexamples),
                "domain": domain, "trace": trace}
        if impl is not None:
            # El objeto encontrado es el resultado, no un detalle del
            # certificado: tiene que verse sin abrir un JSON.
            meta["implementation"] = {n: v for n, (_, v) in impl.items()}
        return Result(
            "synth", status, verdict, ENGINE,
            (time.perf_counter() - t0) * 1000, cert, detail, meta=meta,
        )

    for k in range(lim.max_iterations):
        if time.perf_counter() >= deadline:
            return done(Status.TIMEOUT, Verdict.INCONCLUSIVE,
                        t("engine.synth.timeout", rounds=k), k=k)

        # --- 1. proponer una implementacion compatible con lo visto -------
        impl_solver.set("timeout", _remaining_ms(deadline))
        r = impl_solver.check()
        if r == z3.unsat:
            # THE NEGATIVE CARRIES ITS PROOF: the constraints and one instance
            # per counterexample are contradictory, and every instance is a
            # consequence of the contract. It used to come back with no
            # certificate at all.
            cert = cegis_none_certificate(
                spec_smt2,
                [[str(v), z3util.sort_name(v)] for v in impl_vars],
                [[str(v), z3util.sort_name(v)] for v in input_vars],
                [[str(h), z3util.sort_name(h)] for h in helper_vars],
                counterexamples)
            return done(Status.UNSAT, Verdict.UNSATISFIABLE,
                        t("engine.synth.none", ces=len(counterexamples)),
                        cert, k=k)
        if r != z3.sat:
            st = classify_unknown(impl_solver.reason_unknown())
            return done(st, Verdict.INCONCLUSIVE,
                        t("engine.synth.impl_unknown",
                          reason=impl_solver.reason_unknown()), k=k)

        model = impl_solver.model()
        impl_assign = z3util.assignment(model, impl_vars)
        fixed = [v == model.eval(v, model_completion=True) for v in impl_vars]

        # --- 2. buscar un contraejemplo para ESA implementacion -----------
        ce_solver.push()
        try:
            ce_solver.add(*fixed)
            ce_solver.set("timeout", _remaining_ms(deadline))
            r2 = ce_solver.check()

            if r2 == z3.unsat:
                cert = cegis_certificate(impl_assign, counterexamples, spec_smt2, k + 1,
                                         helpers=[[str(h), z3util.sort_name(h)]
                                                  for h in helper_vars])
                return done(Status.SAT, Verdict.PROVED,
                            t("engine.synth.found", rounds=k + 1,
                              ces=len(counterexamples)),
                            cert, k + 1, impl=impl_assign)
            if r2 != z3.sat:
                st = classify_unknown(ce_solver.reason_unknown())
                return done(st, Verdict.INCONCLUSIVE,
                            t("engine.synth.ce_unknown",
                              reason=ce_solver.reason_unknown()), k=k)

            ce_model = ce_solver.model()
            ce_assign = z3util.assignment(ce_model, input_vars)
            ce_concrete = [
                (x, ce_model.eval(x, model_completion=True)) for x in input_vars
            ]
        finally:
            ce_solver.pop()  # (d) del original: el pop faltaba en dos ramas

        counterexamples.append(ce_assign)
        trace.append({"round": k + 1, "implementation": impl_assign,
                      "counterexample": ce_assign})
        if on_round is not None:
            on_round(trace[-1])

        # --- 3. aprender: instanciar la spec en ese contraejemplo ---------
        # `behav IMPLIES corr`, not `behav AND corr`. The counterexample is in
        # the domain of THIS candidate; when the domain depends on the
        # implementation (`x >= k`), requiring it to be in the domain of
        # every later candidate excluded the ones it is not an input of --
        # and k = 1 was refuted by x = 0, found against k = 0: "no object
        # satisfies the specification" for a spec k = 1 satisfies.
        subs = list(ce_concrete)
        for h in helper_vars:
            subs.append((h, z3.Const("{}__ce{}".format(h, k), h.sort())))
        impl_solver.add(z3.substitute(z3.Implies(behav, corr), *subs))

    return done(Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                t("engine.synth.max_iter", n=lim.max_iterations),
                k=lim.max_iterations)


# ---------------------------------------------------------------------------
# de candidato acotado a obligacion universal
# ---------------------------------------------------------------------------


def prove_candidate(spec, impl_assign, limits: Limits | None = None):
    """Fija el objeto sintetizado y demuestra el enunciado GENERAL.

    Cierra a mano el hueco que queda tras `synth`: la sintesis vive en un
    dominio acotado, y pasar de ahi al enunciado universal era un paso manual
    donde se cuelan los errores.

    La spec tiene que decir cual es ese enunciado, porque no es deducible:
    normalmente cambia el dominio Y el sort (se busca sobre enteros acotados,
    se demuestra sobre los reales, que es donde el polinomio es decidible).
    """
    from . import smt

    impl_assign = candidate_pairs(spec, impl_assign)
    values = {n: v for n, (_, v) in impl_assign.items()}
    uspec = universal_spec(spec, impl_assign)
    res = smt.prove(uspec, limits)
    res.command = "prove_candidate"
    res.meta["candidate"] = values
    return res


def candidate_pairs(spec, impl_assign) -> dict:
    """`{name: (sort, value)}`, from either shape a candidate comes in.

    `result.meta["implementation"]` is `{name: value}`, the certificate's is
    `{name: [sort, value]}`; passing the first raised `cannot unpack
    non-iterable int object`. The sort is read from the spec, and a name the
    spec does not declare -- or a declared one left out -- is refused by name.
    """
    sorts = {str(v): z3util.sort_name(v) for v in spec.impl_vars}
    out = {}
    for name, val in (impl_assign or {}).items():
        if name not in sorts:
            raise ValueError(t("engine.synth.candidate_unknown", name=name,
                               known=", ".join(sorts)))
        if isinstance(val, (list, tuple)) and len(val) == 2:
            out[name] = (val[0], val[1])
        else:
            out[name] = (sorts[name], val)
    missing = [n for n in sorts if n not in out]
    if missing:
        raise ValueError(t("engine.synth.candidate_missing",
                           names=", ".join(missing)))
    return out


def universal_spec(spec, impl_assign):
    """The universal statement for THIS candidate: the spec's `universal`, or
    its correctness with the candidate substituted under
    `universal_behavior`. One definition, used by the producer and by
    `verify`, which rebuilds it to tie the proof to the candidate."""
    values = {n: v for n, (_, v) in impl_assign.items()}

    if spec.universal is not None:
        uspec = spec.universal(values)
    elif spec.universal_behavior is not None:
        from ..spec import Spec

        _, _, corr = spec.normalized()
        subs = [(z3util.const(n, srt), z3util.value_of(srt, v))
                for n, (srt, v) in impl_assign.items()]
        uspec = Spec(title="obligacion universal")
        # The candidate is substituted in the DOMAIN too. With `x >= k` left
        # as it was, the obligation read "for every k" -- k = 1 was refuted
        # by k = 0 -- which is not the candidate's statement.
        uspec.assume("dominio_universal",
                     z3.substitute(spec.universal_behavior, *subs) if subs
                     else spec.universal_behavior)
        claim = z3.substitute(corr, *subs)
        # The helpers stay EXISTENTIAL in the general statement too: proving
        # the correctness for EVERY helper value claimed more than the spec.
        helpers = list(getattr(spec, "helper_vars", []) or [])
        uspec.claim(z3.Exists(helpers, claim) if helpers else claim)
    else:
        raise ValueError(t("engine.synth.no_universal"))
    return uspec
