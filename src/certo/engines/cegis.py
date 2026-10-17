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
    """CEGIS over the spec's bounded domain.

    `on_round`, a callable, receives every round: a REJECTED one as
    `{"round", "implementation", "counterexample"}`, and the ACCEPTED one --
    the candidate no input refutes -- with `"counterexample": None` and
    `"accepted": True`. So it is called `iterations` times on success."""
    if getattr(spec, "minimize", None) is not None or \
            getattr(spec, "maximize", None) is not None:
        return synth_optimal(spec, limits, on_round)
    lim = limits or Limits()
    t0 = time.perf_counter()
    deadline = t0 + lim.timeout_ms / 1000.0
    # The run's deadline too, on this loop's own clock (`perf_counter`).
    from .. import clock

    left = clock.remaining_s()
    if left is not None:
        deadline = min(deadline, t0 + left)

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

    scope = spec.scope_data() if hasattr(spec, "scope_data") else None

    def done(status, verdict, detail, cert=None, k=0, impl=None):
        meta = {"iterations": k, "counterexamples": len(counterexamples),
                "domain": domain, "trace": trace}
        if scope:
            # WHAT the search was about travels with what it found, and in
            # the certificate, where a reader of the result looks.
            meta["scope"] = scope
            if cert is not None:
                cert.payload["scope"] = scope
            if (cert is not None and cert.kind == "cegis_none"
                    and scope.get("counterexamples") == "relaxation"):
                detail = detail.rstrip(". ") + ". " + t("engine.synth.relaxed_none")
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
                if on_round is not None:
                    # The ACCEPTED round is a round too: a caller counting
                    # callbacks saw one fewer than `iterations` and no sign
                    # of the candidate that survived.
                    on_round({"round": k + 1, "implementation": impl_assign,
                              "counterexample": None, "accepted": True})
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
            breaks = _which_fail(spec, behav, fixed, ce_concrete, helper_vars, lim)
        finally:
            ce_solver.pop()  # (d) del original: el pop faltaba en dos ramas

        counterexamples.append(ce_assign)
        trace.append({"round": k + 1, "implementation": impl_assign,
                      "counterexample": ce_assign})
        if breaks is not None:
            # WHICH obligation this input breaks -- access, or payment.
            trace[-1]["breaks"] = breaks
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


def _which_fail(spec, behav, fixed, ce_concrete, helper_vars, lim):
    """The named obligations this counterexample breaks, for a `correctness`
    given as a dict: obligation i is broken when no helper saves IT at this
    input. None when the correctness is one formula."""
    names = spec.obligation_names() if hasattr(spec, "obligation_names") else None
    if not names:
        return None
    out = []
    for name in names:
        s = z3.Solver()
        lim.apply_to(s)
        s.add(*fixed)
        s.add(*[x == v for x, v in ce_concrete])
        s.add(behav)
        s.add(_no_helper_saves(behav, spec.correctness[name], helper_vars))
        if s.check() == z3.sat:
            out.append(name)
    return out


def synth_optimal(spec, limits=None, on_round=None) -> Result:
    """The BEST candidate: CEGIS, then CEGIS again under `objective < best`
    (or `>`), until no candidate exists. The last found works; the last
    search proves nothing better does -- `synth_optimum`, the two
    certificates together, each verified as it is."""
    import dataclasses

    from ..certificate import synth_optimum_certificate

    lim = limits or Limits()
    t0 = time.perf_counter()
    obj = spec.minimize if spec.minimize is not None else spec.maximize
    sense = "min" if spec.minimize is not None else "max"
    if not (z3.is_expr(obj) and z3.is_int(obj)):
        return Result("synth", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE, ENGINE,
                      0.0, None, detail=t("engine.synth.objective_int"))
    base = spec.impl_constraints if spec.impl_constraints is not None else z3.BoolVal(True)
    plain = dataclasses.replace(spec, minimize=None, maximize=None)
    best, rounds, path = None, 0, []
    current = plain
    for _ in range(max(1, lim.max_iterations)):
        res = synth(current, lim, on_round)
        rounds += res.meta.get("iterations", 0)
        if res.verdict is Verdict.PROVED and res.certificate is not None:
            impl = res.certificate.payload["implementation"]
            subs = [(z3util_const(n, s), z3util_value(s, v)) for n, (s, v) in impl.items()]
            value = z3.simplify(z3.substitute(obj, *subs))
            best = (value.as_long(), res)
            path.append(best[0])
            better = obj < best[0] if sense == "min" else obj > best[0]
            current = dataclasses.replace(plain, impl_constraints=z3.And(base, better))
            continue
        ms = (time.perf_counter() - t0) * 1000
        if res.verdict is Verdict.UNSATISFIABLE and res.certificate is not None:
            if best is None:
                return res          # no candidate at all: the plain answer
            value, found = best
            cert = synth_optimum_certificate(
                found.certificate.to_dict(), res.certificate.to_dict(),
                z3util.smt2(base), z3util.smt2(obj == value), sense, value)
            if found.certificate.payload.get("scope"):
                cert.payload["scope"] = found.certificate.payload["scope"]
            meta = dict(found.meta, value=value, sense=sense, path=path,
                        rounds=rounds)
            return Result("synth", Status.SAT, Verdict.PROVED, ENGINE, ms, cert,
                          t("engine.synth.optimum", sense=sense, value=value,
                            steps=len(path), rounds=rounds), meta=meta)
        # stopped: the best so far is reported, its optimality is not
        detail = res.detail
        if best is not None:
            detail = t("engine.synth.optimum_open", value=best[0], sense=sense) + " " + detail
        res.detail = detail
        res.meta["best_so_far"] = None if best is None else best[0]
        return res
    return Result("synth", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE, ENGINE,
                  (time.perf_counter() - t0) * 1000, None,
                  t("engine.synth.max_iter", n=lim.max_iterations))


def implementation_of(cert) -> dict:
    """The candidate a synthesis certificate is about, `{name: [sort,
    value]}`: a `cegis` keeps it in its payload, a `synth_optimum` in the
    half that FOUND it. `synth --prove-candidate` read the first shape only
    and died with KeyError on every optimised synthesis."""
    d = cert.to_dict() if hasattr(cert, "to_dict") else (cert or {})
    p = d.get("payload") or {}
    if d.get("kind") == "synth_optimum":
        p = (p.get("found") or {}).get("payload") or {}
    return dict(p.get("implementation") or {})


def z3util_const(name, sort):
    from ..certificate import _const

    return _const(z3, name, sort)


def z3util_value(sort, val):
    from ..certificate import _value

    return _value(z3, sort, val)


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
