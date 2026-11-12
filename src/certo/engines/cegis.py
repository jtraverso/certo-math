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



def _in_original(original, point):
    """True, False, or None (it mentions something the point does not fix)."""
    import z3

    v = z3.simplify(z3.substitute(original, *point)) if point else z3.simplify(original)
    if z3.is_true(v):
        return True
    if z3.is_false(v):
        return False
    return None

def _plain_values(assign) -> dict:
    """`{name: (sort, text)}` as Python values: int, Fraction, bool."""
    from fractions import Fraction

    out = {}
    for n, (sort, v) in assign.items():
        if sort == "Int":
            out[n] = int(v)
        elif sort == "Real":
            out[n] = Fraction(str(v))
        elif sort == "Bool":
            out[n] = str(v).lower() == "true"
        else:
            out[n] = v
    return out


def _as_z3(var, value):
    """A Python value as a z3 value of `var`'s sort."""
    from fractions import Fraction

    if var.sort() == z3.IntSort():
        return z3.IntVal(int(value))
    if var.sort() == z3.RealSort():
        return z3.RealVal(str(Fraction(str(value))))
    if var.sort() == z3.BoolSort():
        return z3.BoolVal(bool(value) if not isinstance(value, str)
                          else value.lower() == "true")
    raise ValueError("unsupported sort: {}".format(var.sort()))


def _sha(obj) -> str:
    import hashlib
    import json

    text = json.dumps(obj, sort_keys=True, default=str, ensure_ascii=False)
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _domain_check(spec, impl_assign):
    """Run the external verifier on one candidate. `(valid, ce, record)`:
    valid True / False / None (it raised), ce `{input: value}` or None, and
    the record the trace and the certificate keep."""
    fn = spec.domain_verifier
    values = _plain_values(impl_assign)
    version = (getattr(spec, "domain_verifier_version", "")
               or getattr(fn, "version", None) or getattr(fn, "__version__", None)
               or "")
    record = {"verifier": getattr(fn, "__qualname__", type(fn).__name__),
              "version": str(version),
              "input_sha256": _sha({n: str(v) for n, v in values.items()})}
    try:
        got = fn(values)
    except Exception as e:  # noqa: BLE001 -- the program is the user's
        record.update(valid=None, error="{}: {}".format(type(e).__name__, e),
                      result_sha256=None)
        return None, None, record
    if isinstance(got, dict):
        valid = bool(got.get("valid", False))
        ce = got.get("counterexample") or got.get("input")
        reason = got.get("reason")
    else:
        valid, ce, reason = (got is None or got is True), None, None
    record.update(valid=valid, result_sha256=_sha(got))
    if reason:
        record["reason"] = str(reason)[:200]
    if ce is not None:
        record["counterexample"] = {str(k): str(v) for k, v in ce.items()}
    return valid, ce, record


def _remaining_ms(deadline):
    return max(1, int((deadline - time.perf_counter()) * 1000))


def _no_helper_saves(behav, corr, helper_vars):
    """`behav AND forall helpers . NOT corr` -- or, with no helpers, the
    plain `behav AND NOT corr`."""
    if not helper_vars:
        return z3.And(behav, z3.Not(corr))
    return z3.And(behav, z3.ForAll(list(helper_vars), z3.Not(corr)))


#: Helper witnesses tried for ONE candidate before the counterexample search
#: falls back to the quantified query. Each try is two quantifier-free calls.
WITNESS_ROUNDS = 64
#: The witnesses kept across candidates (each is a constraint on every later
#: counterexample query); past this the oldest are no longer added.
WITNESS_POOL = 512
#: An input bounded by this is called bounded: the reading of a result whose
#: inputs are not (`input_domain`).
BIG = 10 ** 15


def _rlimit(s) -> int:
    """z3's deterministic work counter for this solver so far (0 if absent)."""
    try:
        st = s.statistics()
        return int(st.get_key_value("rlimit count")) if "rlimit count" in st.keys() else 0
    except Exception:  # noqa: BLE001
        return 0


def _helpers_in(expr, helper_vars) -> bool:
    names = {str(h) for h in helper_vars}
    return any(str(c) in names for c in z3util.free_consts(expr))


def _with(corr, witness):
    """`corr` with the helpers replaced by one witness's values."""
    return z3.substitute(corr, *witness) if witness else corr


def _ce_search(behav, corr, fixed, input_vars, helper_vars, pool, lim,
               deadline, work, ms):
    """A counterexample for the candidate `fixed` WITHOUT QUANTIFIERS.

    `exists x . behav AND forall h . not corr` is the classic 2QBF, and z3's
    quantifier engine answered `incomplete quantifiers` or `canceled` on
    domains of four values (5..8). The same question as a loop of plain
    queries: an input no KNOWN helper value saves; then, with that input
    concrete, a helper value that saves it. None -> a real counterexample;
    one -> it joins the witnesses and the loop asks again. With finitely many
    helper values it ends; the witnesses that closed it are the certificate's
    strategy -- `verify` checks them with one quantifier-free query.

    `("none", None)` no counterexample (every input saved by a witness),
    `("ce", model)`, `("unknown", (phase, reason))`, or `("fallback", None)`
    when WITNESS_ROUNDS tries did not close it. `pool` is extended in place.
    """
    sx = z3.Solver()
    lim.apply_to(sx)
    sx.add(behav, *fixed)
    for w in pool[-WITNESS_POOL:]:
        sx.add(z3.Not(_with(corr, w)))
    try:
        for _ in range(WITNESS_ROUNDS):
            t1 = time.perf_counter()
            sx.set("timeout", _remaining_ms(deadline))
            r = sx.check()
            ms["counterexample"] += (time.perf_counter() - t1) * 1000
            if r == z3.unsat:
                return "none", None
            if r != z3.sat:
                return "unknown", ("counterexample", sx.reason_unknown())
            m = sx.model()
            point = [x == m.eval(x, model_completion=True) for x in input_vars]
            sh = z3.Solver()
            lim.apply_to(sh)
            sh.set("timeout", _remaining_ms(deadline))
            sh.add(*fixed, *point, corr)
            t1 = time.perf_counter()
            r2 = sh.check()
            ms["helpers"] += (time.perf_counter() - t1) * 1000
            work["rlimit"] += _rlimit(sh)
            if r2 == z3.unsat:
                return "ce", m
            if r2 != z3.sat:
                return "unknown", ("helpers", sh.reason_unknown())
            hm = sh.model()
            w = [(h, hm.eval(h, model_completion=True)) for h in helper_vars]
            pool.append(w)
            sx.add(z3.Not(_with(corr, w)))
        return "fallback", None
    finally:
        work["rlimit"] += _rlimit(sx)


def _input_domain(behav, fixed, input_vars, lim, deadline):
    """Which inputs the candidate's domain leaves UNBOUNDED (beyond BIG).
    One query when every input is bounded, the common case; one per input
    otherwise. `{"bounded": bool, "unbounded": [names]}`, or None when a
    query was not decided -- then nothing is said."""
    nums = [x for x in input_vars if x.sort() in (z3.IntSort(), z3.RealSort())]
    if not nums:
        return {"bounded": True, "unbounded": []}

    def big(xs):
        s = z3.Solver()
        lim.apply_to(s)
        s.set("timeout", max(1, min(1000, _remaining_ms(deadline))))
        s.add(behav, *fixed, z3.Or(*[z3.Or(x > BIG, x < -BIG) for x in xs]))
        return s.check()

    r = big(nums)
    if r == z3.unsat:
        return {"bounded": True, "unbounded": []}
    if r != z3.sat or len(nums) > 64:
        return None
    out = []
    for x in nums:
        r = big([x])
        if r == z3.unknown:
            return None
        if r == z3.sat:
            out.append(str(x))
    return {"bounded": not out, "unbounded": out}


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
    # ...asked WITHOUT the quantifier when the helpers are only in the
    # correctness (`_ce_search`); the quantified query stays as the fallback.
    by_witness = bool(helper_vars) and not _helpers_in(behav, helper_vars)
    pool = []               # helper values that saved some input
    work = {"rlimit": 0}
    ms = {"candidate": 0.0, "counterexample": 0.0, "helpers": 0.0,
          "quantified": 0.0, "decisive": 0.0, "which_fail": 0.0,
          "domain_verifier": 0.0}
    fallbacks = 0
    impl_assign = None

    counterexamples = []
    ce_points = []          # the same, as (z3 var, value) pairs
    trace = []
    domain_log = []         # every call of the external verifier
    rejected = []           # the candidates it rejected, kept as exclusions
    by_name = {str(v): v for v in input_vars}
    spec_smt2 = {
        "impl_constraints": z3util.smt2(impl_cons),
        "behavior": z3util.smt2(behav),
        "correctness": z3util.smt2(corr),
    }

    domain = str(z3.simplify(behav)).replace("\n", " ")
    if len(domain) > 200:
        domain = domain[:197] + "..."

    scope = spec.scope_data() if hasattr(spec, "scope_data") else None

    built = time.perf_counter()

    def done(status, verdict, detail, cert=None, k=0, impl=None, stalled=None):
        work["rlimit"] += _rlimit(impl_solver) + _rlimit(ce_solver)
        meta = {"iterations": k, "counterexamples": len(counterexamples),
                "domain": domain, "trace": trace,
                # construction: the contract normalised and the solvers set
                # up; search: the rounds, the certificate written with them --
                # and inside it, where the time went, by step
                "phases_ms": {"construction": round((built - t0) * 1000, 2),
                              "search": round((time.perf_counter() - built) * 1000, 2),
                              **{"search." + n: round(v, 2) for n, v in ms.items() if v}},
                "work": {"rlimit": work["rlimit"]}}
        if helper_vars:
            meta["helper_search"] = {"witnesses": len(pool),
                                     "quantifier_free": by_witness,
                                     "fallbacks": fallbacks}
        if stalled is not None:
            # WHERE it stopped, not only that it did: the step, the round,
            # the sizes, and the last candidate it was examining.
            phase, reason = stalled
            meta["stalled"] = {"phase": phase, "reason": reason or "unknown",
                               "round": k + 1,
                               "counterexamples": len(counterexamples),
                               "witnesses": len(pool),
                               "inputs": len(input_vars),
                               "helpers": len(helper_vars),
                               "rlimit": work["rlimit"]}
            if impl_assign is not None:
                meta["stalled"]["candidate"] = {n: v for n, (_, v)
                                                in impl_assign.items()}
        if domain_log:
            meta["domain_verifier"] = {
                "calls": len(domain_log),
                "rejected": sum(1 for r in domain_log if r.get("valid") is False),
                "log": domain_log}
            if cert is not None and cert.kind == "cegis_none":
                cert.payload["domain_rejected"] = rejected
            if cert is not None and cert.kind == "cegis":
                cert.payload["domain_check"] = domain_log[-1]
                detail = detail.rstrip(". ") + ". " + t(
                    "engine.synth.domain_accepted",
                    rejected=meta["domain_verifier"]["rejected"],
                    version=domain_log[-1].get("version") or "-")
        original = getattr(spec, "original", None)
        if original is not None and ce_points:
            inside = [_in_original(original, pt) for pt in ce_points]
            meta["counterexamples_in_original"] = {
                "inside": sum(1 for v in inside if v is True),
                "outside": sum(1 for v in inside if v is False),
                "undecided": sum(1 for v in inside if v is None),
                "each": inside}
            out_ = meta["counterexamples_in_original"]["outside"]
            if out_:
                detail = detail.rstrip(". ") + ". " + t(
                    "engine.synth.outside_original", n=out_, total=len(inside))
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
            if getattr(spec, "templates", None):
                # the FUNCTIONS found, written out
                meta["functions"] = {tp.name: tp.instantiate(impl)
                                     for tp in spec.templates}
        return Result(
            "synth", status, verdict, ENGINE,
            (time.perf_counter() - t0) * 1000, cert, detail, meta=meta,
        )

    for k in range(lim.max_iterations):
        if time.perf_counter() >= deadline:
            return done(Status.TIMEOUT, Verdict.INCONCLUSIVE,
                        t("engine.synth.timeout", rounds=k), k=k,
                        stalled=("clock", "timeout"))


        # --- 1. proponer una implementacion compatible con lo visto -------
        impl_solver.set("timeout", _remaining_ms(deadline))
        t1 = time.perf_counter()
        r = impl_solver.check()
        ms["candidate"] += (time.perf_counter() - t1) * 1000
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
            # THE DECISIVE ONES: a minimal subset of the counterexamples that
            # still leaves no candidate -- "these three inputs force it", the
            # sentence a write-up wants. Checked again by `verify`. Not when
            # the domain verifier excluded candidates: those exclusions are
            # part of the refutation, and the subset alone would not be one.
            t1 = time.perf_counter()
            decisive = None if rejected else _decisive(
                impl_cons, behav, corr, input_vars, helper_vars,
                counterexamples, lim)
            ms["decisive"] += (time.perf_counter() - t1) * 1000
            detail = t("engine.synth.none", ces=len(counterexamples))
            if rejected:
                detail = detail.rstrip(". ") + ". " + t(
                    "engine.synth.domain_rejected", n=len(rejected))
            if decisive is not None:
                cert.payload["decisive"] = decisive
                detail = detail.rstrip(". ") + ". " + t(
                    "engine.synth.decisive", k=len(decisive), n=len(counterexamples))
            res = done(Status.UNSAT, Verdict.UNSATISFIABLE, detail, cert, k=k)
            if decisive is not None:
                res.meta["decisive"] = [counterexamples[i] for i in decisive]
            return res
        if r != z3.sat:
            st = classify_unknown(impl_solver.reason_unknown())
            return done(st, Verdict.INCONCLUSIVE,
                        t("engine.synth.impl_unknown",
                          reason=impl_solver.reason_unknown()), k=k,
                        stalled=("candidate", impl_solver.reason_unknown()))

        model = impl_solver.model()
        impl_assign = z3util.assignment(model, impl_vars)
        fixed = [v == model.eval(v, model_completion=True) for v in impl_vars]

        # --- 2. buscar un contraejemplo para ESA implementacion -----------
        ce_solver.push()
        try:
            ce_solver.add(*fixed)
            how, got, ce_model = "quantified", None, None
            if by_witness:
                how, got = _ce_search(behav, corr, fixed, input_vars, helper_vars,
                                      pool, lim, deadline, work, ms)
            if how == "none":
                r2 = z3.unsat
            elif how == "ce":
                r2, ce_model = z3.sat, got
            elif how == "unknown":
                phase, why_ = got
                st = classify_unknown(why_)
                return done(st, Verdict.INCONCLUSIVE,
                            t("engine.synth.ce_unknown", reason=why_), k=k,
                            stalled=(phase, why_))
            else:
                # no helper search, or it did not close in WITNESS_ROUNDS:
                # the quantified query, as before
                fallbacks += how == "fallback"
                ce_solver.set("timeout", _remaining_ms(deadline))
                t1 = time.perf_counter()
                r2 = ce_solver.check()
                ms["quantified" if helper_vars else "counterexample"] += \
                    (time.perf_counter() - t1) * 1000
                if r2 == z3.sat:
                    ce_model = ce_solver.model()

            if r2 == z3.unsat and getattr(spec, "domain_verifier", None) is not None:
                # THE MODEL ACCEPTS IT; NOW THE REAL PROBLEM. A candidate the
                # domain verifier rejects is excluded, and the search goes on.
                t1 = time.perf_counter()
                valid, dce, record = _domain_check(spec, impl_assign)
                ms["domain_verifier"] += (time.perf_counter() - t1) * 1000
                record["round"] = k + 1
                domain_log.append(record)
                if valid is None:
                    return done(Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                                t("engine.synth.domain_error",
                                  error=record.get("error", "")), k=k,
                                stalled=("domain_verifier", record.get("error", "")))
                if not valid:
                    rejected.append(dict(record, implementation=impl_assign))
                    trace.append({"round": k + 1, "implementation": impl_assign,
                                  "counterexample": record.get("counterexample"),
                                  "source": "domain",
                                  "input_sha256": record["input_sha256"],
                                  "result_sha256": record["result_sha256"],
                                  "version": record["version"]})
                    if on_round is not None:
                        on_round(trace[-1])
                    impl_solver.add(z3.Not(z3.And(*fixed)) if len(fixed) > 1
                                    else z3.Not(fixed[0]))
                    pts = [(by_name[n], _as_z3(by_name[n], v))
                           for n, v in (dce or {}).items() if n in by_name]
                    if pts and len(pts) == len(input_vars):
                        subs = list(pts) + [
                            (h, z3.Const("{}__dom{}".format(h, k), h.sort()))
                            for h in helper_vars]
                        impl_solver.add(z3.substitute(z3.Implies(behav, corr), *subs))
                    continue
            if r2 == z3.unsat:
                if on_round is not None:
                    # The ACCEPTED round is a round too: a caller counting
                    # callbacks saw one fewer than `iterations` and no sign
                    # of the candidate that survived.
                    on_round({"round": k + 1, "implementation": impl_assign,
                              "counterexample": None, "accepted": True})
                witnesses = None
                exact = all(z3.is_int_value(v) or z3.is_rational_value(v)
                            or z3.is_true(v) or z3.is_false(v)
                            for w in pool for _h, v in w)
                # an algebraic helper value (a root of 2) has no exact text:
                # then no strategy is written, and `verify` quantifies
                if how == "none" and helper_vars and exact:
                    # THE STRATEGY, written down: these helper values save
                    # every input of the domain -- checked by `verify` with
                    # one quantifier-free query instead of the quantified one
                    witnesses = [{str(h): [z3util.sort_name(h), z3util.value_repr(v)]
                                  for h, v in w} for w in pool[-WITNESS_POOL:]]
                cert = cegis_certificate(impl_assign, counterexamples, spec_smt2, k + 1,
                                         helpers=[[str(h), z3util.sort_name(h)]
                                                  for h in helper_vars],
                                         helper_witnesses=witnesses)
                # NOTHING TO SATISFY: a candidate whose domain is empty passes
                # every contract. Said in the headline, as `prove` does.
                vs = z3.Solver()
                lim.apply_to(vs)
                vs.set("timeout", max(1, min(1000, _remaining_ms(deadline))))
                vs.add(behav, *fixed)
                vacuous = vs.check() == z3.unsat
                inputs_dom = _input_domain(behav, fixed, input_vars, lim, deadline)
                if vacuous:
                    cert.payload["vacuous"] = True
                    detail = t("engine.synth.vacuous", rounds=k + 1)
                elif inputs_dom is not None and not inputs_dom["bounded"]:
                    detail = t("engine.synth.found_unbounded", rounds=k + 1,
                               ces=len(counterexamples),
                               names=", ".join(inputs_dom["unbounded"]))
                else:
                    detail = t("engine.synth.found", rounds=k + 1,
                               ces=len(counterexamples))
                res = done(Status.SAT, Verdict.PROVED, detail,
                           cert, k + 1, impl=impl_assign)
                res.meta["vacuous"] = vacuous
                if inputs_dom is not None:
                    res.meta["input_domain"] = inputs_dom
                return res
            if r2 != z3.sat:
                st = classify_unknown(ce_solver.reason_unknown())
                return done(st, Verdict.INCONCLUSIVE,
                            t("engine.synth.ce_unknown",
                              reason=ce_solver.reason_unknown()), k=k,
                            stalled=("quantified" if helper_vars else "counterexample",
                                     ce_solver.reason_unknown()))

            ce_assign = z3util.assignment(ce_model, input_vars)
            ce_concrete = [
                (x, ce_model.eval(x, model_completion=True)) for x in input_vars
            ]
            t1 = time.perf_counter()
            breaks = _which_fail(spec, behav, fixed, ce_concrete, helper_vars, lim)
            ms["which_fail"] += (time.perf_counter() - t1) * 1000
        finally:
            ce_solver.pop()  # (d) del original: el pop faltaba en dos ramas

        counterexamples.append(ce_assign)
        ce_points.append(ce_concrete)
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
                k=lim.max_iterations, stalled=("rounds", "max_iterations"))


def _instance(behav, corr, input_vars, helper_vars, ce, i):
    """The contract at counterexample `ce` (index `i` names its helpers)."""
    from ..certificate import _const, _value

    subs = [(_const(z3, n, s), _value(z3, s, v)) for n, (s, v) in ce.items()]
    subs += [(h, z3.Const("{}__ce{}".format(h, i), h.sort())) for h in helper_vars]
    f = z3.Implies(behav, corr)
    return z3.substitute(f, *subs) if subs else f


def _decisive(impl_cons, behav, corr, input_vars, helper_vars, counterexamples, lim):
    """Indices of a MINIMAL subset of the counterexamples that, with the
    implementation's constraints, is still unsatisfiable -- deletion-based,
    one solver call per counterexample. None when a check is not decided."""
    inst = [_instance(behav, corr, input_vars, helper_vars, ce, i)
            for i, ce in enumerate(counterexamples)]

    def unsat(keep):
        s = z3.Solver()
        lim.apply_to(s)
        s.add(impl_cons, *[inst[i] for i in keep])
        r = s.check()
        return None if r == z3.unknown else r == z3.unsat

    keep = list(range(len(inst)))
    if unsat(keep) is not True:
        return None
    for i in list(keep):
        trial = [j for j in keep if j != i]
        got = unsat(trial)
        if got is None:
            return None
        if got:
            keep = trial
    return keep


def _which_fail(spec, behav, fixed, ce_concrete, helper_vars, lim):
    """The named obligations this counterexample breaks, for a `correctness`
    given as a dict: obligation i is broken when no helper saves IT at this
    input. None when the correctness is one formula."""
    names = spec.obligation_names() if hasattr(spec, "obligation_names") else None
    if not names:
        return None
    out = []
    quantified = bool(helper_vars) and _helpers_in(behav, helper_vars)
    for name in names:
        s = z3.Solver()
        lim.apply_to(s)
        s.add(*fixed)
        s.add(*[x == v for x, v in ce_concrete])
        s.add(behav)
        if quantified:
            s.add(_no_helper_saves(behav, spec.correctness[name], helper_vars))
            if s.check() == z3.sat:
                out.append(name)
            continue
        # The input is concrete: "no helper saves obligation i" is "the
        # obligation is unsatisfiable over the helpers" -- no quantifier.
        s.add(spec.correctness[name])
        if s.check() == z3.unsat:
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
    best, rounds, path, searches = None, 0, [], []
    all_trace, all_ces = [], 0
    where = {"inside": 0, "outside": 0, "undecided": 0}   # over every search
    current = plain
    for _ in range(max(1, lim.max_iterations)):
        res = synth(current, lim, on_round)
        rounds += res.meta.get("iterations", 0)
        all_ces += res.meta.get("counterexamples", 0)
        for row in res.meta.get("trace") or []:
            all_trace.append(dict(row, search=len(searches) + 1))
        searches.append({"iterations": res.meta.get("iterations", 0),
                         "counterexamples": res.meta.get("counterexamples", 0),
                         "verdict": res.verdict.value})
        for key in where:
            where[key] += (res.meta.get("counterexamples_in_original") or {}).get(key, 0)
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
            # ONE SCALE AT THE TOP. `iterations`, `counterexamples` and
            # `trace` are every search together (each trace row says which
            # search, 1-based); the search that found the optimum keeps its
            # own under `last_candidate`. 0.34-0.39 put that one at the top,
            # and three sessions summarising jobs read `iterations: 1,
            # counterexamples: 0` off a run of eight searches.
            meta["last_candidate"] = {
                "iterations": found.meta.get("iterations", 0),
                "counterexamples": found.meta.get("counterexamples", 0),
                "trace": found.meta.get("trace") or []}
            meta.update(iterations=rounds, counterexamples=all_ces, trace=all_trace)
            meta["optimization"] = {
                "total_rounds": rounds, "improvements": len(path), "path": path,
                "searches": searches,
                "better_value_refutation": {
                    "iterations": res.meta.get("iterations", 0),
                    "counterexamples": res.meta.get("counterexamples", 0),
                    # WHAT blocks a better value: the inputs that refute every
                    # candidate past the optimum, and the decisive few
                    "inputs": [row.get("counterexample") for row
                               in res.meta.get("trace") or []
                               if row.get("counterexample") is not None],
                    "decisive": res.meta.get("decisive")}}
            detail = t("engine.synth.optimum", sense=sense, value=value,
                       steps=len(path), rounds=rounds)
            if getattr(spec, "original", None) is not None:
                meta["counterexamples_in_original"] = dict(where)
                if where["outside"]:
                    detail += " " + t("engine.synth.outside_original", n=where["outside"],
                                      total=sum(where.values()))
            return Result("synth", Status.SAT, Verdict.PROVED, ENGINE, ms, cert,
                          detail, meta=meta)
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
