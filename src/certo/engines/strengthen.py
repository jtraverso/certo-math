"""CEGIS for induction: the strengthening that makes P(k) inductive.

A true P(k) is often not inductive: from P(k) alone, P(k + 1) does not
follow, because the step's hypothesis admits states no run reaches. The
classical repair is to prove something STRONGER -- P(k) and Q(k) -- whose
step goes through. Finding Q is search; checking it is the ordinary `induct`.

Here the search is CEGIS over a template's integer coefficients, Q_c(k):

  1. propose c within the bounds, consistent with every point learnt so far;
  2. check P and Q_c on each base case k0..base_upto, then the step
     (k >= step_from, facts(k), facts(k + 1), P(k), Q_c(k)) -> P(k+1), Q_c(k+1);
  3. a failure is a MODEL -- an index and values of the sequence there. The
     obligation is grounded at it (every symbol but c replaced by its value,
     every application of the sequence by the value the model gives it) and
     the coefficients are asked to satisfy that instance from now on.

A grounded instance is a consequence of the obligation, so no valid c is ever
excluded: "none in the template" is a statement about the template, never
about P, and the result says `template_too_small`. A found Q is not trusted
either: P(k) and Q(k) go through `induct` -- base cases, step, links, every
sub-certificate -- and the certificate records the strengthening, with
`verify` checking that what was proved implies P(k).
"""
from __future__ import annotations

import time

import z3

from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict, classify_unknown
from ..why import Phases

ENGINE = "certo/strengthen+z3:" + z3.get_version_string()


def _is_value(x) -> bool:
    return (z3.is_int_value(x) or z3.is_rational_value(x) or z3.is_true(x)
            or z3.is_false(x) or z3.is_algebraic_value(x))


def _ground(expr, model, keep):
    """`expr` with every free symbol not in `keep` replaced by its value in
    `model`, and every application of an uninterpreted function to values
    replaced by the value the model gives it."""
    memo = {}

    def g(e):
        key = e.get_id()
        if key in memo:
            return memo[key]
        if z3.is_quantifier(e) or z3.is_var(e):
            out = e
        elif z3.is_const(e):
            if e.decl().kind() == z3.Z3_OP_UNINTERPRETED and str(e) not in keep:
                out = model.eval(e, model_completion=True)
            else:
                out = e
        elif z3.is_app(e):
            args = [g(a) for a in e.children()]
            if e.decl().kind() == z3.Z3_OP_UNINTERPRETED and args:
                simple = [z3.simplify(a) for a in args]
                if all(_is_value(a) for a in simple):
                    out = model.eval(e.decl()(*simple), model_completion=True)
                else:
                    out = e.decl()(*args)
            else:
                out = e.decl()(*args) if args else e
        else:
            out = e
        memo[key] = out
        return out

    return g(expr)


def _fail(detail, t0, status=Status.UNKNOWN_SOLVER, meta=None):
    return Result("induct", status, Verdict.INCONCLUSIVE, ENGINE,
                  (time.perf_counter() - t0) * 1000, None, detail=detail,
                  meta=meta or {})


def strengthen(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    from ..spec import InductSpec, Spec
    from . import induct as _induct

    lim = limits or Limits()
    t0 = time.perf_counter()
    ph = Phases()
    k = spec.k
    k0 = int(spec.k0)
    upto = k0 if spec.base_upto is None else int(spec.base_upto)
    step_from = k0 if spec.step_from is None else int(spec.step_from)
    if step_from > upto:
        return _fail(t("engine.induct.gap", step=step_from, upto=upto), t0,
                     Status.OUT_OF_THEORY)
    n = int(spec.coefficients)
    lo, hi = spec.bounds
    with ph("construction"):
        cs = [z3.Int("q__{}".format(i)) for i in range(n)]
        keep = {str(c) for c in cs}
        facts = (lambda kk: list(spec.facts(kk))) if spec.facts else (lambda kk: [])
        initial = list(spec.initial or [])
        P = spec.prop
        Q = (lambda kk: spec.template(cs, kk))
        obligations = []
        for kb in range(k0, upto + 1):
            prem = initial + [f for j in range(k0, kb + 1) for f in facts(z3.IntVal(j))]
            obligations.append(("base {}".format(kb), z3.Implies(
                z3.And(*prem) if prem else z3.BoolVal(True),
                z3.And(P(z3.IntVal(kb)), Q(z3.IntVal(kb))))))
        obligations.append(("step", z3.Implies(
            z3.And(k >= step_from, *facts(k), *facts(k + 1), P(k), Q(k)),
            z3.And(P(k + 1), Q(k + 1)))))
        proposer = z3.Solver()
        lim.apply_to(proposer)
        proposer.add(*[z3.And(c >= lo, c <= hi) for c in cs])

    deadline = t0 + lim.timeout_ms / 1000.0
    trace, rounds, found = [], 0, None
    with ph("search"):
        for rounds in range(1, lim.max_iterations + 1):
            if time.perf_counter() >= deadline:
                return ph.into(_fail(t("engine.strengthen.timeout", rounds=rounds - 1),
                                     t0, Status.TIMEOUT, {"trace": trace}))
            r = proposer.check()
            if r == z3.unsat:
                return ph.into(_fail(
                    t("engine.strengthen.none", rounds=rounds - 1, lo=lo, hi=hi),
                    t0, Status.UNKNOWN_SOLVER,
                    {"trace": trace, "why": "template_too_small",
                     "counterexamples": len(trace)}))
            if r != z3.sat:
                return ph.into(_fail(
                    t("engine.synth.impl_unknown", reason=proposer.reason_unknown()),
                    t0, classify_unknown(proposer.reason_unknown()),
                    {"trace": trace}))
            m = proposer.model()
            cand = [m.eval(c, model_completion=True) for c in cs]
            failing = None
            for name, ob in obligations:
                s = z3.Solver()
                lim.apply_to(s)
                s.add(*[c == v for c, v in zip(cs, cand)], z3.Not(ob))
                got = s.check()
                if got == z3.unsat:
                    continue
                if got != z3.sat:
                    return ph.into(_fail(
                        t("engine.strengthen.unknown", where=name,
                          reason=s.reason_unknown()),
                        t0, classify_unknown(s.reason_unknown()), {"trace": trace}))
                failing = (name, _ground(ob, s.model(), keep), s.model())
                break
            if failing is None:
                found = cand
                break
            name, inst, cm = failing
            trace.append({"round": rounds, "candidate": [str(v) for v in cand],
                          "fails": name,
                          "at": str(cm.eval(k, model_completion=True))
                          if name == "step" else name.split()[-1]})
            proposer.add(inst)
        else:
            return ph.into(_fail(t("engine.synth.max_iter", n=lim.max_iterations),
                                 t0, Status.RESOURCE_EXHAUSTED, {"trace": trace}))

    # FOUND: now the induction itself, through `induct`.
    with ph("extraction"):
        qstar = (lambda kk: spec.template(found, kk))
        pp = (lambda kk: z3.And(P(kk), qstar(kk)))

        def base(kb):
            s = Spec(title="P'({})".format(kb))
            for i, f in enumerate(initial):
                s.assume("initial_{}".format(i), f)
            for j in range(k0, kb + 1):
                for i, f in enumerate(facts(z3.IntVal(j))):
                    s.assume("facts_{}_{}".format(j, i), f)
            s.claim(pp(z3.IntVal(kb)))
            return s

        step = Spec(title="P'(k) -> P'(k+1)")
        step.assume("k_from", k >= step_from)
        for i, f in enumerate(facts(k)):
            step.assume("facts_k_{}".format(i), f)
        for i, f in enumerate(facts(k + 1)):
            step.assume("facts_k1_{}".format(i), f)
        step.assume("P_k", pp(k))
        step.claim(pp(k + 1))
        q_text = str(z3.simplify(qstar(k)))
        ind = InductSpec(
            k0=k0, base_upto=upto, base=base, step=step, step_from=step_from,
            k=k, facts=spec.facts, initial=initial,
            describe=spec.describe or t("engine.strengthen.conclusion",
                                        p=str(P(k)), q=q_text, k0=k0),
            title=spec.title)
        res = _induct.induct(ind, lim, spec_path)
        res.engine = ENGINE
        meta = {"strengthening": q_text, "coefficients": [str(v) for v in found],
                "rounds": rounds, "trace": trace}
        res.meta.update(meta)
        if res.certificate is not None:
            from .. import z3util

            res.certificate.payload["strengthened"] = {
                "prop_smt2": z3util.smt2(P(k)), "q": q_text,
                "coefficients": [str(v) for v in found], "rounds": rounds}
            res.detail = (res.detail or "").rstrip(". ") + ". " + t(
                "engine.strengthen.found", q=q_text, rounds=rounds)
        else:
            res.detail = t("engine.strengthen.found_unproved", q=q_text,
                           detail=res.detail)
    return ph.into(res)
