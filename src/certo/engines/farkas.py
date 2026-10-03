"""The `farkas` command: linarith and nlinarith, with an exact certificate.

`prove` tells you whether something is true; this tells you WHY in a form a
referee can check by hand and Lean can consume. The whole content of the
certificate is a list of non-negative rationals.
"""
from __future__ import annotations

import time
from fractions import Fraction

from .. import exact, linarith
from ..certificate import farkas_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict


def _search(rows, limits):
    """The LP behind linarith: lambda >= 0 that cancels every monomial.

    Two closing conditions, and they are not interchangeable. With a strict
    row carrying weight, the constant only has to be >= 0 (the contradiction
    is `0 < 0`). With no strict row it has to be strictly positive, and 1 is
    as good as any because the system is scale-free.
    """
    from ..engines import lp
    from ..spec import LPSpec

    monomials = sorted({m for _, p, _ in rows for m in p if m != linarith.CONST})
    strict = [i for i, (_, _, rel) in enumerate(rows) if rel == "<"]

    def build(with_strict):
        s = LPSpec(sense="max", title="farkas")
        for i, _ in enumerate(rows):
            s.variable("L{}".format(i))
        s.objective({"L{}".format(i): 0 for i in range(len(rows))})
        for m in monomials:
            s.constraint({"L{}".format(i): p.get(m, 0)
                          for i, (_, p, _) in enumerate(rows)}, "==", 0,
                         name="cancel_" + ("_".join(m)))
        consts = {"L{}".format(i): p.get(linarith.CONST, 0)
                  for i, (_, p, _) in enumerate(rows)}
        if with_strict:
            s.constraint(consts, ">=", 0, name="const_nonneg")
            s.constraint({"L{}".format(i): 1 for i in strict}, ">=", 1,
                         name="strict_active")
        else:
            s.constraint(consts, ">=", 1, name="const_positive")
        return s

    for with_strict in ([True, False] if strict else [False]):
        res = lp.opt(build(with_strict), limits)
        if res.verdict is not Verdict.SATISFIABLE:
            continue
        sol = res.meta.get("solution") or {}
        lams = [Fraction(str(sol.get("L{}".format(i), 0)))
                for i in range(len(rows))]
        ok, const, strict_used = linarith.is_contradiction(rows, lams)
        if ok:
            return lams, const, strict_used, res.meta.get("exact", False)
    return None, None, None, False


def as_hypotheses(spec):
    """A linear program read as named hypotheses with NO goal.

    Its bounds and constraints, each a row named after itself, every variable
    over the reals: a contradiction among the real rows is one among the
    integer points too, so an integer program is decided by its relaxation
    when that is infeasible, and is not claimed feasible when it is not.
    """
    import z3

    from ..exact import to_fraction
    from ..spec import Spec

    def num(v):
        q = to_fraction(v)
        return z3.Q(q.numerator, q.denominator)

    xs = {v: z3.Real(v) for v in spec.var_names}
    out = Spec(title=spec.title)
    for v in spec.var_names:
        lo, hi = spec.bounds[v]
        if lo is not None:
            out.assume(v + "_lo", xs[v] >= num(lo))
        if hi is not None:
            out.assume(v + "_hi", xs[v] <= num(hi))
    for name, coeffs, sense, rhs in spec.cons:
        lhs = (z3.Sum([num(c) * xs[v] for v, c in coeffs.items()]) if coeffs
               else z3.RealVal(0))
        out.assume(name, {"<=": lhs <= num(rhs), ">=": lhs >= num(rhs),
                          "==": lhs == num(rhs)}[sense])
    out.claim(False)
    # Which variables are integers: not a row (a Farkas row is linear), but
    # the point offered when there is no combination has to respect them.
    out.integral = [v for v in spec.var_names
                    if spec.kind_of(v) in ("integer", "binary")]
    return out


def _infeasibility(spec) -> bool:
    """Is the question "are the hypotheses contradictory?" -- a claim of
    False, or none at all -- rather than "do they imply the goal?"."""
    import z3

    g = spec.goal
    return g is None or g is False or (z3.is_expr(g) and z3.is_false(g))


def _feasible_point(spec, infeasibility, limits):
    """A point satisfying the hypotheses (and the negated goal), as a `model`
    certificate, or None. When no Farkas combination exists a linear system
    IS feasible over the reals -- that is Farkas' lemma -- and saying so with
    the point is an answer where `unknown_solver` was none."""
    import z3

    from .. import z3util
    from ..certificate import model_certificate

    exprs = [f for _, f in spec.assumptions]
    if not infeasibility:
        exprs.append(z3.Not(spec.goal))
    exprs += [z3.IsInt(z3.Real(v)) for v in getattr(spec, "integral", ())]
    if not exprs:
        return None
    s = z3.Solver()
    s.set("timeout", int(limits.timeout_ms))
    s.add(*exprs)
    if s.check() != z3.sat:
        return None
    consts = z3util.free_consts(*exprs)
    return model_certificate(z3util.smt2(*exprs),
                             z3util.assignment(s.model(), consts))


def farkas(spec, limits: Limits | None = None, nonlinear: bool = False,
           spec_path: str = "") -> Result:
    lim = limits or Limits()
    t0 = time.perf_counter()

    from ..spec import LPSpec, Spec

    if type(spec).__name__ == "PackingSpec":
        spec = spec.to_lp()
    if isinstance(spec, LPSpec):
        spec = as_hypotheses(spec)
    integral = getattr(spec, "integral", [])
    infeasibility = _infeasibility(spec)
    if infeasibility and spec.goal is not None:
        # The goal row of `False` would be `0 <= 0`: true, and no help. The
        # question is the hypotheses alone.
        spec = Spec(assumptions=list(spec.assumptions), goal=None,
                    title=spec.title)
        spec.integral = integral

    try:
        rows = linarith.rows_of(spec)
    except linarith.NotPolynomial as e:
        return Result("farkas", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      "certo/farkas", (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.farkas.not_polynomial", detail=str(e)))

    base, origin = len(rows), {}
    if nonlinear:
        extra, origin = linarith.products(rows)
        rows = rows + extra

    degree = max((len(m) for _, p, _ in rows for m in p), default=0)
    if degree > 1 and not nonlinear:
        return Result("farkas", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      "certo/farkas", (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.farkas.nonlinear_needed"))

    lams, const, strict, is_exact = _search(rows, lim)
    ms = (time.perf_counter() - t0) * 1000

    if lams is None:
        point = _feasible_point(spec, infeasibility, lim)
        if point is not None:
            return Result(
                "farkas", Status.SAT, Verdict.REFUTED, "certo/farkas",
                (time.perf_counter() - t0) * 1000, point,
                detail=t("engine.farkas.feasible" if infeasibility
                         else "engine.farkas.counterexample"),
                meta={"rows": len(rows), "degree": degree,
                      "point": {k: v[1] for k, v
                                in point.payload["assignment"].items()}})
        return Result("farkas", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      "certo/farkas", ms, None,
                      detail=t("engine.farkas.none",
                               mode=t("engine.farkas.nonlinear" if nonlinear
                                      else "engine.farkas.linear")),
                      meta={"rows": len(rows), "degree": degree})
    if not is_exact:
        return Result("farkas", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      "certo/farkas", ms, None,
                      detail=t("engine.farkas.inexact"))

    used = [(rows[i][0], exact.serialize(l)) for i, l in enumerate(lams) if l]
    # With no goal there is nothing for the hypotheses to be vacuous ABOUT:
    # their contradiction is the answer that was asked for.
    vacuous = False if infeasibility else _vacuous(rows, lim)
    cert = farkas_certificate(
        rows=linarith.serialize_rows(rows),
        multipliers=[exact.serialize(l) for l in lams],
        constant=exact.serialize(const), strict=strict,
        nonlinear=nonlinear, base_rows=base, sorts=_sorts(spec),
        vacuous=vacuous, derived=origin, spec_path=str(spec_path))

    return Result(
        "farkas", Status.UNSAT, Verdict.PROVED, "certo/farkas", ms, cert,
        detail=(t("engine.farkas.infeasible", n=len(used)) if infeasibility
                else t("engine.farkas.vacuous") if vacuous else
                t("engine.farkas.found", n=len(used),
                  mode=t("engine.farkas.nonlinear" if nonlinear
                         else "engine.farkas.linear"))),
        meta={"multipliers": dict(used), "rows": len(rows), "degree": degree,
              "vacuous": vacuous, "infeasible": infeasibility,
              "constant": exact.serialize(const), "strict": strict,
              "hint": _lean_hint(spec, used, nonlinear)},
    )


def _vacuous(rows, limits) -> bool:
    """Do the hypotheses close the system WITHOUT the negated goal?

    Reading it off the multipliers does not work: the LP is free to give the
    goal row a non-zero weight even when it is not needed, and often does. So
    the question has to be asked directly -- drop the goal row and search
    again. One extra LP, only on the successful path.
    """
    # Every row DERIVED from the goal has to go too, not just the goal row:
    # in nonlinear mode the products are named "h*__goal__" and keeping one
    # would smuggle the goal back in and report vacuity that is not there.
    rest = [r for r in rows if "__goal__" not in r[0]]
    if not rest:
        return False
    lams, _, _, exact_ok = _search(rest, limits)
    return lams is not None and exact_ok


def _sorts(spec) -> dict:
    """Which variables are integers. A row rebuilt in the wrong sort is a
    different variable, so `compose` needs this to re-read the rows."""
    from .. import z3util

    exprs = [f for _, f in spec.assumptions]
    if spec.goal is not None:
        exprs.append(spec.goal)
    out = {}
    for c in z3util.free_consts(*exprs):
        try:
            out[str(c)] = z3util.sort_name(c)
        except ValueError:
            pass
    return out


def _lean_hint(spec, used, nonlinear) -> str:
    """The Lean one-liner this certificate corresponds to.

    The multipliers are not needed there -- `linarith` will rediscover them --
    but which hypotheses to hand it is exactly what this found out.
    """
    names = [n for n, _ in used if not n.startswith(("__goal__", "sq_"))
             and "*" not in n and "^" not in n]
    names = [n[:-4] if n.endswith("_rev") else n for n in names]
    seen, ordered = set(), []
    for n in names:
        if n not in seen:
            seen.add(n)
            ordered.append(n)
    tactic = "nlinarith" if nonlinear else "linarith"
    return "{} [{}]".format(tactic, ", ".join(ordered)) if ordered else tactic
