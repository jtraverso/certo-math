"""`mixed`: a discrete skeleton found by search, certified by an exact LP.

The workflow this exists for is one a user wrote down better than I would
have: a MILP chooses a discrete structure and a compatible fractional packing
at the same time, and what the proof needs is not that the choice was optimal
but that the construction it found REACHES A TARGET. An existence proof does
not care whether a better design exists.

So the flow is deliberately not "certify the MILP":

    search (CBC, heuristic)  ->  freeze the discrete part
                             ->  residual LP over the continuous part
                             ->  exact dual, exact everything
                             ->  compare against the target

and what is certified is exactly that, stated in those words. `LPSpec(integer=
True)` could not express it at all, because it makes EVERY variable integer;
a design whose discrete part chooses a structure and whose continuous part
packs inside it needs both kinds at once.

Three numbers come out, and keeping them apart is the point:

  achieved       what the construction attains -- exact, and a genuine LOWER
                 bound on the true optimum, because the construction exists;
  conditional    the best the continuous part can do WITH THIS SKELETON, from
                 the residual LP's exact dual;
  bound          the LP relaxation over all skeletons, an UPPER bound on the
                 true optimum.

If `achieved` meets `bound` the MILP optimum is pinned exactly and that is
said. Otherwise global optimality is not claimed, and the gap is printed
rather than left to be inferred from silence. The extra relaxation solve costs
one LP and buys a real answer often enough to be worth doing unasked.
"""
from __future__ import annotations

import time
from fractions import Fraction

from .. import exact
from ..certificate import mixed_design_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "certo/mixed+CBC"

# Three levels, and the distance between them is the point. A user asked for
# exactly this taxonomy, in these words, which is the strongest argument for
# it: the names are what a reader needs, and "declare exactly what was proved"
# is the whole discipline here.
FEASIBLE = "feasible"                    # a mixed point satisfies everything
CONDITIONAL = "conditional_optimum"      # and the residual LP is optimal
GLOBAL = "global_optimum"                # and it meets the relaxation bound


def _round_assignment(spec, solution):
    """The discrete variables, rounded -- and only rounded.

    CBC returns 0.9999997 for a binary as often as not. Rounding is a guess
    until something checks it, and the checking happens next, against the
    original constraints in exact arithmetic. A design nobody checked is a
    design nobody can cite.
    """
    out = {}
    for v in spec.discrete:
        raw = solution.get(v, 0)
        val = Fraction(round(float(exact.to_fraction(raw))))
        lo, hi = spec.bounds[v]
        if val < Fraction(lo or 0):
            return None, v
        if hi is not None and val > Fraction(hi):
            return None, v
        out[v] = val
    return out, None


def _violations(spec, values):
    """Every original constraint, checked exactly at the full point."""
    bad = []
    for name, coeffs, sense, rhs in spec.cons:
        lhs = sum((exact.to_fraction(c) * values.get(v, Fraction(0))
                   for v, c in coeffs.items()), Fraction(0))
        rhs = exact.to_fraction(rhs)
        ok = (lhs <= rhs if sense == "<=" else
              lhs >= rhs if sense == ">=" else lhs == rhs)
        if not ok:
            bad.append({"name": name, "lhs": exact.serialize(lhs),
                        "sense": sense, "rhs": exact.serialize(rhs)})
    return bad


def mixed(spec, limits: Limits | None = None, spec_path: str = "",
          target=None, freeze=None) -> Result:
    from . import lp

    lim = limits or Limits()
    t0 = time.perf_counter()

    def ms():
        return (time.perf_counter() - t0) * 1000

    if not spec.discrete:
        return Result("mixed", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE, ms(), None, detail=t("engine.mixed.no_discrete"))

    # --- 1. the skeleton -------------------------------------------------
    # Either CBC finds it, or it arrives already found. `freeze` matters more
    # than it looks: a real MILP may be solved by HiGHS, Gurobi, a bespoke
    # search or a person, and requiring certo's own solver to reproduce it
    # would put certo's limits in the way of a construction that already
    # exists. Nothing about this step is certified either way, and the
    # certificate never pretends otherwise.
    if freeze is not None:
        raw, engine_used = dict(freeze), "external"
        missing = [v for v in spec.discrete if v not in raw]
        if missing:
            return Result("mixed", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                          ENGINE, ms(), None,
                          detail=t("engine.mixed.freeze_missing",
                                   names=", ".join(missing[:5]),
                                   n=len(missing)))
    else:
        found = lp.opt(_as_milp(spec), lim, use_exact=False)
        if found.verdict is not Verdict.SATISFIABLE:
            return Result("mixed", found.status, Verdict.INCONCLUSIVE, ENGINE,
                          ms(), None, detail=t("engine.mixed.search_failed",
                                               detail=found.detail))
        raw, engine_used = found.meta.get("solution") or {}, "CBC"

    assignment, bad_var = _round_assignment(spec, raw)
    if assignment is None:
        return Result("mixed", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE, ms(), None,
                      detail=t("engine.mixed.out_of_bounds", var=bad_var))

    # --- 2. freeze, and certify the residual exactly ---------------------
    residual, discrete_gain = spec.frozen(assignment)
    cont = lp.opt(residual, lim)
    if cont.verdict is not Verdict.SATISFIABLE:
        return Result("mixed", cont.status, Verdict.INCONCLUSIVE, ENGINE, ms(),
                      None, detail=t("engine.mixed.residual_failed",
                                     detail=cont.detail))
    if not cont.meta.get("exact"):
        return Result("mixed", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE, ms(), None, detail=t("engine.mixed.inexact"))

    cont_values = {k: exact.to_fraction(v)
                   for k, v in (cont.meta.get("solution") or {}).items()}
    conditional = exact.to_fraction(cont.meta["objective"])
    achieved = discrete_gain + conditional

    full_point = dict(assignment)
    full_point.update(cont_values)
    bad = _violations(spec, full_point)
    if bad:
        return Result("mixed", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE, ms(), None,
                      detail=t("engine.mixed.infeasible",
                               name=bad[0]["name"], n=len(bad)))

    # --- 3. the bound over ALL skeletons ---------------------------------
    # One extra LP. When it meets `achieved`, global MILP optimality falls out
    # for free, which happens often enough to be worth asking unprompted.
    relax = lp.opt(spec.relaxed(), lim)
    bound = (exact.to_fraction(relax.meta["objective"])
             if relax.meta.get("exact") else None)
    globally_optimal = bound is not None and bound == achieved

    want = None if target is None else exact.to_fraction(target)
    deficit = None if want is None else want - achieved
    meets = want is None or achieved >= want

    # The residual dual is exact by the time we get here, so the level is at
    # least conditional; `feasible` is what a frozen assignment reaches when
    # its LP was not certified, and that path returns earlier.
    level = GLOBAL if globally_optimal else CONDITIONAL

    cert = mixed_design_certificate(
        assignment={k: exact.serialize(v) for k, v in assignment.items()},
        continuous={k: exact.serialize(v) for k, v in cont_values.items()},
        kinds={v: spec.kind_of(v) for v in spec.var_names},
        skeleton_from=engine_used,
        system=_system(spec),
        objective={k: exact.serialize(exact.to_fraction(v))
                   for k, v in spec.obj.items()},
        sense=spec.sense,
        discrete_gain=exact.serialize(discrete_gain),
        conditional=exact.serialize(conditional),
        achieved=exact.serialize(achieved),
        residual_cert=cont.certificate.to_dict(),
        relaxation_cert=relax.certificate.to_dict() if bound is not None else None,
        bound=None if bound is None else exact.serialize(bound),
        target=None if want is None else exact.serialize(want),
        globally_optimal=globally_optimal, level=level,
        title=spec.title,
        bounds={v: [None if spec.bounds[v][0] is None
                    else exact.serialize(exact.to_fraction(spec.bounds[v][0])),
                    None if spec.bounds[v][1] is None
                    else exact.serialize(exact.to_fraction(spec.bounds[v][1]))]
                for v in spec.var_names},
    ).stamp(spec_path or None)

    if want is not None:
        detail = t("engine.mixed.meets" if meets else "engine.mixed.short",
                   value=exact.serialize(achieved), target=exact.serialize(want),
                   deficit=exact.serialize(abs(deficit)))
    elif globally_optimal:
        detail = t("engine.mixed.optimal", value=exact.serialize(achieved))
    else:
        detail = t("engine.mixed.design", value=exact.serialize(achieved),
                   bound="-" if bound is None else exact.serialize(bound))

    return Result(
        # A construction that exists and reaches its target is SATISFIABLE:
        # something was exhibited. Calling it PROVED would claim the optimum.
        "mixed", Status.SAT,
        Verdict.SATISFIABLE if meets else Verdict.REFUTED,
        ENGINE, ms(), cert, detail=detail,
        meta={"level": level,
              "achieved": exact.serialize(achieved),
              "conditional": exact.serialize(conditional),
              "discrete_gain": exact.serialize(discrete_gain),
              "bound": None if bound is None else exact.serialize(bound),
              "target": None if want is None else exact.serialize(want),
              # The verdict already said this; a script should not have to
              # infer a boolean from a verdict, nor parse it out of `detail`.
              "reached": None if want is None else bool(meets),
              "deficit": None if deficit is None else exact.serialize(deficit),
              "globally_optimal": globally_optimal,
              "selected": sorted(k for k, v in assignment.items() if v),
              "discrete_vars": len(spec.discrete),
              "continuous_vars": len(spec.continuous),
              "skeleton_from": engine_used},
    )


def _as_milp(spec):
    """The search problem: CBC gets the real kinds, via pulp's categories."""
    out = spec.relaxed()
    out.kinds = dict(spec.kinds)
    out.integer = spec.integer
    return out


def _system(spec) -> list:
    """The original constraints, so verification can redo the substitution."""
    return [{"name": n,
             "coeffs": {v: exact.serialize(exact.to_fraction(c))
                        for v, c in coeffs.items()},
             "sense": s, "rhs": exact.serialize(exact.to_fraction(rhs))}
            for n, coeffs, s, rhs in spec.cons]
