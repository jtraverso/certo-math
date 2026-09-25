"""Engines for polynomial ideals, sums of squares, and integers.

Three commands that have nothing to do with SMT, and one shape in common with
everything else here: a search that may be as clever or as numeric as it
likes, and a certificate that is exact and checkable without it.

  parametric A bound that holds for EVERY value of a parameter, not the ones
          you tried. Weak duality, symbolically: `y >= 0` with
          `A(p)^T y >= c(p)` bounds the optimum for all p at once, and each
          inequality is certified on a ray by a shift.

  eliminate  The resultant of two polynomials in one variable, with the
          Bezout identity `Res = A f + B g` attached. Turns "do these two
          share a root in t" into a condition on the other variables.

  ideal   Groebner cofactors. `1 = sum h_i g_i` refutes a polynomial system
          outright; `f = sum h_i g_i` says f follows from it. Either way the
          check is expanding a product.
  sos     A sum of squares, searched for in floating point and then rounded,
          re-projected and re-verified in exact rationals. The floats never
          reach the certificate.
  number  A Pratt primality tree, or a factorisation whose factors carry one.
          Checked with modular exponentiation alone.
"""
from __future__ import annotations

import time

from ..certificate import (cover_certificate, ideal_certificate,
                           number_certificate, parametric_bound_certificate,
                           family_extremum_certificate,
                           first_entry_certificate,
                           integer_matrix_certificate, symmetry_reduction_certificate,
                           first_moment_certificate,
                           ratio_bound_certificate,
                           integer_peak_certificate,
                           resultant_certificate, sos_certificate)
from ..i18n import t
from ..limits import Limits

ENGINE_COLGEN = "certo/column-generation"
from ..polynomials import Budget, Poly, cofactors
from ..status import Result, Status, Verdict

ENGINE_IDEAL = "certo/groebner"
ENGINE_ELIM = "certo/sylvester"
ENGINE_PARAM = "certo/weak-duality"
ENGINE_COVER = "certo/counting"
ENGINE_SOS = "certo/sos"
ENGINE_NUM = "certo/pratt"
ENGINE_LATTICE = "certo/unimodular"
ENGINE_ORBIT = "certo/orbit-quotient"
ENGINE_EXACT = "certo/exact-elimination"
ENGINE_TORIC = "certo/toric-local"
ENGINE_SEMIGROUP = "certo/affine-semigroup"
ENGINE_PROFILE = "certo/capacity-profile"
ENGINE_RANGE = "certo/exact-range"
ENGINE_CYCLE = "certo/growth-classes"
ENGINE_BIND = "certo/lean-binding"


def _poly(expr, variables):
    """A spec's term, whether it arrived as a Poly or as a z3 expression."""
    if isinstance(expr, Poly):
        return expr
    return Poly.from_z3(expr, variables)


# ---------------------------------------------------------------------------


def cover(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """Is this an exact cover, and how many parts does it use?"""
    from ..cover import NotACover, check, clique_parts

    t0 = time.perf_counter()
    universe = [u for u in spec.universe]
    report = None
    try:
        if spec.cliques:
            parts, report = clique_parts(universe, spec.parts, spec.max_size)
        else:
            parts = [list(part) for part in spec.parts]
        out = check(universe, parts, exact=spec.exact)
    except NotACover as e:
        return Result("cover", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_COVER, (time.perf_counter() - t0) * 1000, None,
                      detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    meta = {"parts": out["parts"], "universe": out["universe"],
            "missed": len(out["missed"]), "doubled": len(out["doubled"])}

    if not out["ok"]:
        # Not a cover. No certificate, and the reason is the useful part.
        if out["foreign"]:
            detail = t("engine.cover.foreign", n=len(out["foreign"]))
        elif out["missed"]:
            detail = t("engine.cover.missed", n=len(out["missed"]),
                       names=", ".join(map(str, out["missed"][:4])))
        else:
            detail = t("engine.cover.doubled", n=len(out["doubled"]),
                       names=", ".join(map(str, out["doubled"][:4])))
        return Result("cover", Status.SAT, Verdict.REFUTED, ENGINE_COVER, ms,
                      None, detail=detail, meta=meta)

    cert = cover_certificate(
        universe=[list(u) if isinstance(u, (tuple, list)) else u
                  for u in universe],
        parts=[[list(e) if isinstance(e, (tuple, list)) else e for e in part]
               for part in parts],
        exact=spec.exact, cliques=spec.cliques,
        multiplicities={}, part_report=report, max_size=spec.max_size,
        title=spec.title,
    ).stamp(spec_path or None)

    return Result("cover", Status.UNSAT, Verdict.PROVED, ENGINE_COVER, ms,
                  cert,
                  detail=t("engine.cover.proved" if spec.exact
                           else "engine.cover.proved_atleast",
                           parts=out["parts"], n=out["universe"]),
                  meta=meta)


def cover_bounds(spec, limits=None, prove_optimal=False, max_nodes=5_000,
                 wall_ms=None) -> dict:
    """The relaxation's exact lower bound, and the integer optimum if asked.

    Returned as data rather than folded into the cover's verdict: the cover is
    one claim and the bound is another, and a single verdict covering both is
    how "valid" gets read as "optimal".
    """
    from . import bb, lp

    out = {"relaxation": None, "optimum": None, "stopped": None}
    relaxed = lp.opt(spec.to_lp(integral=False), limits)
    if relaxed.verdict is Verdict.SATISFIABLE and relaxed.meta.get("exact"):
        out["relaxation"] = relaxed.meta["objective"]
        out["relaxation_cert"] = relaxed.certificate
    else:
        out["relaxation_failed"] = relaxed.detail

    if prove_optimal:
        got = bb.prove_optimal(spec.to_lp(integral=True), limits,
                               max_nodes=max_nodes, wall_ms=wall_ms)
        if got.verdict is Verdict.PROVED:
            out["optimum"] = got.meta["optimum"]
            out["optimum_cert"] = got.certificate
        else:
            # Not a failure: a partial result, and it says which.
            out["stopped"] = got.meta
            out["stopped_detail"] = got.detail
    return out


def entry(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """Where a sequence first crosses a threshold, and how far past it lands."""
    from ..entry import NotAnEntry, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotAnEntry as e:
        return Result("entry", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    if out["index"] is None:
        n = len(spec.values() if callable(spec.values) else spec.values)
        return Result("entry", Status.SAT, Verdict.REFUTED, ENGINE_PARAM, ms,
                      None,
                      detail=t("engine.entry.never",
                               threshold=str(out["threshold"]), n=n),
                      meta={"crossed": False})
    if not out["steps_ok"]:
        return Result("entry", Status.SAT, Verdict.REFUTED, ENGINE_PARAM, ms,
                      None,
                      detail=t("engine.entry.steps", delta=out["step_bound"]),
                      meta={"index": out["index"]})

    cert = first_entry_certificate(
        index=out["index"], prefix=out["prefix"],
        threshold=str(out["threshold"]), direction=out["direction"],
        strict=out["strict"], step_bound=out["step_bound"],
        window=out["window"], title=spec.title,
    ).stamp(spec_path or None)

    key = "engine.entry.window" if out["window"] else "engine.entry.proved"
    return Result("entry", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM, ms,
                  cert,
                  detail=t(key, index=out["index"], value=out["prefix"][-1],
                           threshold=str(out["threshold"]),
                           window=out["window"] or "-"),
                  meta={"index": out["index"], "value": out["prefix"][-1],
                        "window": out["window"] or ""})


def moment(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """The first moment, exactly, and the existence a mean below one buys."""
    from ..moment import NotAMoment, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotAMoment as e:
        return Result("moment", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    shown = str(out["expectation"])
    if out["out_of_range"]:
        return Result("moment", Status.OUT_OF_THEORY, Verdict.REFUTED,
                      ENGINE_PARAM, ms, None,
                      detail=t("engine.moment.range",
                               n=len(out["out_of_range"]),
                               names=", ".join(out["out_of_range"][:4])),
                      meta={"expectation": shown})
    if not out["holds"]:
        # Not a failed route: the sum is the sum, and it is on the wrong side.
        return Result("moment", Status.SAT, Verdict.REFUTED, ENGINE_PARAM, ms,
                      None,
                      detail=t("engine.moment.fails", value=shown,
                               rel=out["relation"],
                               threshold=str(out["threshold"])),
                      meta={"expectation": shown})

    cert = first_moment_certificate(
        terms=out["terms"], expectation=shown,
        threshold=str(out["threshold"]), relation=out["relation"],
        counts=out["counts"], concludes=out["concludes"],
        masses=out["masses"], title=spec.title,
    ).stamp(spec_path or None)

    key = "engine.moment.exists" if out["concludes"] else "engine.moment.bound"
    return Result("moment", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM, ms,
                  cert,
                  detail=t(key, value=shown, rel=out["relation"],
                           threshold=str(out["threshold"]),
                           n=len(out["terms"])),
                  meta={"expectation": shown, "exists": out["concludes"]})


def reduce_parametric(spec, limits: Limits | None = None,
                      spec_path: str = "") -> Result:
    """The symbolic quotient of a family, tested against a finite window."""
    from ..certificate import parametric_symmetry_certificate
    from ..paramsym import NotParametricSymmetry, certify as run

    t0 = time.perf_counter()
    try:
        out = run(spec, limits)
    except NotParametricSymmetry as e:
        return Result("reduce", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_ORBIT, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    if not out["ok"]:
        first = out["failed"][0]
        return Result(
            "reduce", Status.SAT, Verdict.REFUTED, ENGINE_ORBIT, ms, None,
            detail=t("engine.paramsym.failed", n=len(out["failed"]),
                     total=out["checked"],
                     at=", ".join("{}={}".format(k, v)
                                  for k, v in sorted(first.items()))),
            meta={"checked": out["checked"], "failed": len(out["failed"])})

    cert = parametric_symmetry_certificate(
        out, title=spec.title).stamp(spec_path or None)
    return Result(
        "reduce", Status.UNSAT, Verdict.PROVED, ENGINE_ORBIT, ms, cert,
        detail=t("engine.paramsym.proved", n=out["checked"],
                 orbits=len(out["orbits"]),
                 params=", ".join(out["parameters"]),
                 regimes=len(out["regimes"])),
        meta={"points": out["checked"], "orbits": len(out["orbits"]),
              "regimes": sorted(out["regimes"]),
              "objects": out["objects_text"]})


def linear_system(spec, limits: Limits | None = None,
                  spec_path: str = "") -> Result:
    """`A x = b` exactly, with a witness whichever way it goes."""
    from ..certificate import linear_system_certificate
    from ..linsolve import MANY, NONE, NotSolvable, UNIQUE, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotSolvable as e:
        return Result("solve", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_EXACT, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = linear_system_certificate(out, title=spec.title).stamp(
        spec_path or None)

    rows, cols = len(out["matrix"]), out["columns"]
    if out["status"] == NONE:
        detail = t("engine.solve.none", rows=rows, cols=cols,
                   domain=out["domain"])
        verdict, status = Verdict.REFUTED, Status.UNSAT
    elif out["status"] == MANY:
        detail = t("engine.solve.many", n=len(out["kernel"]), cols=cols)
        verdict, status = Verdict.PROVED, Status.SAT
    else:
        detail = t("engine.solve.unique", cols=cols, domain=out["domain"])
        verdict, status = Verdict.PROVED, Status.SAT
        _ = UNIQUE

    return Result("solve", status, verdict, ENGINE_EXACT, ms, cert,
                  detail=detail,
                  meta={"status": out["status"], "rank": out["rank"],
                        "rows": rows, "columns": cols,
                        "kernel_dimension": len(out["kernel"]),
                        "domain": out["domain"],
                        "solution": out["solution"]})


def equitable_quotient(spec, limits: Limits | None = None,
                       spec_path: str = "") -> Result:
    """The quotient as an equivalence: same attainable values, by two maps."""
    from ..certificate import equitable_quotient_certificate
    from ..equitable import NotEquitable, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotEquitable as e:
        return Result("quotient", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_ORBIT, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = equitable_quotient_certificate(out, title=spec.title).stamp(
        spec_path or None)
    return Result(
        "quotient", Status.UNSAT, Verdict.PROVED, ENGINE_ORBIT, ms, cert,
        detail=t("engine.quotient.proved",
                 prows=out["physical_rows"], pcols=out["physical_columns"],
                 rows=len(out["N"]), cols=len(out["M"])),
        meta={"physical_rows": out["physical_rows"],
              "physical_columns": out["physical_columns"],
              "rows": len(out["N"]), "columns": len(out["M"]),
              "identities": len(out["B"])})


def clique_lp(spec, limits: Limits | None = None,
              spec_path: str = "") -> Result:
    """An LP over every clique of a graph, by column generation, with the
    pricing search that proves no other clique would enter."""
    from .. import colgen
    from ..certificate import clique_lp_certificate

    t0 = time.perf_counter()
    try:
        out = colgen.solve(spec, limits)
    except colgen.NotACliqueLP as e:
        return Result("columns", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_COLGEN, 0.0, None, detail=str(e))
    except colgen.PricingBudget as e:
        return Result("columns", Status.RESOURCE_EXHAUSTED,
                      Verdict.INCONCLUSIVE, ENGINE_COLGEN,
                      (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.colgen.budget", where=str(e)))
    except ArithmeticError as e:
        return Result("columns", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE_COLGEN, (time.perf_counter() - t0) * 1000, None,
                      detail=str(e))
    ms = (time.perf_counter() - t0) * 1000
    if "infeasible_edge" in out:
        return Result("columns", Status.UNSAT, Verdict.UNSATISFIABLE,
                      ENGINE_COLGEN, ms, None,
                      detail=t("engine.colgen.no_clique_covers",
                               edge=out["infeasible_edge"],
                               m=getattr(spec, "min_size", 2)))
    cert = clique_lp_certificate(out, title=spec.title).stamp(spec_path or None)
    p = cert.payload
    return Result(
        "columns", Status.SAT, Verdict.SATISFIABLE, ENGINE_COLGEN, ms, cert,
        detail=t("engine.colgen.optimum", value=p["objective"],
                 problem=p["problem"], generated=out["generated"],
                 rounds=out["rounds"], nodes=p["pricing"]["nodes"]),
        meta={"objective": p["objective"], "problem": p["problem"],
              "vertices": len(p["vertices"]), "edges": len(p["edges"]),
              "generated": out["generated"], "rounds": out["rounds"],
              "support": len(p["columns"]),
              "nodes": p["pricing"]["nodes"], "exact": True})


def capacity_profile(spec, limits: Limits | None = None,
                     spec_path: str = "") -> Result:
    """A proposed profile, decided: bound, attainment and coverage."""
    from ..certificate import capacity_profile_certificate
    from ..profile import NotAProfile, certify

    from ..profile import Undiscovered, discover

    t0 = time.perf_counter()

    # NO SEGMENTS MEANS FIND THEM. The search proposes breakpoints, duals and
    # sources; `certify` then admits or refuses them on exactly the same terms
    # as a profile written by hand. A search with a bug in it cannot produce a
    # wrong certificate, only a refused one -- which is why the checking half
    # was built first and this half could come after.
    found = None
    if not getattr(spec, "segments", None):
        try:
            found = discover(spec)
        except NotAProfile as e:
            return Result("profile", Status.OUT_OF_THEORY,
                          Verdict.INCONCLUSIVE, ENGINE_PROFILE, 0.0, None,
                          detail=str(e))
        except Undiscovered as e:
            return Result("profile", Status.RESOURCE_EXHAUSTED,
                          Verdict.INCONCLUSIVE, ENGINE_PROFILE,
                          (time.perf_counter() - t0) * 1000, None,
                          detail=str(e))
        spec.segments = found["segments"]
        spec.sources = found["sources"]

    try:
        out = certify(spec)
    except NotAProfile as e:
        return Result("profile", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PROFILE, 0.0, None, detail=str(e))
    ms = (time.perf_counter() - t0) * 1000

    if not out["holds"]:
        # No certificate. A profile that does not hold is not a smaller
        # profile, and a payload claiming one would fail its own verifier.
        why = ", ".join(sorted({f["why"] for f in out["failures"]}))
        return Result(
            "profile", Status.SAT, Verdict.REFUTED, ENGINE_PROFILE, ms, None,
            detail=t("engine.profile.fails", why=why),
            meta={"holds": False, "failures": out["failures"][:6],
                  "segments": len(out["segments"])})

    out["discovered"] = found is not None
    if found is not None:
        out["solves"] = found["solves"]
    cert = capacity_profile_certificate(out, title=spec.title).stamp(
        spec_path or None)
    detail = (t("engine.profile.found", n=len(out["segments"]),
                s=found["solves"]) if found is not None else
              t("engine.profile.holds", parameter=out["parameter"],
                lo=out["domain"]["lo"], hi=out["domain"]["hi"],
                n=len(out["segments"]), b=len(out["breakpoints"])))
    return Result(
        "profile", Status.UNSAT, Verdict.PROVED, ENGINE_PROFILE, ms, cert,
        detail=detail,
        meta={"holds": True, "segments": len(out["segments"]),
              "breakpoints": out["breakpoints"],
              "parameter": out["parameter"],
              "discovered": found is not None,
              "solves": None if found is None else found["solves"],
              "piecewise": [p["value"] for p in out["piecewise"]]})


def affine_semigroup(spec, limits: Limits | None = None,
                    spec_path: str = "") -> Result:
    """The finite questions about `S = N.a_1 + ... + N.a_k`, each with its
    check."""
    from ..certificate import affine_semigroup_certificate
    from ..semigroup import NotASemigroup, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotASemigroup as e:
        return Result("semigroup", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_SEMIGROUP, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000

    # A semigroup with no grading is not a failure to report as one: it is a
    # statement about the object, and every search below it would be infinite.
    # The certificate is still worth having -- the generators, the rank and
    # the cone answers are all established -- so it is emitted and the verdict
    # says what was NOT settled.
    if not out["pointed"]:
        cert = affine_semigroup_certificate(out, title=spec.title).stamp(
            spec_path or None)
        # Proved not pointed, or not decided: the same verdict, because no
        # search terminates in either case, but not the same sentence.
        if out["pointed"] is False:
            detail = t("engine.semigroup.not_pointed_proved",
                       witness=", ".join(map(str, out["not_pointed_witness"])))
        else:
            detail = t("engine.semigroup.not_pointed")
        return Result(
            "semigroup", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
            ENGINE_SEMIGROUP, ms, cert, detail=detail,
            meta={"generators": len(out["order"]), "rank": out["rank"],
                  "dimension": out["dimension"], "pointed": out["pointed"],
                  "backend": out["backend"]})

    cert = affine_semigroup_certificate(out, title=spec.title).stamp(
        spec_path or None)

    detail = t("engine.semigroup.summary", gens=len(out["order"]),
               rank=out["rank"])
    if out["not_normal"]:
        detail += " -- " + t("engine.semigroup.not_normal",
                             n=len(out["normality_witnesses"]))
    if out["redundant"]:
        detail += " -- " + t("engine.semigroup.redundant",
                             n=len(out["redundant"]))

    meta = {"generators": len(out["order"]), "rank": out["rank"],
            "dimension": out["dimension"], "pointed": True,
            "backend": out["backend"],
            "minimal": out["minimal"],
            "not_normal": out["not_normal"],
            "witnesses": list(out["normality_witnesses"]),
            "redundant": sorted(out["redundant"])}

    hb = out.get("hilbert")
    if hb is not None:
        verdict = hb["is_minimal_generating_set"]
        meta["hilbert"] = verdict
        if verdict is True:
            detail += " -- " + t("engine.semigroup.hilbert_yes")
        elif verdict is False:
            detail += " -- " + t("engine.semigroup.hilbert_no",
                                 why=", ".join(hb["why_not"][:3]) or "-")
        else:
            detail += " -- " + t("engine.semigroup.hilbert_unknown")

    return Result(
        "semigroup", Status.UNSAT, Verdict.PROVED, ENGINE_SEMIGROUP, ms, cert,
        detail=detail, meta=meta)


def toric_cone(spec, limits: Limits | None = None,
               spec_path: str = "") -> Result:
    """The local data of a cone: primitivity, multiplicity, height,
    discrepancy."""
    from ..certificate import toric_cone_certificate
    from ..toric import NotToric, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotToric as e:
        return Result("cone", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_TORIC, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = toric_cone_certificate(out, title=spec.title).stamp(
        spec_path or None)
    return Result(
        "cone", Status.UNSAT, Verdict.PROVED, ENGINE_TORIC, ms, cert,
        detail=t("engine.toric.proved", n=len(out["order"]),
                 dim=out["dimension"],
                 mult=out["multiplicity"] if out["multiplicity"] is not None
                      else t("engine.toric.no_multiplicity"),
                 where=out["multiplicity_in"],
                 height="yes" if out["height_one"] else "no"),
        meta={"multiplicity": out["multiplicity"],
              "multiplicity_in": out["multiplicity_in"],
              "regular": out["regular"], "height_one": out["height_one"],
              "crepant": out["crepant"],
              "height_functional": out["height_functional"],
              "discrepancies": out["discrepancies"]})


def variable_range(spec, var, limits: Limits | None = None,
                   spec_path: str = "") -> Result:
    """How far a variable may go over the regime, with a dual at each end."""
    from ..certificate import range_certificate
    from ..rangebound import NotRangeable, bounds_of

    t0 = time.perf_counter()
    try:
        out = bounds_of(spec, var, limits)
    except NotRangeable as e:
        return Result("range", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_RANGE, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = range_certificate(out, title=spec.title).stamp(spec_path or None)

    if out["empty"]:
        # Not a range and not a failure: the regime has no points, which is
        # the answer `check --hypotheses-only` gives with a minimal clash.
        return Result(
            "range", Status.UNSAT, Verdict.PROVED, ENGINE_RANGE, ms, cert,
            detail=t("engine.varrange.empty", var=var),
            meta={"empty": True, "interval": out["interval"]})

    return Result(
        "range", Status.SAT, Verdict.SATISFIABLE, ENGINE_RANGE, ms, cert,
        detail=t("engine.varrange.found", var=var, interval=out["interval"]),
        meta={"empty": False, "interval": out["interval"],
              "lower": out["lower"]["bound"], "upper": out["upper"]["bound"]})


def dependency_cycle(spec, limits: Limits | None = None,
                     spec_path: str = "") -> Result:
    """Compose the declared growth classes around the chain and close it."""
    from ..certificate import dependency_cycle_certificate
    from ..cycles import NotCyclic, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotCyclic as e:
        return Result("cycle", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_CYCLE, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = dependency_cycle_certificate(out, title=spec.title).stamp(
        spec_path or None)
    arrow = " -> ".join(out["cycle"])

    if out["empty"]:
        return Result(
            "cycle", Status.UNSAT, Verdict.PROVED, ENGINE_CYCLE, ms, cert,
            detail=t("engine.cycle.empty", cycle=arrow,
                     param=out["parameter"]),
            meta={"empty": True, "cycle": out["cycle"]})

    # Never "there is no cycle": only that composing these classes did not
    # refute the closing constraint.
    return Result(
        "cycle", Status.SAT, Verdict.SATISFIABLE, ENGINE_CYCLE, ms, cert,
        detail=t("engine.cycle.open", cycle=arrow, why=out.get("why") or "-"),
        meta={"empty": False, "cycle": out["cycle"], "why": out.get("why")})


def lean_binding(spec, limits: Limits | None = None,
                 spec_path: str = "") -> Result:
    """Does the declaration provide what the certificate assumed?"""
    from ..binding import NotBindable, certify
    from ..certificate import lean_binding_certificate

    t0 = time.perf_counter()
    try:
        out = certify(spec, limits)
    except NotBindable as e:
        return Result("bind", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_BIND, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = lean_binding_certificate(out, title=spec.title).stamp(
        spec_path or None)

    if out["covers"]:
        return Result(
            "bind", Status.UNSAT, Verdict.PROVED, ENGINE_BIND, ms, cert,
            detail=t("engine.bind.covers", decl=out["declaration"] or "-",
                     name=out["discharges"]),
            meta={"covers": True, "declaration": out["declaration"]})

    return Result(
        "bind", Status.SAT, Verdict.REFUTED, ENGINE_BIND, ms, cert,
        detail=t("engine.bind.gap", decl=out["declaration"] or "-",
                 name=out["discharges"]),
        meta={"covers": False, "declaration": out["declaration"]})


def integer_matrix(spec, limits: Limits | None = None,
                   spec_path: str = "") -> Result:
    """rank, determinant, Hermite or Smith, exactly, with the transforms --
    or, for a symmetric rational matrix, its inertia."""
    from ..lattice import NotAnIntegerMatrix, analyse, parse, shape

    if spec.question in ("inertia", "psd"):
        return symmetric_inertia(spec, limits, spec_path)

    t0 = time.perf_counter()
    try:
        source = spec.matrix
        if isinstance(source, (str, bytes)) or hasattr(source, "__fspath__"):
            # A path, not a matrix: the data came from the other side of the
            # boundary and was written by whatever holds the real object.
            from ..interchange import load

            source = load(source)["entries"]
        elif isinstance(source, dict) and "entries" in source:
            source = source["entries"]
        A = parse(source)
        if spec.rows is not None:
            A = [A[i] for i in spec.rows]
        if spec.cols is not None:
            A = [[row[j] for j in spec.cols] for row in A]
        if not A or not A[0]:
            raise NotAnIntegerMatrix(t("lattice.empty", name="submatrix"))
        out = analyse(A, spec.question)
    except (NotAnIntegerMatrix, IndexError) as e:
        return Result("matrix", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_LATTICE, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    n, m = shape(A)
    payload = {k: v for k, v in out.items() if k != "question"}
    # The number the other side of the boundary computes over its own copy.
    # `matrix` certifies the matrix it was GIVEN; this is what lets somebody
    # establish, independently, that it was the right one.
    from ..interchange import describe, fingerprint

    payload["fingerprint"] = str(fingerprint(A))
    payload["fingerprint_recipe"] = describe()
    cert = integer_matrix_certificate(
        question=out["question"], matrix=A, result=payload,
        title=spec.title).stamp(spec_path or None)

    if spec.question in ("det", "determinant"):
        detail = t("engine.lattice.det", d=out["det"], n=n)
    elif spec.question == "rank":
        detail = t("engine.lattice.rank", r=out["rank"], n=n, m=m)
    elif spec.question == "smith":
        detail = t("engine.lattice.smith", r=out["rank"],
                   values=", ".join(map(str, out["invariants"])) or "-")
    else:
        detail = t("engine.lattice.hermite", r=out["rank"], n=n, m=m)

    return Result("matrix", Status.UNSAT, Verdict.PROVED, ENGINE_LATTICE, ms,
                  cert, detail=detail,
                  meta={"rank": out["rank"], "determinant": out.get("det"),
                        "rows": n, "cols": m,
                        "invariants": out.get("invariants")})


def symmetric_inertia(spec, limits: Limits | None = None,
                      spec_path: str = "") -> Result:
    """The inertia of a symmetric rational matrix, by a congruence `S A S^T =
    D` carried with `S`'s inverse. `question="psd"` asks the yes-or-no
    version: PROVED with the congruence, REFUTED with a vector `x` where
    `x^T A x < 0`."""
    from .. import inertia as inr
    from ..certificate import symmetric_inertia_certificate

    t0 = time.perf_counter()
    try:
        rows = spec.matrix
        if isinstance(rows, dict) and "entries" in rows:
            rows = rows["entries"]
        A = inr.parse(rows)
        if spec.rows is not None or spec.cols is not None:
            # A principal submatrix, the only kind that stays symmetric: the
            # same indices for the rows and the columns.
            idx = spec.rows if spec.rows is not None else spec.cols
            if spec.cols is not None and list(spec.cols) != list(idx):
                raise inr.NotSymmetric(t("inertia.principal_only"))
            A = [[A[i][j] for j in idx] for i in idx]
        out = inr.inertia(A)
    except (inr.NotSymmetric, IndexError) as e:
        return Result("matrix", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_LATTICE, 0.0, None, detail=str(e))
    ms = (time.perf_counter() - t0) * 1000

    cert = symmetric_inertia_certificate(
        question=spec.question, matrix=out["matrix"], S=out["S"],
        S_inv=out["S_inv"], D=out["D"], witness=out["witness"],
        title=spec.title).stamp(spec_path or None)
    n = len(out["D"])
    meta = {"n_plus": out["n_plus"], "n_minus": out["n_minus"],
            "n_zero": out["n_zero"], "rank": out["rank"], "psd": out["psd"],
            "pd": out["pd"], "rows": n, "cols": n}
    if spec.question == "psd" and not out["psd"]:
        value = str(inr.quadratic(out["matrix"], out["witness"]))
        return Result("matrix", Status.SAT, Verdict.REFUTED, ENGINE_LATTICE,
                      ms, cert, detail=t("engine.inertia.not_psd", value=value),
                      meta=meta)
    key = ("engine.inertia.psd" if spec.question == "psd"
           else "engine.inertia.counts")
    return Result("matrix", Status.UNSAT, Verdict.PROVED, ENGINE_LATTICE, ms,
                  cert, detail=t(key, plus=out["n_plus"], minus=out["n_minus"],
                                 zero=out["n_zero"], n=n,
                                 pd=t("engine.inertia.pd") if out["pd"] else ""),
                  meta=meta)


def reduce_symmetry(spec, limits: Limits | None = None,
                    spec_path: str = "") -> Result:
    """Check the group, then quotient the program by its orbits."""
    from ..symmetry import NotSymmetric, certify
    from ..tree import system_of

    t0 = time.perf_counter()
    lp = spec.lp.to_lp() if hasattr(spec.lp, "to_lp") else spec.lp
    try:
        out = certify(lp, spec.generators)
    except NotSymmetric as e:
        return Result("reduce", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = symmetry_reduction_certificate(
        sense=lp.sense, generators=out["generators"], orbits=out["orbits"],
        system=system_of(lp), quotient=system_of(out["quotient"]),
        title=spec.title,
    ).stamp(spec_path or None)

    return Result("reduce", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM, ms,
                  cert,
                  detail=t("engine.symmetry.proved",
                           v=out["variables"], o=out["reduced_variables"],
                           r=out["rows"], rr=out["reduced_rows"]),
                  meta={"variables": out["variables"],
                        "orbits": out["reduced_variables"],
                        "rows": out["rows"],
                        "reduced_rows": out["reduced_rows"]})


def ratio(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """A rational-function inequality, for every parameter at once, no solver."""
    from ..ratio import NotARatio, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotARatio as e:
        return Result("ratio", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    floor = ", ".join("{} >= {}".format(k, v)
                      for k, v in spec.parameters.items())
    ln, ld = out["left"]
    rn, rd = out["right"]

    def show(num, den):
        return str(num) or "0" if str(den) == "1"             else "({}) / ({})".format(str(num) or "0", str(den))

    if not out["ok"]:
        if not (out["left_positive"] and out["right_positive"]):
            which = ", ".join(x for x, ok in ((str(ld), out["left_positive"]),
                                              (str(rd), out["right_positive"]))
                              if not ok)
            detail = t("engine.ratio.denominator", which=which)
        else:
            detail = t("engine.ratio.not_shown", floor=floor,
                       difference=str(out["difference"]) or "0")
        return Result("ratio", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, ms, None, detail=detail,
                      meta={"difference": str(out["difference"]) or "0"})

    cert = ratio_bound_certificate(
        parameters=dict(spec.parameters),
        left=[ln.serialize(), ld.serialize()],
        right=[rn.serialize(), rd.serialize()],
        relation=spec.relation, difference=out["difference"].serialize(),
        region=out["region"] or None, title=spec.title,
    ).stamp(spec_path or None)

    return Result("ratio", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM, ms,
                  cert,
                  detail=t("engine.ratio.proved", floor=floor,
                           left=show(ln, ld), rel=spec.relation,
                           right=show(rn, rd)),
                  meta={"difference": str(out["difference"]) or "0",
                        "floor": floor})


def family_max(spec, limits: Limits | None = None,
               spec_path: str = "") -> Result:
    """The largest of a finite family of linear programs, and why nothing beats it."""
    from ..family import NotAFamily, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec, limits)
    except NotAFamily as e:
        return Result("family", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = family_extremum_certificate(
        value=str(out["value"]), argmax=out["argmax"], primal=out["primal"],
        dual=out["dual"], bounds=out["bounds"], ids=out["ids"],
        count=out["count"], title=spec.title,
    ).stamp(spec_path or None)

    return Result("family", Status.SAT, Verdict.SATISFIABLE, ENGINE_PARAM, ms,
                  cert,
                  detail=t("engine.family.proved", value=str(out["value"]),
                           argmax=out["argmax"], n=out["count"]),
                  meta={"value": str(out["value"]), "argmax": out["argmax"],
                        "items": out["count"]})


def exists(spec, limits: Limits | None = None, spec_path: str = "",
           backend: str = "internal", max_parts=None) -> Result:
    """Does a cover exist at all? And when it does not, the refutation.

    Two answers, two certificates, and neither of them trusts the solver. A
    model is handed to `cover`'s own verifier, which checks it by counting; a
    refutation is a DRAT proof, checked by unit propagation.
    """
    from ..existence import NotEncodable, encode
    from . import sat

    t0 = time.perf_counter()
    candidates = spec.candidates if spec.candidates is not None else spec.parts
    if candidates is None:
        return Result("exists", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_COVER, 0.0, None,
                      detail=t("engine.exists.no_candidates"))
    universe = [u for u in spec.universe]
    # An EMPTY UNIVERSE has a cover, and it is the empty family. `cover`
    # certifies exactly that -- "0 parts, every one of the 0 elements in
    # exactly one" -- while `exists` refused the same spec as having "no
    # content": two commands, one object, one certifying and one declining.
    #
    # The refusal was the vacuity reflex misapplied. Vacuity matters when a
    # hypothesis set is contradictory, because the proof is then about
    # nothing; here the question has an answer and a witness. So it is
    # answered, and the warning says what it does not establish.
    if not universe:
        from ..certificate import cover_certificate

        cert = cover_certificate(
            universe=[], parts=[], exact=spec.exact, cliques=spec.cliques,
            multiplicities={}, part_report=None, max_size=spec.max_size,
            title=spec.title,
        ).stamp(spec_path or None)
        return Result(
            "exists", Status.SAT, Verdict.PROVED, ENGINE_COVER,
            (time.perf_counter() - t0) * 1000, cert,
            detail=t("engine.exists.empty_universe"),
            meta={"universe": 0, "candidates": 0, "vacuous": True})

    if spec.cliques:
        # Vertex sets, so the parts are the edges they span -- the same
        # reading `cover --cliques` uses, and the reason a triangle is three
        # edges here rather than three vertices.
        from ..cover import clique_parts

        candidates, _report = clique_parts(universe, candidates, spec.max_size)

    try:
        cnf, parts = encode(universe, candidates, exact=spec.exact,
                            max_parts=max_parts, title=spec.title)
    except NotEncodable as e:
        return Result("exists", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_COVER, 0.0, None, detail=str(e))

    got = sat.cases(cnf, limits, backend=backend)
    ms = (time.perf_counter() - t0) * 1000
    meta = {"universe": len(universe), "candidates": len(parts),
            "vars": cnf.nvars, "clauses": len(cnf.clauses),
            "exact": bool(spec.exact)}
    if max_parts is not None:
        meta["max_parts"] = max_parts

    if got.verdict is Verdict.INCONCLUSIVE:
        return Result("exists", got.status, Verdict.INCONCLUSIVE, got.engine,
                      ms, None, detail=got.detail, meta=meta)

    if got.verdict is Verdict.SATISFIABLE:
        # The solver's model is a SUGGESTION. What is certified is the cover
        # it names, checked by counting -- the same verifier a hand-written
        # cover goes through.
        chosen = [parts[i] for i in _chosen(cnf, got)]
        from ..spec import CoverSpec

        found = cover(CoverSpec(universe=universe, parts=chosen,
                                exact=spec.exact, title=spec.title),
                      limits, spec_path)
        return Result("exists", Status.SAT, Verdict.SATISFIABLE,
                      found.engine, ms, found.certificate,
                      detail=t("engine.exists.found", n=len(chosen),
                               total=len(parts)),
                      meta={**meta, "parts": len(chosen)})

    # No cover exists over these candidates, and the DRAT proof says so.
    return Result("exists", Status.UNSAT, Verdict.PROVED, got.engine, ms,
                  got.certificate,
                  detail=t("engine.exists.none" if spec.exact
                           else "engine.exists.none_atleast",
                           n=len(parts), universe=len(universe)),
                  meta={**meta, **got.meta})


def _chosen(cnf, got) -> list:
    """Which candidate indices the model selected."""
    payload = got.certificate.payload if got.certificate else {}
    out = []
    for v in payload.get("true_vars") or []:
        name = cnf.name_of(v)
        if name.startswith("part_"):
            out.append(int(name[5:]))
    return sorted(out)


def peak(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """The best integer choice, for every parameter value at once."""
    from ..peak import NotAPeak, certify

    t0 = time.perf_counter()
    try:
        out = certify(spec)
    except NotAPeak as e:
        return Result("peak", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    floor = ", ".join("{} >= {}".format(k, v)
                      for k, v in spec.parameters.items())

    if not out["ok"]:
        # Each failure is its own sentence, because they mean different
        # things: a convex objective has no peak to find, a fractional
        # maximiser is not a point, and a failed step test is this route
        # coming up short rather than the claim being false.
        if not out["concave"]:
            detail = t("engine.peak.not_concave", lead=str(out["A"]) or "0")
        elif not out["integral"]:
            detail = t("engine.peak.fractional",
                       coefs=", ".join(out["fractional"][:4]))
        else:
            detail = t("engine.peak.not_shown", floor=floor,
                       slope=str(out["slope"]) or "0")
        return Result("peak", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, ms, None, detail=detail,
                      meta={"slope": str(out["slope"]) or "0"})

    cert = integer_peak_certificate(
        parameters=dict(spec.parameters), variable=spec.variable,
        objective=spec.objective.serialize(),
        argmax=out["argmax"].serialize(),
        value=out["value"].serialize(),
        region=out["region"] or None, title=spec.title,
    ).stamp(spec_path or None)

    return Result("peak", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM, ms, cert,
                  detail=t("engine.peak.proved", value=str(out["value"]) or "0",
                           argmax=str(out["argmax"]) or "0", floor=floor),
                  meta={"value": str(out["value"]) or "0",
                        "argmax": str(out["argmax"]) or "0",
                        "floor": floor})


def parametric(spec, limits: Limits | None = None,
               spec_path: str = "") -> Result:
    """`opt(p) <= b(p).y` for every p at or above the floor, or why not."""
    from ..linarith import NotPolynomial
    from ..parametric import NotParametric, certify

    t0 = time.perf_counter()

    # Two shapes: a packing (max, `<=`, bounded from above) and a cover (min,
    # `>=`, bounded from below). Mixing the rows of one into the other is a
    # modelling mistake, not a harder problem, so it is named rather than run.
    if spec.sense not in ("max", "min"):
        return Result("parametric", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None,
                      detail=t("engine.param.max_only", sense=spec.sense))
    want = "<=" if spec.sense == "max" else ">="
    # A primal only has to be FEASIBLE, so any sense is fine there; with a
    # dual, an equality row is fine too -- its dual simply has no sign.
    allowed = ({"<=", ">=", "=="} if getattr(spec, "primal", None) is not None
               else {want, "=="})
    bad_sense = [n for n, _, sense, _ in spec.constraints
                 if sense not in allowed]
    if bad_sense:
        return Result("parametric", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None,
                      detail=t("engine.param.le_only", sense=spec.sense,
                               want=want,
                               names=", ".join(map(str, bad_sense[:4]))))
    try:
        out = certify(spec)
    except (NotParametric, NotPolynomial) as e:
        return Result("parametric", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, 0.0, None, detail=str(e))
    if out.get("witness") == "pieces":
        return _parametric_pieces(spec, out, t0, spec_path)

    ms = (time.perf_counter() - t0) * 1000
    floor = ", ".join("{} >= {}".format(k, v)
                      for k, v in spec.parameters.items())
    if out.get("box"):
        floor = ", ".join("{} in [{}, {}]".format(n, lo, hi)
                          for n, (lo, hi) in out["box"].items())

    if not out["ok"]:
        # No certificate. The shift is sufficient and not necessary, so a
        # failure is "not established by this route" and never "false" -- and
        # emitting a certificate for it would be the overclaim this whole
        # project exists to avoid.
        if out["negative_dual"] and out.get("witness") == "primal":
            detail = t("engine.param.primal_negative",
                       names=", ".join(map(str, out["negative_dual"][:4])))
        elif out.get("witness") == "primal":
            detail = t("engine.param.primal_infeasible",
                       names=", ".join(out["failed"][:4]), floor=floor)
        elif out["negative_dual"]:
            detail = t("engine.param.negative",
                       names=", ".join(map(str, out["negative_dual"][:4])))
        else:
            detail = t("engine.param.not_shown_box" if out.get("box")
                       else "engine.param.not_shown",
                       names=", ".join(out["failed"][:4]), floor=floor)
        return Result("parametric", Status.UNKNOWN_SOLVER,
                      Verdict.INCONCLUSIVE, ENGINE_PARAM, ms, None,
                      detail=detail,
                      meta={"failed_columns": out["failed"]})

    cert = parametric_bound_certificate(
        parameters=dict(spec.parameters),
        variables=out["variables"],
        objective={v: _ser(spec, c) for v, c in spec.objective.items()},
        constraints=[[str(n), {v: _ser(spec, c) for v, c in row.items()},
                      sense, _ser(spec, rhs)]
                     for n, row, sense, rhs in spec.constraints],
        dual=_dual_texts(spec, out),
        # Only when it says something the readable form cannot: a dual of pure
        # rationals is exactly what `dual` already holds, and a second copy of
        # it would be a field nothing checks.
        dual_poly=_dual_polys(spec, out),
        box=out.get("box"),
        box_trees=out.get("box_trees"),
        free=out.get("free") or None,
        claim=out.get("claim"),
        primal=out.get("primal"),
        sense=out["sense"],
        region=out["region"] or None,
        bound=out["bound"].serialize(),
        rows=out["rows"],
        title=spec.title,
    ).stamp(spec_path or None)

    if out.get("witness") == "primal":
        key = ("engine.param.primal_min" if out["sense"] == "min"
               else "engine.param.primal_max")
    else:
        key = "engine.param.proved_min" if out["sense"] == "min" \
            else "engine.param.proved"
    detail = t(key, bound=str(out["bound"]) or "0", floor=floor)
    status, verdict = Status.UNSAT, Verdict.PROVED
    if out.get("claim") is not None:
        c = out["claim"]
        if c["holds"]:
            detail += " -- " + t("engine.param.claim_holds",
                                 relation=c["relation"], target=str(
                                     _poly_text(spec, c["target"])))
        else:
            # The bound is certified; the CLAIM is not shown, and a bound that
            # falls short of what was asked is not the thing that was asked.
            status, verdict = Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE
            detail += " -- " + t("engine.param.claim_not_shown",
                                 relation=c["relation"], target=str(
                                     _poly_text(spec, c["target"])))
    return Result("parametric", status, verdict, ENGINE_PARAM,
                  ms, cert,
                  detail=detail,
                  meta={"bound": str(out["bound"]), "floor": floor,
                        "sense": out["sense"],
                        "columns": len(out["variables"])})


def _parametric_pieces(spec, out, t0, spec_path):
    """One dual per box: a certificate whose pieces tile the box."""
    from ..certificate import parametric_bound_certificate

    ms = (time.perf_counter() - t0) * 1000
    floor = ", ".join("{} in [{}, {}]".format(n, lo, hi)
                      for n, (lo, hi) in out["box"].items())
    if not out["ok"]:
        return Result("parametric", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE_PARAM, ms, None,
                      detail=t("engine.param.pieces_failed",
                               n=len(out["failed_boxes"]),
                               boxes="; ".join(
                                   ", ".join("{} in [{}, {}]".format(k, a, b)
                                             for k, (a, b) in fb.items())
                                   for fb in out["failed_boxes"][:3])),
                      meta={"failed_boxes": out["failed_boxes"]})
    pieces = []
    for b, piece in out["pieces"]:
        pieces.append({
            "box": {n: [str(lo), str(hi)] for n, (lo, hi) in b.items()},
            "dual": _dual_texts(spec, piece),
            "dual_poly": _dual_polys(spec, piece),
            "bound": piece["bound"].serialize(),
            "box_trees": piece.get("box_trees") or {},
            "claim": piece.get("claim"),
        })
    cert = parametric_bound_certificate(
        parameters=dict(spec.parameters), variables=out["variables"],
        objective={v: _ser(spec, c) for v, c in spec.objective.items()},
        constraints=[[str(n), {v: _ser(spec, c) for v, c in row.items()},
                      sense, _ser(spec, rhs)]
                     for n, row, sense, rhs in spec.constraints],
        dual={}, bound=(out["claim"]["target"] if out["claim"] else {}),
        rows=[], title=spec.title, sense=out["sense"],
        free=out.get("free") or None, claim=out.get("claim"),
        box=out["box"], pieces=pieces, split=out["split"],
    ).stamp(spec_path or None)
    if out["claim"]:
        key = ("engine.param.pieces_claim_min" if out["sense"] == "min"
               else "engine.param.pieces_claim")
        detail = t(key, floor=floor, n=len(pieces),
                   target=str(_poly_text(spec, out["claim"]["target"])))
    else:
        detail = t("engine.param.pieces", floor=floor, n=len(pieces))
    return Result("parametric", Status.UNSAT, Verdict.PROVED, ENGINE_PARAM,
                  ms, cert, detail=detail,
                  meta={"pieces": len(pieces), "floor": floor,
                        "sense": out["sense"]})


def _dual_texts(spec, out):
    from ..parametric import dual_text
    from ..polynomials import Poly

    if out.get("found_dual") is not None:
        ring = tuple(spec.parameters)
        return {n: dual_text(Poly.parse(ring, v))
                for n, v in out["found_dual"].items()}
    if not isinstance(spec.dual, dict):
        return {}
    return {str(n): _dual_str(spec, v) for n, v in spec.dual.items()}


def _dual_polys(spec, out):
    if out.get("found_dual") is not None:
        return dict(out["found_dual"])
    if isinstance(spec.dual, dict) and out["polynomial_dual"]:
        return {str(n): _ser(spec, v) for n, v in spec.dual.items()}
    return None


def _poly_text(spec, serialized):
    from ..polynomials import Poly

    return Poly.parse(tuple(spec.parameters), serialized)


def _dual_str(spec, v):
    """The dual entry as a human reads it: a rational, or a polynomial.

    A constant handed over as a bare `Fraction` prints exactly as it always
    has, so certificates from the packing shape are unchanged.
    """
    from ..parametric import dual_text
    from ..polynomials import Poly

    return dual_text(v) if isinstance(v, Poly) else str(v)


def _ser(spec, coef):
    """A coefficient as a serialised Poly over the parameter ring."""
    from ..polynomials import Poly

    ring = tuple(spec.parameters)
    if isinstance(coef, Poly):
        return coef.serialize()
    if isinstance(coef, (int, float)) or hasattr(coef, "numerator"):
        return Poly.const(ring, coef).serialize()
    return Poly.from_z3(coef, ring).serialize()


def eliminate(spec, limits: Limits | None = None,
              spec_path: str = "") -> Result:
    """Get rid of one variable, and say what has to hold without it."""
    from ..linarith import NotPolynomial
    from ..resultants import NotEliminable, eliminate as _elim

    lim = limits or Limits()
    t0 = time.perf_counter()
    variables = tuple(spec.variables)

    if len(spec.equations) != 2:
        return Result("eliminate", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_ELIM, 0.0, None,
                      detail=t("engine.eliminate.two_only",
                               n=len(spec.equations)))
    try:
        f, g = (_poly(e, variables) for e in spec.equations)
    except NotPolynomial as e:
        return Result("eliminate", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_ELIM, 0.0, None,
                      detail=t("engine.ideal.not_polynomial", detail=str(e)))

    try:
        out = _elim(f, g, spec.eliminate)
    except NotEliminable as e:
        return Result("eliminate", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_ELIM, 0.0, None, detail=str(e))
    except Budget as e:
        return Result("eliminate", Status.RESOURCE_EXHAUSTED,
                      Verdict.INCONCLUSIVE, ENGINE_ELIM, 0.0, None,
                      detail=str(e))

    res = out["resultant"]
    ms = (time.perf_counter() - t0) * 1000
    cert = resultant_certificate(
        variables=variables, eliminated=spec.eliminate,
        f=f.serialize(), g=g.serialize(), resultant=res.serialize(),
        A=out["A"].serialize(), B=out["B"].serialize(),
        deg_f=out["deg_f"], deg_g=out["deg_g"],
        lead_f=out["lead_f"].serialize(), lead_g=out["lead_g"].serialize(),
        lead_f_constant=out["lead_f_constant"],
        lead_g_constant=out["lead_g_constant"],
        title=spec.title,
    ).stamp(spec_path or None)

    meta = {"resultant": str(res) or "0",
            "degrees": "{} and {} in {}".format(out["deg_f"], out["deg_g"],
                                                spec.eliminate)}

    # A non-zero CONSTANT resultant is conclusive in the useful direction:
    # no common root, for any values of anything, over any extension field.
    if out["constant"] and res:
        return Result("eliminate", Status.UNSAT, Verdict.REFUTED, ENGINE_ELIM,
                      ms, cert,
                      detail=t("engine.eliminate.never", var=spec.eliminate,
                               value=str(res)),
                      meta=dict(meta, case="no_common_root"))

    if out["identically_zero"]:
        return Result("eliminate", Status.SAT, Verdict.SATISFIABLE,
                      ENGINE_ELIM, ms, cert,
                      detail=t("engine.eliminate.always", var=spec.eliminate),
                      meta=dict(meta, case="common_factor"))

    return Result("eliminate", Status.SAT, Verdict.SATISFIABLE, ENGINE_ELIM,
                  ms, cert,
                  detail=t("engine.eliminate.condition", var=spec.eliminate,
                           res=str(res)),
                  meta=dict(meta, case="condition"))


def ideal(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    from ..linarith import NotPolynomial

    lim = limits or Limits()
    t0 = time.perf_counter()
    variables = tuple(spec.variables)

    try:
        gs = [_poly(e, variables) for e in spec.equations]
        claim = None if spec.claim is None else _poly(spec.claim, variables)
    except NotPolynomial as e:
        return Result("ideal", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_IDEAL, 0.0, None,
                      detail=t("engine.ideal.not_polynomial", detail=str(e)))

    target = claim if claim is not None else Poly.const(variables, 1)
    try:
        hs, in_ideal = cofactors(target, gs, max_pairs=spec.max_pairs)
    except Budget as e:
        return Result("ideal", Status.RESOURCE_EXHAUSTED, Verdict.INCONCLUSIVE,
                      ENGINE_IDEAL, (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.ideal.budget", detail=str(e)))

    ms = (time.perf_counter() - t0) * 1000
    if not in_ideal:
        # Conclusive, not a failure to find: Groebner decides membership.
        detail = (t("engine.ideal.consistent") if claim is None
                  else t("engine.ideal.not_member"))
        return Result("ideal", Status.SAT, Verdict.REFUTED, ENGINE_IDEAL, ms,
                      None, detail=detail)

    cert = ideal_certificate(
        variables=variables,
        equations=[g.serialize() for g in gs],
        claim=None if claim is None else claim.serialize(),
        cofactors=[h.serialize() for h in hs],
        inconsistent=claim is None, title=spec.title,
    ).stamp(spec_path or None)

    used = [str(h) for h in hs if h]
    return Result(
        "ideal", Status.UNSAT, Verdict.PROVED, ENGINE_IDEAL, ms, cert,
        detail=(t("engine.ideal.inconsistent") if claim is None
                else t("engine.ideal.member", n=len(used))),
        meta={"cofactors": {str(i): str(h) for i, h in enumerate(hs) if h},
              "equations": len(gs), "degree": target.degree},
    )


# ---------------------------------------------------------------------------


def sos(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    from .. import sos as sosmod
    from ..linarith import NotPolynomial

    t0 = time.perf_counter()
    variables = tuple(spec.variables)
    try:
        p = _poly(spec.poly, variables)
    except NotPolynomial as e:
        return Result("sos", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_SOS, 0.0, None,
                      detail=t("engine.ideal.not_polynomial", detail=str(e)))

    try:
        found, why = sosmod.certify(
            p, spec.half_degree, spec.iterations,
            time_limit_s=max(1.0, (limits or Limits()).timeout_ms / 1000))
    except sosmod.NoBackend as e:
        return Result("sos", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_SOS, 0.0, None,
                      detail=t("engine.sos.no_backend", detail=str(e)))

    ms = (time.perf_counter() - t0) * 1000
    if found is None:
        # Never REFUTED: not every non-negative polynomial is a sum of squares.
        return Result("sos", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE_SOS, ms, None,
                      detail=t("engine.sos.none", detail=why))

    terms, basis, denom, backend = found
    cert = sos_certificate(
        variables=variables, poly=p.serialize(),
        terms=sosmod.serialize(terms), basis_size=len(basis), denom=denom,
        backend=backend, title=spec.title,
    ).stamp(spec_path or None)
    return Result(
        "sos", Status.UNSAT, Verdict.PROVED, ENGINE_SOS, ms, cert,
        detail=t("engine.sos.found", n=len(terms), denom=denom),
        meta={"squares": ["{} * ({})^2".format(d, q) for d, q in terms],
              "basis_size": len(basis), "denominator": denom,
              "backend": backend},
    )


# ---------------------------------------------------------------------------


def number(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    from .. import numbers

    t0 = time.perf_counter()
    n = int(spec.n)

    if spec.question not in ("prime", "factor"):
        return Result("number", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE_NUM, 0.0, None,
                      detail=t("engine.number.bad_question", got=spec.question))

    if spec.question == "factor":
        tree = numbers.factorisation(n)
        checks = numbers.verify_factorisation(tree)
        ms = (time.perf_counter() - t0) * 1000
        cert = number_certificate("factor", tree, spec.title).stamp(
            spec_path or None)
        factors = " * ".join("{}^{}".format(f["p"], f["e"])
                             for f in tree["factors"]) or "1"
        return Result("number", Status.UNSAT, Verdict.PROVED, ENGINE_NUM, ms,
                      cert, detail=t("engine.number.factored", n=n,
                                     factors=factors),
                      meta={"factors": factors, "checks": len(checks)})

    try:
        tree = numbers.pratt(n)
    except (ValueError, RuntimeError) as e:
        # A composite is a real answer, not a failure to find one.
        return Result("number", Status.SAT, Verdict.REFUTED, ENGINE_NUM,
                      (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.number.composite", n=n, detail=str(e)))

    checks = numbers.verify_pratt(tree)
    ms = (time.perf_counter() - t0) * 1000
    cert = number_certificate("prime", tree, spec.title).stamp(spec_path or None)
    return Result("number", Status.UNSAT, Verdict.PROVED, ENGINE_NUM, ms, cert,
                  detail=t("engine.number.prime", n=n, checks=len(checks)),
                  meta={"witness": tree.get("witness"), "checks": len(checks),
                        "nodes": _nodes(tree), "depth": _depth(tree)})


def _nodes(tree) -> int:
    return 1 + sum(_nodes(f["cert"]) for f in tree.get("factors", []))


def _depth(tree) -> int:
    return 1 + max((_depth(f["cert"]) for f in tree.get("factors", [])),
                   default=0)
