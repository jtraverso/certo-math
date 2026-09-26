"""A cheap look before paying for a certificate.

Most of certo's time on a hard question goes to the certificate, not to the
answer: an LP is 1.3 ms in floating point and seconds through exact
reconstruction and the check; an integer optimum HiGHS finds in a second took
branch and bound over an hour; the certificate of a stopped search took 190 s
to serialise. While searching for a route, most of those answers are thrown
away -- the bound was not the right one, the constant was off -- and paying
for each certificate first is the wrong order.

`--explore` answers the same question the cheap way, and SAYS SO:

  * the status is `explored` and the verdict `likely` -- never `proved`, and
    the exit code is 2, so a script branching on it treats the answer as
    inconclusive, which it is;
  * no certificate is written, and there is nothing to self-check;
  * a COUNTEREXAMPLE is still certified whenever that is cheap -- a
    parametric claim that fails at a sampled point is re-solved EXACTLY at
    that point, and if it still fails the answer is `refuted` with the exact
    certificate of that instance. A "no" is cheap to certify; the "yes" is
    what costs;
  * `--record FILE` keeps what was asked and what was found, and
    `certo promote FILE` runs it again certified and says whether the two
    agree. Floating point can be wrong near a degenerate optimum or at the
    edge of a tolerance, and that disagreement is exactly what promotion
    reports.

What it does per command:

  opt, mixed   the floating-point LP / MILP value, with no exact route
  parametric   the LP solved in floating point on a grid of the box or ray
               (respecting the region); the claim compared at every point
  sweep        a seeded random sample of the family, not all of it
"""
from __future__ import annotations

import json
import random
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import product
from pathlib import Path

from .i18n import t
from .status import Result, Status, Verdict

EXPLORABLE = ("opt", "mixed", "parametric", "sweep")
ENGINE = "certo/explore"
#: Points a parametric exploration may sample, at most.
MAX_POINTS = 125
#: Items a sweep exploration evaluates, by default.
SAMPLE = 200


def _likely(command, t0, detail, meta):
    meta = dict(meta, explore=True)
    return Result(command, Status.EXPLORED, Verdict.LIKELY, ENGINE,
                  (time.perf_counter() - t0) * 1000, None, detail=detail,
                  meta=meta)


# --- opt, mixed --------------------------------------------------------------


def lp(command, spec, limits=None, target=None):
    """The float value of an LP or MILP, labelled for what it is."""
    from .engines import lp as engine

    t0 = time.perf_counter()
    res = engine.opt(spec, limits, use_exact=False, target=target)
    value = res.meta.get("objective_float")
    if res.status is Status.UNSAT:
        return _likely(command, t0, t("explore.infeasible"),
                       {"answer": "infeasible", "lp_solver": res.meta.get("lp_solver")})
    if value is None:
        return Result(command, res.status, Verdict.INCONCLUSIVE, ENGINE,
                      (time.perf_counter() - t0) * 1000, None,
                      detail=res.detail, meta={"explore": True})
    discrete = bool(res.meta.get("integer"))
    detail = t("explore.lp_integer" if discrete else "explore.lp",
               value="{:.10g}".format(value))
    meta = {"answer": "value", "value": value, "integer": discrete,
            "lp_solver": res.meta.get("lp_solver")}
    if target is not None:
        meets = value >= float(Fraction(str(target))) - 1e-9 * (1 + abs(value))
        meta["meets_target"] = meets
        detail += " " + t("explore.target_meets" if meets
                          else "explore.target_short", target=target)
    return _likely(command, t0, detail, meta)


# --- parametric ----------------------------------------------------------------


def _poly(x, ring):
    from .polynomials import Poly

    if isinstance(x, Poly):
        return x
    if isinstance(x, (int, Fraction)):
        return Poly.const(ring, x)
    return Poly.from_z3(x, ring)


def points(spec, cap=MAX_POINTS):
    """A grid over the box -- or along the ray above the floors -- with the
    region's conditions respected."""
    from .parametric import evaluate

    ring = tuple(spec.parameters)
    d = max(1, len(ring))
    m = 2
    while (m + 1) ** d <= cap and m < 9:
        m += 1
    axes = []
    for n in ring:
        if getattr(spec, "box", None):
            lo, hi = (Fraction(x) for x in spec.box[n])
            axes.append([lo + (hi - lo) * Fraction(k, m - 1) for k in range(m)])
        else:
            lo = Fraction(spec.parameters[n])
            steps = [0, Fraction(1, 2), 1, 2, 5, 10, 20, 50, 100][:m]
            axes.append([lo + s for s in steps])
    region = [_poly(g, ring) for _n, g in (getattr(spec, "region", None) or [])]
    out = []
    for combo in product(*axes):
        p = dict(zip(ring, combo))
        if all(evaluate(g, p) >= 0 for g in region):
            out.append(p)
    return out


def instance(spec, p):
    """The LP of a parametric spec at one parameter point, exactly."""
    from .parametric import evaluate
    from .spec import LPSpec

    ring = tuple(spec.parameters)
    free = {str(v) for v in (getattr(spec, "free", None) or [])}
    lp = LPSpec(sense=getattr(spec, "sense", "max"), title="instance")
    names = sorted({v for _n, row, _s, _r in spec.constraints for v in row}
                   | set(spec.objective))
    for v in names:
        lp.variable(v, None if v in free else 0, None)
    lp.objective({v: evaluate(_poly(c, ring), p)
                  for v, c in spec.objective.items()})
    for name, row, sense, rhs in spec.constraints:
        lp.constraint({v: evaluate(_poly(c, ring), p) for v, c in row.items()},
                      sense, evaluate(_poly(rhs, ring), p), name=str(name))
    return lp


def parametric(spec, limits=None):
    """The claim tested at sampled points. A point where it fails is
    re-solved exactly, and a failure that survives is a certified refutation."""
    from .engines import lp as engine
    from .parametric import evaluate

    t0 = time.perf_counter()
    ring = tuple(spec.parameters)
    minimising = getattr(spec, "sense", "max") == "min"
    claim = getattr(spec, "claim", None)
    T = None if claim is None else _poly(claim, ring)
    pts = points(spec)
    worst, sampled, best = None, 0, None
    for p in pts:
        res = engine.opt(instance(spec, p), limits, use_exact=False)
        v = res.meta.get("objective_float")
        if v is None:
            continue
        sampled += 1
        if best is None or (v > best[0]) != minimising:
            best = (v, p)
        if T is None:
            continue
        tp = float(evaluate(T, p))
        margin = (v - tp) if minimising else (tp - v)
        if worst is None or margin < worst[0]:
            worst = (margin, p, v, tp)
        if margin < -1e-9 * (1 + abs(tp)):
            exact = engine.opt(instance(spec, p), limits)
            if exact.certificate is not None and exact.meta.get("exact"):
                ve = Fraction(exact.meta["objective"])
                te = evaluate(T, p)
                if (ve < te) if minimising else (ve > te):
                    return Result(
                        "parametric", Status.SAT, Verdict.REFUTED, ENGINE,
                        (time.perf_counter() - t0) * 1000, exact.certificate,
                        detail=t("explore.param_refuted", point=_pt(p),
                                 value=str(ve), claim=str(te),
                                 rel=">=" if minimising else "<="),
                        meta={"explore": True, "answer": "refuted",
                              "point": {k: str(x) for k, x in p.items()},
                              "value": str(ve), "claim": str(te)})
    if not sampled:
        return Result("parametric", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE, (time.perf_counter() - t0) * 1000, None,
                      detail=t("explore.param_nothing"), meta={"explore": True})
    meta = {"answer": "sampled", "points": sampled,
            "best": {"value": best[0], "point": {k: str(x) for k, x in best[1].items()}}}
    if T is None:
        return _likely("parametric", t0,
                       t("explore.param_no_claim", n=sampled,
                         value="{:.10g}".format(best[0]), point=_pt(best[1]),
                         word="lowest" if minimising else "highest"), meta)
    meta["worst_margin"] = worst[0]
    meta["worst_point"] = {k: str(x) for k, x in worst[1].items()}
    return _likely("parametric", t0,
                   t("explore.param_held", n=sampled,
                     margin="{:.6g}".format(worst[0]), point=_pt(worst[1])),
                   meta)


def _pt(p):
    return ", ".join("{} = {}".format(k, v) for k, v in p.items())


# --- sweep --------------------------------------------------------------------


def sweep(spec, limits=None, use_geng=True, sample=SAMPLE):
    """A seeded random sample of the family, evaluated -- not all of it."""
    from .limits import Limits
    from .spec import DomainSpec

    t0 = time.perf_counter()
    rng = random.Random((limits or Limits()).seed or 0)
    if isinstance(spec, DomainSpec):
        from .engines.domain import _evaluate

        items = spec.items() if callable(spec.items) else list(spec.items)
        name = spec.id_of
    else:
        from .engines.graphsearch import _evaluate
        from .graphs import enumerate_graphs

        items, _engine, _total = enumerate_graphs(spec.n, spec.filters,
                                                  use_geng=use_geng,
                                                  limits=limits)
        name = (lambda g: g.to_graph6())
    items = list(items)
    chosen = items if len(items) <= sample else rng.sample(items, sample)
    failures, undecided = [], 0
    for it in chosen:
        out = _evaluate(spec, it)
        if out.ok is False:
            failures.append(name(it))
        elif out.ok is None:
            undecided += 1
    meta = {"answer": "sampled", "family": len(items), "sampled": len(chosen),
            "failures": failures[:20], "undecided": undecided}
    key = "explore.sweep_failed" if failures else "explore.sweep_held"
    return _likely("sweep", t0,
                   t(key, n=len(chosen), total=len(items), k=len(failures),
                     first=failures[0] if failures else "-",
                     undecided=undecided), meta)


# --- the record, and promotion --------------------------------------------------


def record(res, argv, spec_path=None) -> dict:
    """What was asked and what was found: NOT a certificate. `verify` refuses
    it; `certo promote` runs it again, certified."""
    import hashlib

    from . import __version__

    rec = {"kind": "exploration", "command": argv[0] if argv else res.command,
           "argv": list(argv), "verdict": res.verdict.value,
           "status": res.status.value, "detail": res.detail,
           "answer": {k: v for k, v in res.meta.items()
                      if k not in ("explore",)},
           "certo_version": __version__,
           "created": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    if spec_path and Path(spec_path).exists():
        rec["spec_path"] = str(Path(spec_path).resolve())
        rec["spec_sha256"] = hashlib.sha256(Path(spec_path).read_bytes()).hexdigest()
    return rec


def without_explore(argv) -> list:
    """The command line with `--explore` and `--record FILE` taken out."""
    out, skip = [], False
    for a in argv:
        if skip:
            skip = False
            continue
        if a == "--explore":
            continue
        if a == "--record":
            skip = True
            continue
        if a.startswith("--record="):
            continue
        out.append(a)
    return out


def agreement(rec, res) -> tuple:
    """`(agrees, explained)`: does the certified run say what the exploration
    did? `None` when the two answers are not comparable."""
    ans = rec.get("answer") or {}
    kind = ans.get("answer")
    if kind == "value" and res.meta.get("objective") is not None:
        got = float(Fraction(str(res.meta.get("objective"))))
        if ans.get("integer") and res.meta.get("achieved") is not None:
            got = float(Fraction(str(res.meta["achieved"])))
        v = float(ans["value"])
        ok = abs(got - v) <= 1e-6 * (1 + abs(got))
        return ok, t("explore.promote_value", explored="{:.10g}".format(v),
                     certified=str(res.meta.get("objective")))
    if kind == "infeasible":
        ok = res.verdict is Verdict.UNSATISFIABLE
        return ok, t("explore.promote_infeasible")
    if kind == "refuted":
        return res.verdict is not Verdict.PROVED, t("explore.promote_refuted")
    if kind == "sampled":
        failures = ans.get("failures") or []
        if rec.get("command") == "sweep":
            ok = (res.verdict is Verdict.REFUTED) == bool(failures)
        else:
            ok = res.verdict is Verdict.PROVED
        return ok, t("explore.promote_sampled", verdict=res.verdict.value)
    return None, ""


def load_record(path):
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if data.get("kind") != "exploration":
        raise ValueError(t("explore.not_a_record", path=str(path)))
    return data
