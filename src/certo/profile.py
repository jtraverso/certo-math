"""How an optimum responds to ONE capacity, as a certified function.

    f(t) = max { c.x : A x <= b, x >= 0, load of the named row <= t }

WHAT THIS IS, AND WHY IT IS NOT `parametric`. `certo parametric` certifies a
bound for a whole FAMILY, where the parameter sits in the data -- `A(p)`,
`b(p)`, `c(p)` polynomial -- and the answer is an inequality. Here the
parameter is ONE CAPACITY and the answer is a FUNCTION: concave, piecewise
affine, with breakpoints. Different question, different certificate.

A user on a chordal-graph route asked for exactly this and wrote one by hand:

    f_e(t) = min{6 + 3t, 7 + t},   0 <= t <= 1

with a dual per branch and primal sources at t = 0, 1/2 and 1. The profile
answers a question a single optimum cannot: what incompatibility survives when
only a FRACTION of the shared resource is available. `D = f(1) - something` is
one value of it; the shape near zero is what decides whether an obstruction
amplifies when the piece is repeated.

WHY FINITE DATA PROVES A STATEMENT ABOUT A CONTINUUM. This is the whole
argument and it is worth stating rather than assuming:

  * A DUAL BOUNDS THE WHOLE SEGMENT AT ONCE. Feasibility of `y` is
    `A^T y >= c`, which does not mention `b` -- so `f(t) <= y.b(t)` holds for
    EVERY `t`, not just the one it was found at. Writing `b(t)` out, that
    bound is the affine function `alpha + beta t` with `alpha` the cost on the
    other rows and `beta` the price of the parametrised one.

  * TWO SOURCES ATTAIN THE WHOLE SEGMENT. If `x0` is feasible at `t_i` with
    value `alpha + beta t_i`, and `x1` at `t_{i+1}` with value
    `alpha + beta t_{i+1}`, then `(1-s) x0 + s x1` is feasible at
    `(1-s) t_i + s t_{i+1}` -- loads are linear, the other capacities are
    constant -- and its value is `alpha + beta t`. So equality holds along the
    segment from its two ends.

  * AND THE SEGMENTS TILE THE DOMAIN. Sorted breakpoints starting at `lo`,
    ending at `hi`, each consecutive pair sharing an endpoint where the two
    bounds agree with the source there.

Those three together DECIDE `f` on `[lo, hi]`. Not bound it: decide it. It is
the first certificate here whose subject is a function rather than a number.

WHAT IS CHECKED AND WHAT IS SUPPLIED. Everything is checked; nothing stated is
believed. The breakpoints, the duals and the sources are INPUT -- finding them
is parametric programming and belongs to whatever solver you like. `alpha`,
`beta` and every value are recomputed here from the columns, never read back.

WHAT IT DOES NOT ESTABLISH. That the profile is the optimum of some OTHER
program, that the columns are all the columns, or that the rows mean what
their names suggest. A profile certified over a column set is a statement
about that column set. If the columns came from a graph, that translation is
a separate obligation and this does not discharge it.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t as _t


class NotAProfile(ValueError):
    """The input is not a capacity profile this can read."""


def _q(value, what):
    try:
        return Fraction(str(value))
    except (TypeError, ValueError, ZeroDivisionError):
        raise NotAProfile(_t("profile.not_rational", what=what,
                             value=repr(value))) from None


def _read(spec) -> dict:
    cols = dict(getattr(spec, "columns", None) or {})
    if not cols:
        raise NotAProfile(_t("profile.no_columns"))
    gain = dict(getattr(spec, "gain", None) or {})
    cap = dict(getattr(spec, "capacity", None) or {})
    param = str(getattr(spec, "parameter", "") or "")
    if not param:
        raise NotAProfile(_t("profile.no_parameter"))

    columns, rows = {}, set()
    for name, usage in cols.items():
        u = {}
        for row, coeff in dict(usage or {}).items():
            u[str(row)] = _q(coeff, "{}[{}]".format(name, row))
            rows.add(str(row))
        columns[str(name)] = u
    rows.add(param)

    missing = sorted(n for n in columns if n not in gain)
    if missing:
        raise NotAProfile(_t("profile.no_gain",
                             names=", ".join(missing[:3])))
    gains = {str(n): _q(v, "gain[{}]".format(n)) for n, v in gain.items()}

    # The parametrised row has no fixed capacity: `t` is its capacity, and a
    # number supplied for it would be a second, silent answer.
    if param in cap:
        raise NotAProfile(_t("profile.parameter_has_capacity", row=param))
    caps = {str(r): _q(v, "capacity[{}]".format(r)) for r, v in cap.items()}
    unbounded = sorted(r for r in rows if r != param and r not in caps)
    if unbounded:
        raise NotAProfile(_t("profile.no_capacity",
                             names=", ".join(unbounded[:3])))
    return {"columns": columns, "gain": gains, "capacity": caps,
            "parameter": param, "rows": sorted(rows)}


def dual_bound(data, y) -> tuple:
    """`(alpha, beta)` for the affine bound `f(t) <= alpha + beta t`.

    `alpha` is the dual's cost on the fixed capacities and `beta` is the price
    of the parametrised row. Recomputed from the prices every time: a stored
    pair is a pair anybody can edit.
    """
    p = data["parameter"]
    alpha = sum((y.get(r, Fraction(0)) * c
                 for r, c in data["capacity"].items()), Fraction(0))
    return alpha, y.get(p, Fraction(0))


def dual_violations(data, y) -> list:
    """Columns the dual does NOT cover, and by how much. Empty means feasible.

    `A^T y >= c`, column by column. This is the only place `t` is absent from
    the reasoning, which is exactly why the bound holds for every `t`.
    """
    bad = []
    for name, usage in sorted(data["columns"].items()):
        priced = sum((y.get(r, Fraction(0)) * a for r, a in usage.items()),
                     Fraction(0))
        if priced < data["gain"][name]:
            bad.append({"column": name, "priced": str(priced),
                        "gain": str(data["gain"][name]),
                        "short_by": str(data["gain"][name] - priced)})
    return bad


def source_report(data, x, t) -> dict:
    """Feasibility and value of one primal at capacity `t`."""
    p = data["parameter"]
    negative = sorted(n for n, m in x.items() if m < 0)
    unknown = sorted(n for n in x if n not in data["columns"])
    load = {}
    for name, mass in x.items():
        for row, a in data["columns"].get(name, {}).items():
            load[row] = load.get(row, Fraction(0)) + mass * a
    over = []
    for row, used in sorted(load.items()):
        limit = t if row == p else data["capacity"].get(row)
        if limit is not None and used > limit:
            over.append({"row": row, "load": str(used), "limit": str(limit)})
    value = sum((mass * data["gain"].get(name, Fraction(0))
                 for name, mass in x.items()), Fraction(0))
    return {"value": value, "over": over, "negative": negative,
            "unknown": unknown,
            "load": {r: str(v) for r, v in sorted(load.items())},
            "parameter_load": str(load.get(p, Fraction(0)))}


# --- finding one, rather than checking one ---------------------------------

#: How many linear programs the search may solve before giving up. Exceeding
#: it is reported, never rounded into a shorter profile.
MAX_SOLVES = 400


class Undiscovered(RuntimeError):
    """The search stopped before it had the whole profile."""


def _matrix(data, order, rows):
    """`A` with one ROW per constraint and one column per program column."""
    return [[data["columns"][n].get(r, Fraction(0)) for n in order]
            for r in rows]


def _rhs(data, rows, t):
    p = data["parameter"]
    return [t if r == p else data["capacity"][r] for r in rows]


def _solve_at(data, order, rows, t):
    """The exact optimal dual at capacity `t`, and the line it gives.

    `simplex.minimise` takes the primal data and returns that primal's DUAL,
    which is precisely what a segment needs: its feasibility is `A^T y >= c`,
    so the line `alpha + beta t` it defines bounds EVERY `t` at once, not only
    the one it was found at.
    """
    from .simplex import minimise

    y = minimise(_matrix(data, order, rows), _rhs(data, rows, t),
                 [data["gain"][n] for n in order])
    priced = {r: Fraction(v) for r, v in zip(rows, y)}
    alpha, beta = dual_bound(data, priced)
    return priced, alpha, beta


def _primal_at(data, order, rows, t):
    """A FEASIBLE optimal primal at capacity `t`, exactly.

    The primal is the optimal dual OF THE DUAL, and `simplex.minimise` returns
    a primal's dual, so the dual is handed to it written as a maximisation:

        min b.y  s.t.  A^T y >= c        becomes
        max (-b).y  s.t.  (-A^T) y <= -c

    and what comes back is `x`. The signs are checked against an instance with
    a known answer in the tests rather than argued here, because this module's
    own neighbour says it plainly: passing the transpose around invites
    getting it the wrong way round once.

    `exact.primal_from_dual` was the obvious first choice and is the wrong
    tool: it solves the complementary-slackness system, which pins a candidate
    without requiring `x >= 0`, and on the first real profile it returned
    primals with negative masses. The checker refused them, which is the
    design working -- but a search that proposes infeasible sources never
    certifies anything.
    """
    At = [[data["columns"][n].get(r, Fraction(0)) for r in rows]
          for n in order]
    A2 = [[-v for v in row] for row in At]
    b2 = [-data["gain"][n] for n in order]
    c2 = [-v for v in _rhs(data, rows, t)]

    from .simplex import minimise

    return [Fraction(v) for v in minimise(A2, b2, c2)]


def _cross(l1, l2):
    """Where two lines meet, or None when they are parallel."""
    (a1, b1), (a2, b2) = l1, l2
    if b1 == b2:
        return None
    return (a2 - a1) / (b1 - b2)


def discover(spec, max_solves=MAX_SOLVES) -> dict:
    """Find the profile instead of checking one. Exactly, and without sampling.

    `f(t)` is the minimum, over dual-feasible `y`, of `alpha_y + beta_y t`, so
    it is the LOWER ENVELOPE of a finite family of lines, and every line comes
    from one linear program. That turns discovery into a question with a
    termination argument rather than a grid:

      * solve at both ends; two lines come back;
      * if they are the same line, the profile is affine there and it is done;
      * otherwise the lines cross at some `t*`. Solve there. If the value
        equals the crossing, `t*` IS a breakpoint and both sides are settled;
      * if the value is strictly BELOW the crossing, a third piece lives in
        between, and the same question is asked on each half.

    Each step either settles a segment or exhibits a new piece, and a finite
    program has finitely many pieces. No step samples a grid, and no step
    guesses where a breakpoint might be: it is computed from two lines meeting.

    NOTHING HERE IS TRUSTED. What comes back is a PROPOSAL -- breakpoints,
    duals, sources -- and `certify` admits or refuses it on exactly the same
    terms as one written by hand. A search with a bug in it cannot produce a
    wrong certificate, only a refused one. That is why this half could be
    built after the checking half instead of before it.
    """
    data = _read(spec)
    lo, hi = getattr(spec, "domain", None) or (0, 1)
    lo, hi = _q(lo, "domain.lo"), _q(hi, "domain.hi")
    if lo >= hi:
        raise NotAProfile(_t("profile.empty_domain", lo=str(lo), hi=str(hi)))

    order = sorted(data["columns"])
    rows = sorted(set(data["capacity"]) | {data["parameter"]})
    solved = {}

    def at(t):
        if t not in solved:
            if len(solved) >= max_solves:
                raise Undiscovered(_t("profile.budget", n=max_solves))
            solved[t] = _solve_at(data, order, rows, t)
        return solved[t]

    breaks = set()

    def refine(t1, t2, depth=0):
        if depth > 64:
            raise Undiscovered(_t("profile.too_deep"))
        _y1, a1, b1 = at(t1)
        _y2, a2, b2 = at(t2)
        if (a1, b1) == (a2, b2):
            return                               # one line covers [t1, t2]
        star = _cross((a1, b1), (a2, b2))
        if star is None or not (t1 < star < t2):
            # Two different lines that do not meet inside the interval: this
            # pair cannot see the piece between them. Split and ask again
            # rather than inventing a breakpoint.
            mid = (t1 + t2) / 2
            if mid <= t1 or mid >= t2:
                return
            breaks.add(mid)
            refine(t1, mid, depth + 1)
            refine(mid, t2, depth + 1)
            return
        _ys, astar, bstar = at(star)
        if astar + bstar * star == a1 + b1 * star:
            breaks.add(star)                     # the two lines meet ON f
            return
        breaks.add(star)                         # strictly below: a new piece
        refine(t1, star, depth + 1)
        refine(star, t2, depth + 1)

    refine(lo, hi)
    points = sorted({lo, hi} | breaks)

    # One segment per consecutive pair, priced by the dual at its MIDPOINT --
    # the interior of a piece, where exactly one line attains the envelope. At
    # a breakpoint two do, and either would be a different segment.
    segments = []
    for a, b in zip(points, points[1:]):
        y, _al, _be = at((a + b) / 2)
        segments.append({"from": str(a), "to": str(b),
                         "dual": {r: str(v) for r, v in sorted(y.items())
                                  if v != 0}})

    # And one source per breakpoint, from an exact solve of the primal at
    # that capacity. Feasibility is the whole job of a source, so it is solved
    # for rather than reconstructed.
    sources = {}
    for t in points:
        x = _primal_at(data, order, rows, t)
        if x is None or len(x) != len(order):
            raise Undiscovered(_t("profile.no_source_found", t=str(t)))
        sources[str(t)] = {n: str(v) for n, v in zip(order, x) if v != 0}

    return {"segments": segments, "sources": sources,
            "breakpoints": [str(v) for v in points],
            "solves": len(solved)}


def certify(spec) -> dict:
    """Check a proposed profile end to end. Every number recomputed."""
    data = _read(spec)
    lo, hi = getattr(spec, "domain", None) or (0, 1)
    lo, hi = _q(lo, "domain.lo"), _q(hi, "domain.hi")
    if lo >= hi:
        raise NotAProfile(_t("profile.empty_domain", lo=str(lo), hi=str(hi)))

    raw_segments = list(getattr(spec, "segments", None) or [])
    if not raw_segments:
        raise NotAProfile(_t("profile.no_segments"))
    raw_sources = dict(getattr(spec, "sources", None) or {})
    if not raw_sources:
        raise NotAProfile(_t("profile.no_sources"))

    sources = {}
    for key, cols in raw_sources.items():
        at = _q(key, "sources key")
        sources[at] = {str(n): _q(m, "source[{}][{}]".format(key, n))
                       for n, m in dict(cols or {}).items()}

    # --- the segments, each with its dual, in the order given --------------
    segments, failures = [], []
    for i, seg in enumerate(raw_segments):
        s = dict(seg or {})
        a = _q(s.get("from", lo), "segment {} from".format(i))
        b = _q(s.get("to", hi), "segment {} to".format(i))
        if a >= b:
            raise NotAProfile(_t("profile.empty_segment", i=i,
                                 a=str(a), b=str(b)))
        y = {str(r): _q(v, "segment {} dual[{}]".format(i, r))
             for r, v in dict(s.get("dual") or {}).items()}
        negative = sorted(r for r, v in y.items() if v < 0)
        bad = dual_violations(data, y)
        alpha, beta = dual_bound(data, y)
        if negative:
            failures.append({"segment": i, "why": "negative_price",
                             "rows": negative})
        if bad:
            failures.append({"segment": i, "why": "dual_infeasible",
                             "columns": bad[:4]})
        segments.append({
            "from": str(a), "to": str(b),
            "dual": {r: str(v) for r, v in sorted(y.items())},
            "alpha": str(alpha), "beta": str(beta),
            "at_from": str(alpha + beta * a),
            "at_to": str(alpha + beta * b),
            "_a": a, "_b": b, "_alpha": alpha, "_beta": beta,
        })

    # --- coverage: the segments must tile [lo, hi] with no gap -------------
    ordered = sorted(segments, key=lambda s: s["_a"])
    gaps = []
    if ordered[0]["_a"] != lo:
        gaps.append({"where": "start", "expected": str(lo),
                     "got": str(ordered[0]["_a"])})
    if ordered[-1]["_b"] != hi:
        gaps.append({"where": "end", "expected": str(hi),
                     "got": str(ordered[-1]["_b"])})
    for left, right in zip(ordered, ordered[1:]):
        if left["_b"] != right["_a"]:
            gaps.append({"where": "between", "expected": str(left["_b"]),
                         "got": str(right["_a"])})
    if gaps:
        failures.append({"why": "not_covered", "gaps": gaps[:4]})

    # --- the sources, and the agreement that turns a bound into a value ----
    breaks = sorted({s["_a"] for s in ordered} | {s["_b"] for s in ordered})
    reported, disagree, missing = {}, [], []
    for at in breaks:
        if at not in sources:
            missing.append(str(at))
            continue
        rep = source_report(data, sources[at], at)
        entry = {"at": str(at), "value": str(rep["value"]),
                 "parameter_load": rep["parameter_load"],
                 "mass": {n: str(m) for n, m in sorted(sources[at].items())}}
        if rep["negative"] or rep["unknown"] or rep["over"]:
            entry["infeasible"] = {"negative": rep["negative"],
                                   "unknown": rep["unknown"],
                                   "over": rep["over"][:3]}
            failures.append({"why": "source_infeasible", "at": str(at),
                             "detail": entry["infeasible"]})
        # THE STEP THAT MAKES IT AN EQUALITY. A dual alone bounds; a source
        # alone attains something. They have to meet at every breakpoint of
        # every segment touching it, or the profile is two unrelated facts.
        for s in ordered:
            if s["_a"] == at or s["_b"] == at:
                want = s["_alpha"] + s["_beta"] * at
                if want != rep["value"]:
                    disagree.append({"at": str(at), "bound": str(want),
                                     "source": str(rep["value"])})
        reported[str(at)] = entry
    if missing:
        failures.append({"why": "no_source_at", "at": missing[:4]})
    if disagree:
        failures.append({"why": "bound_and_source_disagree",
                         "where": disagree[:4]})

    # --- concavity, which the LP guarantees and a typo does not ------------
    #
    # Concave means the slopes are NON-INCREASING: more capacity is worth less
    # once the cheap uses are taken. The first version of this compared them
    # the other way round and flagged the correct instance -- a profile of
    # slopes 3 then 1 -- as a failure. Caught by running it against a real
    # profile rather than by reading it.
    slopes = [s["_beta"] for s in ordered]
    if any(b > a for a, b in zip(slopes, slopes[1:])):
        failures.append({"why": "not_concave",
                         "slopes": [str(v) for v in slopes]})

    for s in segments:
        for k in ("_a", "_b", "_alpha", "_beta"):
            s.pop(k, None)

    pieces = [{"from": s["from"], "to": s["to"],
               "value": "{} + {} t".format(s["alpha"], s["beta"])}
              for s in sorted(segments, key=lambda s: Fraction(s["from"]))]
    return {
        "parameter": data["parameter"],
        "domain": {"lo": str(lo), "hi": str(hi)},
        "columns": {n: {r: str(a) for r, a in sorted(u.items())}
                    for n, u in sorted(data["columns"].items())},
        "gain": {n: str(v) for n, v in sorted(data["gain"].items())},
        "capacity": {r: str(v) for r, v in sorted(data["capacity"].items())},
        "segments": sorted(segments, key=lambda s: Fraction(s["from"])),
        "breakpoints": [str(v) for v in breaks],
        "sources": reported,
        "piecewise": pieces,
        "holds": not failures,
        "failures": failures,
        # `at_lo` and `at_hi` used to sit here as conveniences. They duplicate
        # `sources[lo]["value"]` and `sources[hi]["value"]`, nothing
        # recomputed them, and the adversarial suite found that editing either
        # changed no check. A field nobody recomputes is a field anybody can
        # edit, so they are gone rather than excused.
        "title": getattr(spec, "title", ""),
    }
