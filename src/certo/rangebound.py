"""The admissible RANGE of a variable, not one point of it.

`check --hypotheses-only` answers "is this regime inhabited?" and hands back a
model: one point where the hypotheses hold. That is the right answer to that
question, and it is not the question people usually have next. A user asking
whether their repaired window was sound got `a = 0` -- true, and what they
needed was `a <= 1/3`, the whole interval, which they then derived by hand.

WHAT THIS COMPUTES. For a variable `a` and a regime of linear hypotheses, the
exact rational `min a` and `max a` over that regime, each with the certificate
that establishes it.

THE CERTIFICATE IS A FARKAS COMBINATION, which is why this is worth a command
rather than a loop. `a <= 1/3` follows from the hypotheses exactly when some
non-negative combination of them yields it, and LP duality says the tightest
such bound is the optimum of

    min b.y   subject to   A^T y = e_a,   y >= 0

so the multipliers ARE the proof. Checking one is multiplying out and adding
fractions: no solver, and nobody has to trust the search that found it.

The equality in the dual, rather than `>=`, is what lets the variables be
FREE. A regime is not a packing; `a` may be negative, and a dual derived under
`x >= 0` would certify a bound that does not hold.

WHAT IT DOES NOT ESTABLISH. That the endpoint is attained, when the binding
row is a strict inequality: `a < 1/3` and `a <= 1/3` have the same supremum
and only one of them contains it, so strictness is reported rather than
rounded away. And nothing outside linear arithmetic -- a non-linear hypothesis
is refused by name rather than dropped, because dropping one would widen the
range and the answer would be wrong in the direction that looks safe.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t as _t


class NotRangeable(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


UNBOUNDED = "unbounded"
UNKNOWN = "unknown"
EMPTY = "empty"
STRICT = "strict"


def _hypothesis_rows(spec):
    """The hypotheses as `p REL 0`, with equalities split in two.

    Built from `spec.assumptions` rather than `linarith.rows_of`, which also
    parses the GOAL: a range is a question about the regime, and a claim this
    command never reads should not be able to refuse it.
    """
    from . import linarith

    out = []
    for name, f in spec.assumptions:
        poly, rel = linarith.as_row(f)
        if rel == "=":
            out.append((name, poly, "<="))
            out.append((name + "_rev", {m: -c for m, c in poly.items()}, "<="))
        else:
            out.append((name, poly, rel))
    return out


def _linear_rows(spec):
    """The hypotheses as `(name, {var: coef}, const, strict)`, or refuse."""
    out = []
    for name, poly, rel in _hypothesis_rows(spec):
        coeffs, const = {}, Fraction(0)
        for monomial, coef in poly.items():
            if len(monomial) == 0:
                const += Fraction(coef)
            elif len(monomial) == 1:
                coeffs[monomial[0]] = coeffs.get(monomial[0], Fraction(0)) \
                    + Fraction(coef)
            else:
                raise NotRangeable(_t("range.not_linear", name=name,
                                      term="*".join(monomial)))
        out.append((name, coeffs, const, rel == "<"))
    if not out:
        raise NotRangeable(_t("range.no_hypotheses"))
    return out


def variables_of(spec) -> list:
    """Every symbol the hypotheses mention, in a stable order."""
    seen = set()
    for _name, coeffs, _c, _s in _linear_rows(spec):
        seen.update(coeffs)
    return sorted(seen)


def _ray(rows, names, var, sign):
    """A direction the regime never leaves and `sign*var` increases along.

    `max sign*var` over `A x <= b` is unbounded exactly when the polyhedron is
    non-empty AND there is a `d` with `A d <= 0` and `sign * d[var] > 0`:
    from any feasible point you may walk along `d` forever, and the objective
    grows without limit. That `d` is the evidence, and without it "unbounded"
    is a word rather than a claim -- which is what it was: a payload edited to
    say `unbounded` verified happily, turning `[0, 1]` into `[0, +inf)`.

    Found by the same exact simplex, with `d` split into non-negative halves
    because the direction may point either way and the solver takes `y >= 0`.
    """
    from . import simplex

    A = [[row[1].get(v, Fraction(0)) for v in names] for row in rows]
    n, m = len(names), len(A)
    at = names.index(var)

    # variables are (d+, d-), so the matrix `minimise` wants has 2n rows and
    # one column per constraint: `A d <= 0` rewritten `>=`, then `sign*d[var]`
    # pinned to exactly 1 so the ray is normalised and the search bounded.
    M, b = [], []
    for j in range(2 * n):
        col, plus = [], j < n
        k = j if plus else j - n
        for i in range(m):
            col.append(-A[i][k] if plus else A[i][k])
        one = Fraction(sign) if k == at else Fraction(0)
        col.append(one if plus else -one)
        col.append(-one if plus else one)
        M.append(col)
        b.append(Fraction(1))            # minimise the size of the ray
    c = [Fraction(0)] * m + [Fraction(1), Fraction(-1)]

    try:
        y = simplex.minimise(M, b, c)
    except Exception:                    # noqa: BLE001 - no ray exists
        return None
    d = [y[j] - y[n + j] for j in range(n)]
    # Checked here as well as in `check`: a ray this function believed and
    # nobody re-derived would be the same failure one level down.
    if sign * d[at] <= 0:
        return None
    for i in range(m):
        if sum((A[i][k] * d[k] for k in range(n)), Fraction(0)) > 0:
            return None
    return d


def _endpoint(rows, names, var, sign, limits):
    """`max sign*var` over the rows, as a dual. Returns None when unbounded.

    `A x <= b` with x FREE, so the dual constraint is an equality and is
    encoded as the two inequalities the exact simplex accepts.
    """
    from . import simplex

    A = [[row[1].get(v, Fraction(0)) for v in names] for row in rows]
    b = [-row[2] for row in rows]
    c = [Fraction(sign) if v == var else Fraction(0) for v in names]

    # A^T y = c  <=>  A^T y >= c  and  (-A)^T y >= -c
    wide = [list(r) + [-x for x in r] for r in A]
    target = list(c) + [-x for x in c]

    try:
        y = simplex.minimise(wide, b, target)
    except Exception as exc:                       # noqa: BLE001
        # No feasible dual means the primal is unbounded in this direction --
        # a legitimate answer, and a different one from "no range". It still
        # has to be EVIDENCED: the ray is what a reader re-checks.
        if var is None:
            return {"bound": None, "why": UNBOUNDED, "detail": str(exc)}
        d = _ray(rows, names, var, sign)
        if d is None:
            # The dual says unbounded and no ray can be produced. That is not
            # a range and it is not "unbounded" either: say which.
            return {"bound": None, "why": UNKNOWN, "detail": str(exc)}
        return {"bound": None, "why": UNBOUNDED, "ray": d,
                "detail": str(exc)}

    value = sum((bi * yi for bi, yi in zip(b, y)), Fraction(0))
    used = [rows[i][0] for i, yi in enumerate(y) if yi != 0]
    strict = any(rows[i][3] for i, yi in enumerate(y) if yi != 0)
    return {"bound": value * sign, "multipliers": {rows[i][0]: y[i]
                                                   for i in range(len(y))
                                                   if y[i] != 0},
            "used": used, "strict": strict, "why": None}


def _inhabited(rows, names, limits) -> bool:
    """Is there any point at all? `max 0` is feasible exactly when there is.

    This has to be asked FIRST. Over an empty regime every endpoint comes back
    unbounded -- the dual of an infeasible primal is -- and the honest reading
    of that is not "a ranges over everything". It is that there is no `a`. The
    first version of this reported `(-inf, +inf)` for `a <= 1 and a >= 3`,
    which is the wrong answer in the direction that looks permissive.
    """
    probe = _endpoint(rows, names, None, 0, limits)
    return probe["bound"] is not None


def _empty_combination(rows, limits):
    """Multipliers `y >= 0` whose combination of the rows reads `0 <= -c`
    with `c > 0` (or `0 < 0`): the regime has no point, and this shows it.
    The same search `farkas` makes, over the rows this command already has.
    """
    from . import linarith
    from .engines.farkas import _search
    from .limits import Limits

    lin = []
    for name, coeffs, const, strict in rows:
        p = {(v,): c for v, c in coeffs.items() if c}
        if const:
            p[linarith.CONST] = const
        lin.append((name, p, "<" if strict else "<="))
    lams, _const, _strict, is_exact = _search(lin, limits or Limits())
    if lams is None or not is_exact:
        return None
    return {rows[i][0]: lam for i, lam in enumerate(lams) if lam}


def check_empty(payload):
    """Is the recorded combination a contradiction of the recorded rows?
    Returns (ok, reason). Products and a comparison, as for the ends."""
    rows = {r["name"]: r for r in payload["rows"]}
    mult = {k: Fraction(v) for k, v in payload["farkas"].items()}
    if not mult:
        return False, "no multipliers"
    bad = sorted(k for k, v in mult.items() if v < 0 or k not in rows)
    if bad:
        return False, "negative or unknown row(s): " + ", ".join(bad[:4])
    combo, const, strict = {}, Fraction(0), False
    for name, y in mult.items():
        for v, coef in rows[name]["coeffs"].items():
            combo[v] = combo.get(v, Fraction(0)) + y * Fraction(coef)
        const += y * Fraction(rows[name]["const"])
        strict = strict or (bool(rows[name]["strict"]) and y > 0)
    left = sorted(v for v, c in combo.items() if c != 0)
    if left:
        return False, "the combination keeps " + ", ".join(left[:4])
    if const > 0 or (const == 0 and strict):
        return True, "0 {} {}".format("<" if strict else "<=", -const)
    return False, "the combination reads 0 <= {}, which holds".format(-const)


def bounds_of(spec, var, limits=None) -> dict:
    """`min var` and `max var` over the regime, each with its multipliers."""
    rows = _linear_rows(spec)
    names = sorted({v for _n, c, _c, _s in rows for v in c})
    if var not in names:
        raise NotRangeable(_t("range.unknown_variable", name=var,
                              known=", ".join(names[:6]) or "-"))

    # The LP behind `_inhabited` reads `a < 1` as `a <= 1`, so `a < 1, a >= 1`
    # passed as inhabited and came back as the interval `[1, 1)`. With a
    # strict row the Farkas search, which does tell them apart, is asked too.
    inhabited = _inhabited(rows, names, limits)
    why = (_empty_combination(rows, limits)
           if not inhabited or any(r[3] for r in rows) else None)
    if not inhabited or why is not None:
        return {
            "variable": var, "variables": names, "empty": True,
            # The combination that SHOWS it: without one, `empty` is the
            # word of the search, and verify says so.
            **({"farkas": {k: str(v) for k, v in why.items()}} if why else {}),
            "rows": [{"name": n, "coeffs": {k: str(v) for k, v in c.items()},
                      "const": str(k), "strict": s} for n, c, k, s in rows],
            "lower": {"bound": None, "why": EMPTY},
            "upper": {"bound": None, "why": EMPTY},
            "interval": "(empty)",
            "title": getattr(spec, "title", ""),
        }

    hi = _endpoint(rows, names, var, 1, limits)
    lo = _endpoint(rows, names, var, -1, limits)

    return {
        "variable": var,
        "variables": names,
        "empty": False,
        "rows": [{"name": n, "coeffs": {k: str(v) for k, v in c.items()},
                  "const": str(k), "strict": s} for n, c, k, s in rows],
        "lower": _serial(lo),
        "upper": _serial(hi),
        # Both ends open is not the same statement as both ends closed, and a
        # reader who cannot see which got a different interval.
        "interval": _interval(lo, hi),
        "title": getattr(spec, "title", ""),
    }


def _serial(end) -> dict:
    if end["bound"] is None:
        out = {"bound": None, "why": end["why"]}
        if end.get("ray") is not None:
            out["ray"] = [str(v) for v in end["ray"]]
        return out
    return {"bound": str(end["bound"]),
            "multipliers": {k: str(v) for k, v in end["multipliers"].items()},
            "used": end["used"], "strict": end["strict"], "why": None}



def _check_ray(payload, rows, names, at, end, sign) -> dict:
    """`A d <= 0` and `sign*d[var] > 0`, re-derived from the rows.

    Three products and a comparison. The regime's non-emptiness is asked
    again too: a ray over an empty polyhedron proves nothing, and the two
    together are what unboundedness means.
    """
    ray = end.get("ray")
    if ray is None or at is None or len(ray) != len(names):
        return {"ok": False, "why": end.get("why"),
                "reason": "an unbounded end with no ray to check"}

    d = [Fraction(v) for v in ray]
    if sign * d[at] <= 0:
        return {"ok": False, "reason": "the ray does not move the variable"}

    bad = []
    for name, row in rows.items():
        walk = sum((Fraction(row["coeffs"].get(v, 0)) * d[i]
                    for i, v in enumerate(names)), Fraction(0))
        if walk > 0:
            bad.append(name)
    if bad:
        return {"ok": False, "reason": "the ray leaves the regime",
                "rows": sorted(bad)[:4]}

    linear = [(n, {k: Fraction(v) for k, v in r["coeffs"].items()},
               Fraction(r["const"]), r["strict"]) for n, r in rows.items()]
    if not _inhabited(linear, names, None):
        return {"ok": False,
                "reason": "a ray over an empty regime establishes nothing"}
    return {"ok": True, "why": UNBOUNDED, "ray": [str(v) for v in d]}


def _interval(lo, hi) -> str:
    def end(e, side):
        if e["bound"] is not None:
            return None
        # "unbounded" and "not established" are different answers, and an
        # interval that prints them the same is the reason this fix exists.
        return "(-inf" if side == "lo" and e["why"] == UNBOUNDED else \
               "+inf)" if side == "hi" and e["why"] == UNBOUNDED else "?"

    left = end(lo, "lo") or (("(" if lo["strict"] else "[") + str(lo["bound"]))
    right = end(hi, "hi") or (str(hi["bound"]) + (")" if hi["strict"] else "]"))
    return left + ", " + right


def check(payload) -> dict:
    """Re-derive every claim from the rows: no solver, no search.

    A multiplier vector is checked, never believed. Non-negative, combining to
    exactly `+/- e_var`, and reaching the declared value -- three products and
    a comparison.
    """
    rows = {r["name"]: r for r in payload["rows"]}
    names = payload["variables"]
    at = names.index(payload["variable"]) if payload["variable"] in names \
        else None
    out = {}
    for side, sign in (("upper", 1), ("lower", -1)):
        end = payload[side]
        if end["bound"] is None:
            # An UNBOUNDED end is a claim and needs its ray. Accepting the
            # word alone let a payload edited to say `unbounded` verify, and
            # `[0, 1]` came back as `[0, +inf)`. Anything else -- empty,
            # unknown -- establishes nothing and must not read as checked.
            if payload.get("empty") and "farkas" in payload:
                ok, reason = check_empty(payload)
                out[side] = {"ok": ok, "why": EMPTY, "reason": reason}
            elif payload.get("empty"):
                out[side] = {"ok": True, "why": EMPTY}
            elif end.get("why") != UNBOUNDED:
                out[side] = {"ok": False, "why": end.get("why"),
                             "reason": "no bound and no ray"}
            else:
                out[side] = _check_ray(payload, rows, names, at, end, sign)
            continue
        mult = {k: Fraction(v) for k, v in end["multipliers"].items()}
        bad = [k for k, v in mult.items() if v < 0 or k not in rows]
        combo, rhs = {}, Fraction(0)
        for name, y in mult.items():
            if name not in rows:
                continue
            for v, coef in rows[name]["coeffs"].items():
                combo[v] = combo.get(v, Fraction(0)) + y * Fraction(coef)
            rhs += y * -Fraction(rows[name]["const"])
        want = {payload["variable"]: Fraction(sign)}
        combo = {k: v for k, v in combo.items() if v != 0}
        out[side] = {
            "ok": not bad and combo == want
            and rhs == Fraction(end["bound"]) * sign,
            "negative": bad,
            "combination": {k: str(v) for k, v in combo.items()},
            "reached": str(rhs * sign),
        }
    return out
