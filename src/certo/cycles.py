"""A parameter that depends on itself, and the loop that cannot close.

The most expensive shape in a real session: a parameter derived from `delta`
reappears in a condition on `delta`. It is invisible until you already suspect
it, and the way people find it is by building a substitute for the growth by
hand until a solver can see it -- which proves something strictly weaker than
what they meant.

    k    >= tower(1/delta)          the regularity lemma's bound
    rho  <= K / (3 k**2)            what the crude count leaves
    delta <= rho                    Chebyshev

Nothing in those three lines mentions a cycle, and there is one:
`delta -> k -> rho -> delta`. Composing the bounds gives
`delta <= K/(3 tower(1/delta)**2)`, and the right-hand side vanishes faster
than any power of delta, so no positive delta survives.

WHAT IS CHECKED, and it is finite. The chain is walked once, each edge
composing a magnitude CLASS rather than a function (see `growth`), and the
closing constraint is a comparison of two classes. No search, no solver, and
the certificate is the chain with its classes and the one comparison that
fails.

MONOTONICITY IS TRACKED, not assumed. A lower bound pushed through a
decreasing function becomes an UPPER bound: `k >= tower(1/delta)` with
`rho <= K/(3k**2)` gives an upper bound on rho precisely because the second
map decreases. Get that backwards and a live regime is declared empty, which
is the one direction of error this must not make -- so an edge whose available
side does not support the direction needed is REFUSED by name rather than
composed anyway.

WHAT IT DOES NOT ESTABLISH. That the growth classes you declared are the real
ones. A tower is a tower because the lemma says so; certo checks what follows
from that, the way `reduce` checks what follows from a group you supply. And
`EMPTY` is only ever reported on a STRICT comparison: anything else comes back
"not established by this route", never "no cycle".
"""
from __future__ import annotations

from fractions import Fraction

from . import growth as g
from .i18n import t as _t

UPPER, LOWER, EXACT = "upper", "lower", "exact"


class NotCyclic(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


def _edge_fields(e, i):
    try:
        src, dst = str(e["from"]), str(e["to"])
        rel = e.get("rel", ">=")
        fn = e.get("fn", "poly")
        degree = Fraction(e.get("degree", 1))
        of = e.get("of", "value")
    except (KeyError, TypeError) as exc:
        raise NotCyclic(_t("cycle.bad_edge", i=i, why=str(exc)))
    if rel not in (">=", "<="):
        raise NotCyclic(_t("cycle.bad_relation", rel=rel, i=i))
    if of not in ("value", "reciprocal"):
        raise NotCyclic(_t("cycle.bad_of", of=of, i=i))
    return src, dst, rel, fn, degree, of


def _increasing(fn, degree, of) -> bool:
    """Does the edge's map increase in its source?"""
    base = True if fn in ("exp", "tower") else degree > 0
    return not base if of == "reciprocal" else base


def walk(spec) -> dict:
    """Propagate classes along the chain, tracking which side each bound is."""
    param = str(getattr(spec, "parameter", "") or "")
    if not param:
        raise NotCyclic(_t("cycle.no_parameter"))

    edges = list(getattr(spec, "edges", None) or [])
    if not edges:
        raise NotCyclic(_t("cycle.no_edges"))

    # The parameter IS the scale: delta = u^-1, exactly, by construction.
    cls = {param: g.Class(g.POLY, -1)}
    side = {param: EXACT}
    steps = []

    for i, raw in enumerate(edges):
        src, dst, rel, fn, degree, of = _edge_fields(raw, i)
        if src not in cls:
            raise NotCyclic(_t("cycle.unreached", name=src, i=i,
                               known=", ".join(sorted(cls))))
        if dst in cls:
            raise NotCyclic(_t("cycle.revisited", name=dst, i=i))

        up = _increasing(fn, degree, of)
        # To bound `dst` on the side `rel` gives, the source must be bounded on
        # the side the map carries there.
        need = (LOWER if up else UPPER) if rel == ">=" else \
               (UPPER if up else LOWER)
        have = side[src]
        if have != EXACT and have != need:
            raise NotCyclic(_t("cycle.wrong_side", src=src, dst=dst,
                               need=need, have=have, i=i))

        arg = g.invert(cls[src]) if of == "reciprocal" else cls[src]
        out = g.apply(fn, arg, degree)
        cls[dst] = out
        side[dst] = LOWER if rel == ">=" else UPPER
        steps.append({"from": src, "to": dst, "rel": rel, "fn": fn,
                      "degree": str(degree), "of": of,
                      "source_class": cls[src].to_dict(),
                      "class": out.to_dict(), "side": side[dst]})

    return {"parameter": param, "classes": cls, "side": side, "steps": steps}


def certify(spec) -> dict:
    """Walk the chain, close the loop, and say what the comparison gives."""
    state = walk(spec)
    closes = getattr(spec, "closes", None)
    if not closes or len(closes) != 3:
        raise NotCyclic(_t("cycle.no_closes"))

    left, rel, right = str(closes[0]), str(closes[1]), str(closes[2])
    if rel not in ("<=", ">="):
        raise NotCyclic(_t("cycle.bad_relation", rel=rel, i="closes"))
    for name in (left, right):
        if name not in state["classes"]:
            raise NotCyclic(_t("cycle.unreached", name=name, i="closes",
                               known=", ".join(sorted(state["classes"]))))

    a, b = state["classes"][left], state["classes"][right]
    cmp = g.compare(a, b)

    # `left <= right` is refuted when left STRICTLY dominates, and the bounds
    # have to point the right way for that to follow: an upper bound on the
    # left and a lower bound on the right would not.
    if rel == "<=":
        contradicts = cmp > 0
        need = (state["side"][left] in (EXACT, LOWER)
                and state["side"][right] in (EXACT, UPPER))
    else:
        contradicts = cmp < 0
        need = (state["side"][left] in (EXACT, UPPER)
                and state["side"][right] in (EXACT, LOWER))

    empty = bool(contradicts and need)
    return {
        "parameter": state["parameter"],
        # The chain, then back to where it started: that IS the cycle, and
        # printing the far end twice made it read like a self-loop.
        "cycle": [state["parameter"]] + [s["to"] for s in state["steps"]]
                 + [state["parameter"]],
        "steps": state["steps"],
        "closes": {"left": left, "rel": rel, "right": right,
                   "left_class": a.to_dict(), "right_class": b.to_dict(),
                   "left_side": state["side"][left],
                   "right_side": state["side"][right],
                   "comparison": cmp},
        "empty": empty,
        # Never "there is no cycle": only that this route did not settle it.
        "why": None if empty else ("not_strict" if not contradicts
                                   else "bounds_point_the_wrong_way"),
        "classes": {k: v.to_dict() for k, v in state["classes"].items()},
        "title": getattr(spec, "title", ""),
    }


def check(payload) -> dict:
    """Redo every composition and the final comparison, from the steps alone."""
    cls = g.Class(g.POLY, -1)
    seen = {payload["parameter"]: cls}
    bad = []
    for step in payload["steps"]:
        src = seen.get(step["from"])
        if src is None or src.to_dict() != step["source_class"]:
            bad.append(step["to"])
            src = g.Class.from_dict(step["source_class"])
        arg = g.invert(src) if step["of"] == "reciprocal" else src
        out = g.apply(step["fn"], arg, Fraction(step["degree"]))
        if out.to_dict() != step["class"]:
            bad.append(step["to"])
        seen[step["to"]] = out

    c = payload["closes"]
    a = g.Class.from_dict(c["left_class"])
    b = g.Class.from_dict(c["right_class"])
    cmp = g.compare(a, b)
    # The two sides compared ARE what the steps derived for them. Read from
    # `closes` alone, the comparison could be between any two classes, and
    # the steps -- emptied, even -- decided nothing.
    left, right = seen.get(c.get("left")), seen.get(c.get("right"))
    tied = (left is not None and right is not None
            and left.to_dict() == c["left_class"]
            and right.to_dict() == c["right_class"])
    return {"steps_ok": not bad, "bad": sorted(set(bad)), "tied": tied,
            "comparison_ok": cmp == c["comparison"],
            "comparison": cmp,
            "empty_ok": payload["empty"] == bool(
                (cmp > 0 if c["rel"] == "<=" else cmp < 0)
                and payload["empty"])}
