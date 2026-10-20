"""A conditioned covering: a box cut into leaves, and on every leaf a reason.

The statement: on the closed box `domain`, wherever every CONDITION
`g_j >= 0` holds (the physical domain, the hypotheses, a selector), at least
one OBLIGATION `p_i > 0` (or `>= 0`) holds. A user certified each leaf's
sign separately and kept the tree, the exclusions and the exhaustiveness in
code of their own -- 2 283 leaves in one session; this is that, native.

Each leaf carries ONE reason, recomputed by `verify` from Bernstein
coefficients on the leaf, exactly:

    obligation   every coefficient of p_i is > 0 (>= 0 for a `>=` one):
                 p_i keeps its sign on the whole closed leaf, boundary
                 included
    excluded     every coefficient of some g_j is < 0: no point of the leaf
                 satisfies the conditions, so nothing there is owed
    unresolved   neither, at the depth allowed: said, never hidden

and the leaves TILE the domain: each inside it, interiors pairwise disjoint,
volumes summing to the domain's. Closed boxes with those three properties
cover every point -- a point outside their union would have a neighbourhood
outside it too, of positive volume. A point where every condition holds and
every obligation fails is a counterexample, evaluated exactly.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t


class NotACovering(ValueError):
    """Raised with what is wrong with the spec."""


def _volume(box) -> Fraction:
    v = Fraction(1)
    for lo, hi in box.values():
        v *= hi - lo
    return v


def _text(box):
    return {n: [str(lo), str(hi)] for n, (lo, hi) in box.items()}


def _box(raw, ring):
    out = {}
    for n in ring:
        if n not in raw:
            raise NotACovering(t("covering.box_missing", name=n))
        lo, hi = raw[n]
        if lo is None or hi is None:
            raise NotACovering(t("covering.unbounded", name=n))
        out[n] = (Fraction(lo), Fraction(hi))
        if out[n][1] <= out[n][0]:
            raise NotACovering(t("covering.empty_side", name=n))
    return out


def _coeffs(poly, box):
    from . import bernstein

    return bernstein.coefficients(poly, box, bernstein.degrees_of(poly)).values()


def holds(poly, rel, box) -> bool:
    """`poly rel 0` on the whole closed box, by its Bernstein coefficients."""
    cs = list(_coeffs(poly, box))
    return all(c > 0 for c in cs) if rel == ">" else all(c >= 0 for c in cs)


def excludes(g, box) -> bool:
    """`g < 0` on the whole closed box: no point of it satisfies `g >= 0`."""
    return all(c < 0 for c in _coeffs(g, box))


def reason(box, obligations, conditions, hint=None):
    """`(by, name)` for one leaf: the first reason that holds."""
    order = list(obligations)
    if hint is not None:
        order.sort(key=lambda o: o[0] != hint)
    for name, g in conditions:
        if excludes(g, box):
            return "excluded", name
    for name, rel, p in order:
        if holds(p, rel, box):
            return "obligation", name
    return "unresolved", None


def _halves(box, name):
    lo, hi = box[name]
    mid = (lo + hi) / 2
    left, right = dict(box), dict(box)
    left[name] = (lo, mid)
    right[name] = (mid, hi)
    return left, right


def cut_at(domain, cuts):
    """The domain cut at the declared values, variable by variable: the
    starting boxes. A value outside its interval is refused by name."""
    from itertools import product

    axes = []
    for name in domain:
        lo, hi = domain[name]
        vals = sorted({Fraction(str(v)) for v in (cuts or {}).get(name, [])})
        bad = [v for v in vals if not (lo < v < hi)]
        if bad:
            raise NotACovering(t("covering.cut_outside", name=name, value=str(bad[0]),
                                 lo=str(lo), hi=str(hi)))
        ends = [lo] + vals + [hi]
        axes.append([(ends[i], ends[i + 1]) for i in range(len(ends) - 1)])
    unknown = sorted(set(cuts or {}) - set(domain))
    if unknown:
        raise NotACovering(t("covering.cut_unknown", names=", ".join(unknown)))
    return [dict(zip(domain, iv)) for iv in product(*axes)]


def build(domain, obligations, conditions, depth, roots=None, deadline_check=None):
    """The leaves: each root (the domain, or the boxes supplied) cut in half
    along its widest side until a reason holds or `depth` runs out."""
    leaves = []

    def go(box, d, last):
        if deadline_check is not None:
            deadline_check()
        by, name = reason(box, obligations, conditions, hint=last)
        if by != "unresolved" or d <= 0:
            leaves.append({"box": box, "by": by, "name": name})
            return
        widest = max(box, key=lambda n: (box[n][1] - box[n][0], n))
        left, right = _halves(box, widest)
        go(left, d - 1, name or last)
        go(right, d - 1, name or last)

    for root in (roots or [domain]):
        go(root, depth, None)
    return leaves


def tiles(domain, boxes) -> tuple:
    """`(ok, why)`: the boxes are inside the domain, interiors pairwise
    disjoint, and their volumes add up to the domain's."""
    for b in boxes:
        for n, (lo, hi) in b.items():
            dlo, dhi = domain[n]
            if not (dlo <= lo < hi <= dhi):
                return False, t("covering.outside", box=str(_text(b)))
    if sum((_volume(b) for b in boxes), Fraction(0)) != _volume(domain):
        return False, t("covering.volume")
    names = sorted(domain)
    first = names[0]
    order = sorted(range(len(boxes)), key=lambda i: boxes[i][first][0])
    active = []
    for i in order:
        b = boxes[i]
        lo = b[first][0]
        active = [j for j in active if boxes[j][first][1] > lo]
        for j in active:
            c = boxes[j]
            if all(max(b[n][0], c[n][0]) < min(b[n][1], c[n][1]) for n in names):
                return False, t("covering.overlap", a=str(_text(b)), b=str(_text(c)))
        active.append(i)
    return True, ""


def counterexample(leaves, obligations, conditions):
    """A corner or centre of an unresolved leaf where every condition holds
    and every obligation fails -- exactly evaluated -- or None."""
    from itertools import product

    from .parametric import evaluate

    for leaf in leaves:
        if leaf["by"] != "unresolved":
            continue
        box = leaf["box"]
        names = sorted(box)
        pts = [{n: (box[n][0] + box[n][1]) / 2 for n in names}]
        pts += [dict(zip(names, c)) for c in product(*[box[n] for n in names])]
        for pt in pts:
            if any(evaluate(g, pt) < 0 for _n, g in conditions):
                continue
            fails = all((evaluate(p, pt) <= 0) if rel == ">" else (evaluate(p, pt) < 0)
                        for _n, rel, p in obligations)
            if fails:
                return pt
    return None
