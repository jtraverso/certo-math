"""A `polynomial_nonneg` certificate, read as a list of leaves.

Auditors outside certo rebuilt this format three times: a reader that knew
only one box failed on `[variable, left, right]` splits, another missed the
`ray` multipliers on an open end. Each wrote its own walk of the tree. This
is the walk `verify` makes, exposed -- it reads, it does not check:

    nonneg_leaves(cert) -> {
        "polynomial":  the certified polynomial, serialised (after clearing
                       denominators, when the certificate says so),
        "parameters":  the variables, in the ring's order,
        "box":         {name: [lo, hi]} -- hi None for an open end,
        "region":      {name: polynomial} -- conditions g >= 0 (scope),
        "method":      "bernstein" | "shift" | "point",
        "leaves":      [{"box": {name: [lo, hi]}, "degrees": [...] or None
                         (the polynomial's own), "region": {term: lambda}},
                        ...]                       -- for "bernstein"
        "multipliers": {term: lambda}             -- for "shift"
        "point", "value"                           -- for "point" (refuted)
    }

Every number is the exact text the certificate holds ('3/7'). A leaf's box
is computed by the same halving as `verify`: at the midpoint, or at the
recorded cut `[name, left, right, at]`.
"""
from __future__ import annotations

from fractions import Fraction


def nonneg_leaves(cert) -> dict:
    from .certificate import Certificate

    if isinstance(cert, dict):
        cert = Certificate.from_dict(cert)
    if cert.kind != "polynomial_nonneg":
        raise ValueError("not a polynomial_nonneg certificate: {}".format(cert.kind))
    p = cert.payload
    ring = list(p["parameters"])
    box = {n: [p["box"][n][0], p["box"][n][1]] for n in ring}
    out = {"polynomial": p["poly"], "parameters": ring, "box": box,
           "region": dict(p.get("region") or {})}
    if p.get("cleared"):
        out["cleared"] = p["cleared"]
    if not p.get("holds", True):
        out.update(method="point", point=dict(p.get("point") or {}),
                   value=p.get("value"))
        return out
    if p.get("ray") is not None or any(hi is None for _lo, hi in box.values()):
        out.update(method="shift",
                   multipliers=dict((p.get("ray") or {}).get("multipliers") or {}))
        return out
    leaves = []
    start = {n: (Fraction(lo), Fraction(hi)) for n, (lo, hi) in box.items()}
    stack = [(p.get("tree"), start)]
    while stack:
        tree, b = stack.pop()
        if isinstance(tree, list) and len(tree) in (3, 4):
            name = tree[0]
            lo, hi = b[name]
            at = Fraction(tree[3]) if len(tree) == 4 else (lo + hi) / 2
            left, right = dict(b), dict(b)
            left[name], right[name] = (lo, at), (at, hi)
            # right first, so the leaves come out left to right
            stack.append((tree[2], right))
            stack.append((tree[1], left))
            continue
        leaf = tree if isinstance(tree, dict) else {}
        leaves.append({"box": {n: [_text(lo), _text(hi)] for n, (lo, hi) in b.items()},
                       "degrees": list(leaf["deg"]) if "deg" in leaf else None,
                       "region": dict(leaf.get("region") or {})})
    out.update(method="bernstein", leaves=leaves)
    return out


def _text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else "{}/{}".format(
        x.numerator, x.denominator)
