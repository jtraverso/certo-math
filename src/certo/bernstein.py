"""Non-negativity on a BOX, by Bernstein coefficients -- and a dual found in
that basis.

    p(x) >= 0 on  [lo_1, hi_1] x ... x [lo_m, hi_m]

is implied by every Bernstein coefficient of `p` on the box being >= 0: the
Bernstein basis polynomials are non-negative on the unit box and sum to one,
so `p` is a convex combination of its coefficients at every point. It is
sufficient and not necessary -- exactly like the shift test `parametric`
already uses on a ray `p >= p0`, which is what the box replaces when both
ends are known.

WHY THIS AND NOT A REPARAMETRISATION. A user proving bounds on boxes wrote
`p = lo + h t/(1+t)` by hand so that the shift test on `t >= 0` would stand in
for Bernstein positivity, then computed the coefficients in Python, then an
LP per control point, then assembled the primal. Here the box is declared and
the coefficients are computed exactly; when they are not all non-negative
the box can be SUBDIVIDED, and the certificate records where it was split, so
the verifier recomputes the coefficients of every leaf rather than trusting
any of them.

THE DUAL, FOUND IN THE SAME BASIS. A dual entry `y_i(p)` of degree `k` per
parameter is written by its Bernstein coefficients. The residuals'
coefficients are then LINEAR in those -- the product of two Bernstein
expansions has an exact closed form -- so asking for all of them to be >= 0
is one linear program, solved and certified exactly by `opt`. What comes out
is a polynomial dual, and it is checked by the same coefficient signs as a
dual somebody brought.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb


class NotABox(ValueError):
    """The box cannot be read."""


def parse_box(box, ring):
    out = {}
    for name in ring:
        if name not in box:
            raise NotABox("box has no interval for {}".format(name))
        lo, hi = box[name]
        lo, hi = Fraction(lo), Fraction(hi)
        if not lo < hi:
            raise NotABox("box interval for {} is empty: [{}, {}]".format(
                name, lo, hi))
        out[name] = (lo, hi)
    extra = set(box) - set(ring)
    if extra:
        raise NotABox("box names what is not a parameter: {}".format(
            ", ".join(sorted(extra))))
    return out


def _unit(poly, box):
    """`poly` in coordinates `t_i in [0,1]`, `p_i = lo_i + w_i t_i`: a dict
    exponent -> coefficient."""
    terms = dict(poly.terms)
    for k, name in enumerate(poly.vars):
        lo, hi = box[name]
        w = hi - lo
        out = {}
        for e, c in terms.items():
            power = e[k]
            for j in range(power + 1):
                mono = list(e)
                mono[k] = j
                add = c * comb(power, j) * lo ** (power - j) * w ** j
                key = tuple(mono)
                out[key] = out.get(key, Fraction(0)) + add
        terms = {e: c for e, c in out.items() if c}
    return terms


def degrees_of(poly):
    m = len(poly.vars)
    return tuple(max((e[i] for e in poly.terms), default=0) for i in range(m))


def coefficients(poly, box, degrees=None):
    """Every Bernstein coefficient of `poly` on `box`, at `degrees` per
    parameter (default: the polynomial's own), as {multi-index: Fraction}."""
    m = len(poly.vars)
    d = tuple(degrees) if degrees is not None else degrees_of(poly)
    own = degrees_of(poly)
    if any(a < b for a, b in zip(d, own)):
        raise ValueError("Bernstein degree below the polynomial's")
    a = _unit(poly, box)
    # One axis at a time: b_k = sum_{j<=k} C(k,j)/C(d,j) a_j.
    grid = {}
    for idx in product(*(range(di + 1) for di in d)):
        grid[idx] = a.get(idx, Fraction(0))
    for axis in range(m):
        da = d[axis]
        if da == 0:
            continue
        new = {}
        for idx in grid:
            k = idx[axis]
            s = Fraction(0)
            for j in range(k + 1):
                src = idx[:axis] + (j,) + idx[axis + 1:]
                v = grid[src]
                if v:
                    s += v * Fraction(comb(k, j), comb(da, j))
            new[idx] = s
        grid = new
    return grid


def _corners(d):
    return [tuple(c) for c in product(*((0, di) for di in d))]


def halves(box, name):
    lo, hi = box[name]
    mid = (lo + hi) / 2
    left, right = dict(box), dict(box)
    left[name] = (lo, mid)
    right[name] = (mid, hi)
    return left, right


def _leaf_degrees(poly, degrees):
    own = degrees_of(poly)
    if degrees is None:
        return own
    return tuple(max(a, b) for a, b in zip(own, degrees))


def nonneg(poly, box, depth=0, degrees=None):
    """`(ok, tree)`. A leaf is None -- the polynomial's own degree -- or
    `{"deg": [...]}` when a higher degree was asked for (a dual found in this
    basis is non-negative at the degree it was found at, which can be above
    the residual's own, where the coefficients are looser). A split is
    `[name, left, right]` at the midpoint of `name`. A negative CORNER
    coefficient is the polynomial's value at a vertex, so it ends the search:
    no subdivision makes a polynomial non-negative where it is negative."""
    if not poly.terms:
        return True, None
    d = _leaf_degrees(poly, degrees)
    b = coefficients(poly, box, d)
    leaf = None if d == degrees_of(poly) else {"deg": list(d)}
    if all(v >= 0 for v in b.values()):
        return True, leaf
    if any(b[c] < 0 for c in _corners(d)) or depth <= 0:
        return False, None
    # Split the widest interval among the parameters the polynomial uses.
    own = degrees_of(poly)
    used = [n for i, n in enumerate(poly.vars) if own[i] > 0] or list(poly.vars)
    name = max(used, key=lambda n: (box[n][1] - box[n][0], -used.index(n)))
    left, right = halves(box, name)
    ok_l, tl = nonneg(poly, left, depth - 1, degrees)
    if not ok_l:
        return False, None
    ok_r, tr = nonneg(poly, right, depth - 1, degrees)
    if not ok_r:
        return False, None
    return True, [name, tl, tr]


def check(poly, box, tree, max_depth=64):
    """Recompute what `nonneg` claimed: every leaf's coefficients >= 0."""
    if not poly.terms:
        return True
    if tree is None or isinstance(tree, dict):
        try:
            d = (degrees_of(poly) if tree is None
                 else tuple(int(x) for x in tree["deg"]))
            return all(v >= 0 for v in coefficients(poly, box, d).values())
        except (KeyError, TypeError, ValueError):
            return False
    if max_depth <= 0 or not isinstance(tree, list) or len(tree) != 3:
        return False
    name, tl, tr = tree
    if name not in box:
        return False
    left, right = halves(box, name)
    return (check(poly, left, tl, max_depth - 1)
            and check(poly, right, tr, max_depth - 1))


# --- the dual, found in the Bernstein basis --------------------------------


def basis_poly(ring, box, degrees, alpha):
    """`B_alpha` on the box as a polynomial in the parameters, exactly."""
    from .polynomials import Poly

    out = Poly.const(ring, 1)
    for k, name in enumerate(ring):
        lo, hi = box[name]
        w = hi - lo
        t = (Poly.var(ring, name) - Poly.const(ring, lo)).scaled(1 / w)
        one_minus = Poly.const(ring, 1) - t
        d, a = degrees[k], alpha[k]
        factor = Poly.const(ring, comb(d, a))
        for _ in range(a):
            factor = factor * t
        for _ in range(d - a):
            factor = factor * one_minus
        out = out * factor
    return out


def from_coefficients(ring, box, degrees, coeffs):
    """The polynomial whose Bernstein coefficients these are."""
    from .polynomials import Poly

    out = Poly(ring)
    for alpha, c in coeffs.items():
        if c:
            out = out + basis_poly(ring, box, degrees, alpha).scaled(c)
    return out


def product_map(a_coeffs, da, k):
    """Coefficients of `A * y` at degree `da + k`, as a linear map of `y`'s
    coefficients at degree `k`: {gamma: {alpha: weight}}."""
    D = tuple(x + y for x, y in zip(da, k))
    out = {}
    for beta, av in a_coeffs.items():
        if not av:
            continue
        for alpha in product(*(range(ki + 1) for ki in k)):
            gamma = tuple(b + a for b, a in zip(beta, alpha))
            w = av
            for i in range(len(D)):
                w = w * Fraction(comb(da[i], beta[i]) * comb(k[i], alpha[i]),
                                 comb(D[i], gamma[i]))
            row = out.setdefault(gamma, {})
            row[alpha] = row.get(alpha, Fraction(0)) + w
    return out
