"""A bound that holds for EVERY value of a parameter, not for the ones you tried.

This is the thing certo has kept saying it cannot do. A sweep checks
`p = 5..12`; a user then writes "and similarly for larger p", and that sentence
is where the work actually is.

For a linear program whose data are POLYNOMIALS in the parameters,

    max c(p).x   subject to   A(p) x <= b(p),  x >= 0

weak duality is available symbolically. Any `y >= 0` with `A(p)^T y >= c(p)`
gives `opt(p) <= b(p).y`, for every `p` at once. So a certificate that the
optimum is bounded by `B(p) = b(p).y` on `p >= p0` needs three things, and
none of them is a solver:

  1. `y >= 0` -- rational constants, compared.
  2. `A(p)^T y - c(p) >= 0` for every column, for all `p >= p0` -- a finite
     set of polynomial inequalities in the parameters.
  3. `B(p) = b(p).y`, expanded.

Only (2) is interesting, and it is handled by a SHIFT. Substitute
`p = p0 + u` with `u >= 0`: if every coefficient of the shifted polynomial is
non-negative, the polynomial is non-negative on the whole ray, because `u` and
all its powers are. Checking that is reading signs off a list.

The shift is SUFFICIENT AND NOT NECESSARY, and this file says so rather than
implying otherwise. `p^2 - 3p + 3` is positive everywhere and shifts to
`(3, -3, 1)` at `p0 = 0`; the test fails and the fact holds. When that happens
the answer is "not certified by this route", never "false" -- and the shifted
coefficients are reported so the next step is obvious.

WHERE THE DUAL COMES FROM is deliberately not this file's problem. Solve one
instance with `opt`, read the dual, and hand it over. That division is the
point: finding a `y` is search and can be as numeric as it likes; checking one
is arithmetic. It is the same split as `farkas`, one level up -- there the
multipliers are constants, here they are constants attached to a family.

TWO SHAPES, NOT ONE. The above is the packing shape: maximise, `<=` rows, and
a bound from above. Symmetrised COVER programs are the other half of the same
duality and turn up at least as often --

    min w(p).z   subject to   M z >= 1,  z >= 0

-- where the useful certificate is a feasible PACKING `y >= 0` with
`M^T y <= w(p)`, giving `opt(p) >= 1.y` for every `p` at once. Same three
checks with the residual's sign flipped, so `sense="min"` with `>=` rows is
accepted and the claim it certifies is a bound from BELOW.

A COVER PROGRAM'S DUAL IS NOT CONSTANT. In the packing shape the multipliers
are pure numbers, because they are rates. In the cover shape the dual is a
packing, and a packing of a growing object grows with it: `d(d-1)/2` triangles
on a neighbourhood of size `d`. So a dual entry may itself be a polynomial in
the parameters, and then `y >= 0` stops being a comparison and becomes the
same shift test as everything else. Both are allowed, and a constant is just
the degree-zero case.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

from .i18n import t as _t
from .polynomials import Poly


class NotParametric(ValueError):
    """Raised with the reason, because a bare failure helps nobody."""


def shift(poly: Poly, offsets: dict) -> Poly:
    """Substitute `v -> v + offset` for each named variable, exactly.

    One variable at a time, expanding `v^k` binomially. The result lives in
    the same ring, where the variable now means the DISTANCE above the offset.
    """
    out = poly
    for name, off in offsets.items():
        off = Fraction(off)
        if not off:
            continue
        if name not in out.vars:
            raise NotParametric(_t("param.unknown", name=name,
                                   names=", ".join(out.vars)))
        k = out.vars.index(name)
        # One dict for the whole substitution. Adding a one-term Poly per
        # binomial term copied the accumulated sum each time -- quadratic in
        # the number of terms, and most of what a large verification cost.
        acc = {}
        powers = [Fraction(1)]
        for e, coef in out.terms.items():
            power = e[k]
            while len(powers) <= power:
                powers.append(powers[-1] * off)
            for j in range(power + 1):
                mono = e[:k] + (j,) + e[k + 1:]
                acc[mono] = acc.get(mono, 0) + coef * comb(power, j) * powers[power - j]
        out = Poly._exact(out.vars, {e: Fraction(c) for e, c in acc.items() if c})
    return out


def nonneg_on_ray(poly: Poly, lows: dict):
    """Is `poly >= 0` everywhere at or above `lows`? Returns (ok, shifted).

    Sufficient, not necessary: every coefficient non-negative after the shift
    means the polynomial is a non-negative combination of products of
    non-negative quantities. A negative coefficient decides nothing, and the
    caller is told exactly that.
    """
    shifted = shift(poly, lows)
    return all(c >= 0 for c in shifted.terms.values()), shifted


def region_terms(region, lows):
    """The declared side conditions, shifted, with their pairwise products.

    A product of non-negative quantities is non-negative, so the products are
    DERIVED and not assumed -- the same step `nlinarith` takes, and the reason
    a region of two conditions can cut out a curved face rather than a corner.
    """
    base = [(str(n), shift(g, lows)) for n, g in region]
    out = list(base)
    for i, (n1, g1) in enumerate(base):
        for n2, g2 in base[i:]:
            out.append(("{}*{}".format(n1, n2), g1 * g2))
    return out


def _monomial_multiples(terms, ring, budget):
    """`u^a * g` for every shifted monomial that fits inside `budget`.

    The multiplier of a side condition is not in general a NUMBER. A residual
    like `r (d - r + 1) / 2` needs `r / 2` times the condition `d - r + 1 >= 0`,
    and after the shift `r` is a floor plus a distance, both non-negative. So
    the multipliers are polynomials with non-negative coefficients, which is
    the same linear program with more columns rather than a different method.
    """
    from itertools import product as _product

    out = []
    for name, g in terms:
        room = budget - g.degree
        if room < 0:
            continue
        for e in _product(range(room + 1), repeat=len(ring)):
            if sum(e) > room:
                continue
            if not any(e):
                out.append((name, g))
                continue
            mono = Poly(ring, {tuple(e): Fraction(1)})
            label = "*".join(v for v, k in zip(ring, e) for _ in range(k))
            out.append(("{}*{}".format(label, name), mono * g))
    return out


def nonneg_on_region(poly: Poly, lows: dict, terms):
    """Is `poly >= 0` on the box, GIVEN the declared side conditions?

    Returns `(ok, shifted, multipliers, remainder)`. The certificate is

        poly  =  sum_k lambda_k g_k  +  remainder,   lambda_k >= 0

    with every coefficient of the shifted `remainder` non-negative, so the
    whole right-hand side is non-negative wherever the `g_k` are. Finding the
    multipliers is a linear program in `lambda` -- the coefficients of the
    remainder are linear in it -- which is why the search lives here: it was
    already an LP, the same reason `farkas` finds its own multipliers.

    With no side conditions this is exactly `nonneg_on_ray`, because the only
    non-negative `lambda` is the empty one.
    """
    from .simplex import SimplexLimit, minimise

    shifted = shift(poly, lows)
    if all(c >= 0 for c in shifted.terms.values()):
        return True, shifted, {}, shifted
    if not terms:
        return False, shifted, {}, shifted

    columns = _monomial_multiples(terms, poly.vars, shifted.degree)
    if not columns:
        return False, shifted, {}, shifted

    monomials = sorted(set(shifted.terms) | {m for _, g in columns
                                             for m in g.terms})
    # `min sum(lambda)` subject to `shifted[m] - sum_k lambda_k g_k[m] >= 0`.
    A = [[-g.terms.get(m, Fraction(0)) for m in monomials] for _, g in columns]
    c = [-shifted.terms.get(m, Fraction(0)) for m in monomials]
    try:
        lam = minimise(A, [Fraction(1)] * len(columns), c)
    except SimplexLimit:
        return False, shifted, {}, shifted

    remainder = shifted
    used = {}
    for (name, g), value in zip(columns, lam):
        if value:
            used[name] = used.get(name, Fraction(0)) + value
            remainder = remainder - g.scaled(value)
    ok = all(v >= 0 for v in used.values()) and \
        all(co >= 0 for co in remainder.terms.values())
    return ok, shifted, used, remainder


# ---------------------------------------------------------------------------


def dual_text(poly) -> str:
    """How a dual entry reads. One function, so the two copies cannot drift.

    `dual` is what somebody opening the file sees and `dual_poly` is what the
    verifier recomputes from; they are checked against each other, and that
    check is only meaningful if both sides agree on what the text should be.
    """
    if not poly.terms:
        return "0"
    if len(poly.terms) == 1 and not any(next(iter(poly.terms))):
        return str(next(iter(poly.terms.values())))
    return str(poly)


def certify(spec) -> dict:
    """The three checks, and everything the certificate needs to repeat them.

    `spec.constraints` are `(name, {var: coef}, sense, rhs)` with every
    coefficient a polynomial in the parameters, `sense` being `"<="` for a
    maximisation and `">="` for a minimisation; `spec.dual` is one rational --
    or one polynomial -- per constraint name.
    """
    params = tuple(spec.parameters)
    ring = params
    minimising = getattr(spec, "sense", "max") == "min"

    def P(x):
        if isinstance(x, Poly):
            if x.vars != ring:
                raise NotParametric(_t("param.wrong_ring",
                                       got=", ".join(x.vars),
                                       want=", ".join(ring)))
            return x
        if isinstance(x, (int, Fraction)):
            return Poly.const(ring, x)
        return Poly.from_z3(x, ring)

    free = {str(v) for v in (getattr(spec, "free", None) or [])}
    claim = getattr(spec, "claim", None)

    # THE BOX, when there is one: Bernstein coefficients decide every
    # non-negativity below, in place of the shift test on a ray.
    box = _box_of(spec, ring)
    depth = int(getattr(spec, "subdivide", 0) or 0)
    trees = {"dual": {}, "columns": {}, "primal": {}, "rows": {}, "claim": None}
    terms_box = []

    def nn(poly, degrees=None):
        """`(ok, shifted, used, remainder, tree)` -- on the box when there is
        one, by the shift test otherwise."""
        if box is not None:
            from . import bernstein
            ok, tree = bernstein.nonneg(poly, box, depth, degrees)
            return ok, poly, {}, poly, tree
        ok, sh, used, rem = nonneg_on_region(poly, spec.parameters,
                                             terms_box[0] if terms_box else [])
        return ok, sh, used, rem, None

    if getattr(spec, "primal", None) is not None:
        return _certify_primal(spec, P, ring, minimising, free, claim, nn,
                               trees, box)

    if getattr(spec, "dual", None) is None:
        raise NotParametric(_t("param.no_witness"))
    hints = {}
    if spec.dual == "bernstein":
        if box is None:
            raise NotParametric(_t("param.bernstein_needs_box"))
        if depth > 0:
            # ONE DUAL PER BOX: find a dual on the box, and where there is
            # none -- or it misses the claim -- halve the box and find one on
            # each half. `subdivide` with a GIVEN dual halves where that one
            # dual's coefficients fall short; here each leaf gets its own.
            return _certify_pieces(spec, box, depth)
        y, hints = _find_dual_bernstein(spec, P, ring, box, minimising, free)
    else:
        y = {n: P(v) for n, v in spec.dual.items()}
    senses = {n: s for n, _, s, _ in spec.constraints}
    names = [n for n, _, _, _ in spec.constraints]
    missing = [n for n in names if n not in y]
    if missing:
        raise NotParametric(_t("param.dual_missing",
                               names=", ".join(missing[:5])))
    extra = [n for n in y if n not in names]
    if extra:
        raise NotParametric(_t("param.dual_extra", names=", ".join(extra[:5])))

    # The declared region, if any. These are SCOPE and not something proved:
    # the certificate holds where they hold, and says so every verification.
    region = [(str(n), P(g)) for n, g in (getattr(spec, "region", None) or [])]
    terms = region_terms(region, spec.parameters)
    terms_box.append(terms)

    # `y >= 0`. A constant dual is a comparison; a polynomial one is the same
    # test the residuals get, and "not shown non-negative" is what a failure
    # means there -- never "negative".
    negative, dual_rows = [], []
    for name in sorted(y):
        if senses.get(name) == "==":
            # An equality row's dual has either sign: nothing to show.
            dual_rows.append({"constraint": str(name),
                              "value": y[name].serialize(),
                              "shifted": y[name].serialize(), "ok": True,
                              "free": True, "region_multipliers": {}})
            continue
        ok, shifted, used, _rem, tree = nn(y[name],
                                           hints.get(("dual", str(name))))
        if tree is not None:
            trees["dual"][str(name)] = tree
        if not ok:
            negative.append(name)
        dual_rows.append({"constraint": str(name), "value": y[name].serialize(),
                          "shifted": shifted.serialize(), "ok": ok,
                          "region_multipliers": {k: str(v)
                                                 for k, v in used.items()}})

    # A^T y - c, column by column. Every variable that appears anywhere gets a
    # column, including ones the objective never mentions: a variable with no
    # objective coefficient still constrains the dual.
    variables = sorted({v for _, row, _, _ in spec.constraints for v in row}
                       | set(spec.objective))
    rows = []
    for var in variables:
        acc = Poly(ring)
        for name, row, _sense, _rhs in spec.constraints:
            if var in row and y[name].terms:
                acc = acc + P(row[var]) * y[name]
        obj = P(spec.objective.get(var, 0))
        # Maximise: `A^T y >= c`. Minimise: `M^T y <= w`. One sign.
        residual = (obj - acc) if minimising else (acc - obj)
        if var in free:
            # No sign on the variable, so the column must balance exactly.
            ok, shifted, used = not residual.terms, residual, {}
        else:
            ok, shifted, used, _rem, tree = nn(residual,
                                               hints.get(("column", var)))
            if tree is not None:
                trees["columns"][var] = tree
        rows.append({"variable": var,
                     "residual": residual.serialize(),
                     "shifted": shifted.serialize(),
                     "ok": ok,
                     "region_multipliers": {k: str(v) for k, v in used.items()},
                     "negative": sorted(str(c) for c in shifted.terms.values()
                                        if c < 0)})

    bound = Poly(ring)
    for name, _row, _sense, rhs in spec.constraints:
        if y[name].terms:
            bound = bound + P(rhs) * y[name]

    claimed = None
    if claim is not None:
        target = P(claim)
        # A dual bounds a maximisation from above: the claim is bound <= T.
        diff = (bound - target) if minimising else (target - bound)
        ok_c, _sh, _u, _r, tree = nn(diff, hints.get(("claim", None)))
        trees["claim"] = tree
        claimed = {"target": target.serialize(), "holds": ok_c,
                   "relation": ">=" if minimising else "<="}

    return {
        "witness": "dual",
        "box": _box_text(box),
        "box_trees": _trees_text(trees) if box is not None else None,
        "found_dual": {str(n): v.serialize() for n, v in y.items()}
        if spec.dual == "bernstein" else None,
        "free": sorted(free),
        "claim": claimed,
        "variables": variables,
        "rows": rows,
        "bound": bound,
        "sense": "min" if minimising else "max",
        "region": {n: g.serialize() for n, g in region},
        "dual_rows": dual_rows,
        # A dual is polynomial when some entry has more than one term, or one
        # term with a non-zero exponent. `any(e)` over the EXPONENT, not over
        # the dict -- iterating the dict yields keys, and a key is a non-empty
        # tuple and therefore always truthy.
        "polynomial_dual": any(len(p.terms) > 1
                               or any(any(e) for e in p.terms)
                               for p in y.values()),
        "negative_dual": negative,
        "ok": not negative and all(r["ok"] for r in rows),
        "failed": [r["variable"] for r in rows if not r["ok"]],
    }


def _certify_pieces(spec, box, depth):
    """The box, halved where one dual is not enough, with a dual found on
    every leaf. Returns the same shape `certify` does, with `pieces`."""
    import dataclasses

    from . import bernstein

    pieces, failed = [], []

    def attempt(b):
        leaf = dataclasses.replace(
            spec, box={n: (lo, hi) for n, (lo, hi) in b.items()},
            subdivide=0)
        try:
            out = certify(leaf)
        except NotParametric:
            return None
        if not out["ok"]:
            return None
        if out.get("claim") is not None and not out["claim"]["holds"]:
            return None
        return out

    def rec(b, d):
        out = attempt(b)
        if out is not None:
            pieces.append((b, out))
            return None                  # a leaf
        if d <= 0:
            failed.append(b)
            return None
        # halve the widest interval
        name = max(b, key=lambda n: (b[n][1] - b[n][0], -list(b).index(n)))
        left, right = bernstein.halves(b, name)
        return [name, rec(left, d - 1), rec(right, d - 1)]

    tree = rec(box, depth)
    minimising = getattr(spec, "sense", "max") == "min"
    return {
        "witness": "pieces", "pieces": pieces, "split": tree,
        "failed_boxes": [_box_text(b) for b in failed],
        "box": _box_text(box), "claim": None if getattr(spec, "claim", None)
        is None else {"target": _claim_text(spec), "holds": not failed,
                      "relation": ">=" if minimising else "<="},
        "ok": not failed, "failed": [], "negative_dual": [],
        "sense": "min" if minimising else "max",
        "variables": sorted({v for _, row, _, _ in spec.constraints for v in row}
                            | set(spec.objective)),
        "rows": [], "dual_rows": [], "polynomial_dual": True,
        "bound": None, "region": {}, "free": sorted(getattr(spec, "free", None)
                                                   or []),
        "box_trees": None, "found_dual": None,
    }


def _claim_text(spec):
    from .polynomials import Poly

    c = spec.claim
    ring = tuple(spec.parameters)
    if isinstance(c, Poly):
        return c.serialize()
    return Poly.const(ring, c).serialize()


def _box_of(spec, ring):
    raw = getattr(spec, "box", None)
    if raw is None:
        return None
    from . import bernstein

    if getattr(spec, "region", None):
        raise NotParametric(_t("param.box_region"))
    try:
        return bernstein.parse_box(raw, ring)
    except bernstein.NotABox as e:
        raise NotParametric(str(e)) from None


def _box_text(box):
    if box is None:
        return None
    return {n: [str(lo), str(hi)] for n, (lo, hi) in box.items()}


def _trees_text(trees):
    """Only the splits and degree hints that say something: a plain leaf at
    the polynomial's own degree is the default and is not written."""
    out = {}
    for key in ("dual", "columns", "primal", "rows"):
        kept = {n: t for n, t in (trees.get(key) or {}).items() if t is not None}
        if kept:
            out[key] = kept
    if trees.get("claim") is not None:
        out["claim"] = trees["claim"]
    return out


def _find_dual_bernstein(spec, P, ring, box, minimising, free):
    """A polynomial dual of degree `dual_degree` per parameter, found by ONE
    exact LP over its Bernstein coefficients on the box.

    Unknowns: the coefficients of every `y_i`, non-negative (so `y_i >= 0`
    on the box) except on an equality row. Constraints: every Bernstein
    coefficient of every residual `A^T y - c` (flipped for a minimisation) is
    `>= 0`, or `== 0` on a free column -- LINEAR in the unknowns, by the
    product formula. Objective: the sum of the bound's coefficients, the
    smallest for a maximisation and the largest for a minimisation. Returns
    the duals as polynomials and the degree each check must use.
    """
    from itertools import product

    from . import bernstein as B
    from .engines import lp as lp_engine
    from .spec import LPSpec

    k = tuple([int(getattr(spec, "dual_degree", 1) or 0)] * len(ring))
    grid = list(product(*(range(ki + 1) for ki in k)))
    rows = [(str(n), row, sense, rhs) for n, row, sense, rhs in spec.constraints]

    def vname(i, alpha):
        return "y{}_{}".format(i, "_".join(map(str, alpha)))

    L = LPSpec(sense="min" if not minimising else "max",
               title="bernstein dual")
    for i, (_n, _r, sense, _rhs) in enumerate(rows):
        for alpha in grid:
            L.variable(vname(i, alpha), None if sense == "==" else 0, None)

    variables = sorted({v for _, row, _, _ in rows for v in row}
                       | set(spec.objective))
    hints = {}
    for var in variables:
        entries = [(i, P(row[var])) for i, (_n, row, _s, _r) in enumerate(rows)
                   if var in row]
        obj = P(spec.objective.get(var, 0))
        deg_a = [B.degrees_of(a) for _i, a in entries] or [(0,) * len(ring)]
        top = tuple(max(d[j] for d in deg_a) + k[j] for j in range(len(ring)))
        D = tuple(max(t, o) for t, o in zip(top, B.degrees_of(obj)))
        hints[("column", var)] = list(D)
        acc = {}
        for i, a in entries:
            da = tuple(D[j] - k[j] for j in range(len(ring)))
            pm = B.product_map(B.coefficients(a, box, da), da, k)
            for gamma, row in pm.items():
                cell = acc.setdefault(gamma, {})
                for alpha, w in row.items():
                    key = vname(i, alpha)
                    cell[key] = cell.get(key, 0) + w
        oc = B.coefficients(obj, box, D)
        for gamma in product(*(range(Dj + 1) for Dj in D)):
            coeffs = dict(acc.get(gamma, {}))
            c0 = oc.get(gamma, 0)
            name = "col_{}_{}".format(var, "_".join(map(str, gamma)))
            if var in free:
                L.constraint(coeffs, "==", c0, name=name)
            elif minimising:
                # c - A^T y >= 0, i.e. A^T y <= c
                L.constraint(coeffs, "<=", c0, name=name)
            else:
                L.constraint(coeffs, ">=", c0, name=name)
    # The bound b(p).y(p), by the same product formula; its coefficients'
    # sum is the objective.
    bound_obj = {}
    rhs_deg = [B.degrees_of(P(rhs)) for _n, _r, _s, rhs in rows]
    Db = tuple(max(d[j] for d in rhs_deg) + k[j] for j in range(len(ring)))
    for i, (_n, _r, _s, rhs) in enumerate(rows):
        b = P(rhs)
        da = tuple(Db[j] - k[j] for j in range(len(ring)))
        for _gamma, row in B.product_map(B.coefficients(b, box, da), da,
                                         k).items():
            for alpha, w in row.items():
                key = vname(i, alpha)
                bound_obj[key] = bound_obj.get(key, 0) + w
    L.objective(bound_obj)

    # THE CLAIM AS A CONSTRAINT, not only a check afterwards: minimising the
    # bound's total can miss a claim at one end of the box that some other
    # dual meets. Every Bernstein coefficient of `T - b.y` must be >= 0 (the
    # other way for a minimisation), at one common degree -- which the check
    # below is then told to use.
    claim = getattr(spec, "claim", None)
    if claim is not None:
        T = P(claim)
        Dc = tuple(max(a, b) for a, b in zip(Db, B.degrees_of(T)))
        acc = {}
        for i, (_n, _r, _s, rhs) in enumerate(rows):
            b = P(rhs)
            da = tuple(Dc[j] - k[j] for j in range(len(ring)))
            for gamma, row in B.product_map(B.coefficients(b, box, da), da,
                                            k).items():
                cell = acc.setdefault(gamma, {})
                for alpha, w in row.items():
                    key = vname(i, alpha)
                    cell[key] = cell.get(key, 0) + w
        tc = B.coefficients(T, box, Dc)
        for gamma in product(*(range(Dj + 1) for Dj in Dc)):
            L.constraint(dict(acc.get(gamma, {})),
                         ">=" if minimising else "<=", tc.get(gamma, 0),
                         name="claim_{}".format("_".join(map(str, gamma))))
        hints[("claim", None)] = list(Dc)
    res = lp_engine.opt(L)
    if res.certificate is None or not res.meta.get("exact"):
        raise NotParametric(_t("param.bernstein_no_dual_claim"
                               if claim is not None else
                               "param.bernstein_no_dual",
                               degree=k[0] if k else 0,
                               detail=res.detail or res.status.value))
    sol = res.meta.get("solution") or {}
    y = {}
    for i, (n, _r, _s, _rhs) in enumerate(rows):
        coeffs = {alpha: Fraction(sol.get(vname(i, alpha), "0"))
                  for alpha in grid}
        y[n] = B.from_coefficients(ring, box, k, coeffs)
        hints[("dual", n)] = list(k)
    return y, hints


def _certify_primal(spec, P, ring, minimising, free, claim, nn=None,
                    trees=None, box=None) -> dict:
    """A feasible `x(p)`: every row holds, every non-free `x >= 0`.

    Weak duality is not used at all, so any row sense is allowed. The bound
    is the objective at `x`, and it bounds the optimum from BELOW for a
    maximisation and from ABOVE for a minimisation -- the direction a user
    was getting by passing a primal off as the dual of a max program.
    """
    region = [(str(n), P(g)) for n, g in (getattr(spec, "region", None) or [])]
    terms = region_terms(region, spec.parameters)
    trees = trees if trees is not None else {"primal": {}, "rows": {},
                                             "claim": None}
    if nn is None or box is None:
        def nn(poly, degrees=None):
            ok, sh, used, rem = nonneg_on_region(poly, spec.parameters, terms)
            return ok, sh, used, rem, None
    x = {str(v): P(e) for v, e in spec.primal.items()}
    variables = sorted({v for _, row, _, _ in spec.constraints for v in row}
                       | set(spec.objective) | set(x))
    xrows = []
    for var in variables:
        value = x.get(var, Poly(ring))
        if var in free:
            xrows.append({"variable": var, "value": value.serialize(),
                          "ok": True, "free": True})
            continue
        ok, shifted, used, _rem, tree = nn(value)
        if tree is not None:
            trees["primal"][var] = tree
        xrows.append({"variable": var, "value": value.serialize(), "ok": ok,
                      "shifted": shifted.serialize(),
                      "region_multipliers": {k: str(v) for k, v in used.items()}})
    rows = []
    for name, row, sense, rhs in spec.constraints:
        lhs = Poly(ring)
        for var, coef in row.items():
            if x.get(var) is not None and x[var].terms:
                lhs = lhs + P(coef) * x[var]
        if sense == "==":
            slack = lhs - P(rhs)
            ok, shifted = not slack.terms, slack
        else:
            slack = (P(rhs) - lhs) if sense == "<=" else (lhs - P(rhs))
            ok, shifted, _u, _r, tree = nn(slack)
            if tree is not None:
                trees["rows"][str(name)] = tree
        rows.append({"constraint": str(name), "slack": slack.serialize(),
                     "shifted": shifted.serialize(), "ok": ok})
    bound = Poly(ring)
    for var, coef in spec.objective.items():
        if x.get(var) is not None and x[var].terms:
            bound = bound + P(coef) * x[var]
    claimed = None
    if claim is not None:
        target = P(claim)
        # A primal bounds a minimisation from above: the claim is bound <= T.
        diff = (target - bound) if minimising else (bound - target)
        ok_c, _sh, _u, _r, tree = nn(diff)
        trees["claim"] = tree
        claimed = {"target": target.serialize(), "holds": ok_c,
                   "relation": "<=" if minimising else ">="}
    negative = [r["variable"] for r in xrows if not r["ok"]]
    failed = [r["constraint"] for r in rows if not r["ok"]]
    return {
        "witness": "primal", "free": sorted(free), "claim": claimed,
        "box": _box_text(box),
        "box_trees": _trees_text(trees) if box is not None else None,
        "found_dual": None,
        "variables": variables, "rows": rows, "primal_rows": xrows,
        "bound": bound, "sense": "min" if minimising else "max",
        "region": {n: g.serialize() for n, g in region},
        "dual_rows": [], "polynomial_dual": False,
        "primal": {v: e.serialize() for v, e in sorted(x.items())},
        "negative_dual": negative, "ok": not negative and not failed,
        "failed": failed,
    }


def evaluate(poly: Poly, values: dict) -> Fraction:
    """The polynomial at one point. For checking a bound against a known LP."""
    total = Fraction(0)
    for e, coef in poly.terms.items():
        term = coef
        for name, power in zip(poly.vars, e):
            if power:
                term *= Fraction(values[name]) ** power
        total += term
    return total
