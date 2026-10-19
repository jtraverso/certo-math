"""Farkas and degree-2 Positivstellensatz certificates.

The Python counterparts of Lean's `linarith` and `nlinarith`, and built the
same way they are.

`linarith` does not "decide" anything clever: it looks for a NON-NEGATIVE
combination of the hypotheses (plus the negated goal) that sums to a
contradiction. Those multipliers are a Farkas certificate, and finding them is
a linear program -- which is why this lives on top of the exact LP machinery
rather than next to it.

`nlinarith` is `linarith` with a preprocessing step: multiply pairs of
hypotheses, throw in some squares, treat each monomial as a fresh variable,
and run the linear search on that. No semidefinite programming involved. That
is why it is a heuristic and not a decision procedure -- and it is reproduced
here faithfully, heuristic and all.

Why not go through an SDP and get a real sum-of-squares certificate instead:
an SDP is solved in floating point, so what comes back is not exact, and an
inexact certificate is not citable. Same reason `opt` reconstructs rationals.
Z3's `nlsat` is available through `prove` and is COMPLETE for real arithmetic,
so the honest division of labour is: `prove` to know, `farkas` to certify.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

import z3

from .exact import to_fraction

# A polynomial is {monomial: coefficient}, where a monomial is a sorted tuple
# of variable names with repetition: () is the constant, ("x",) is x,
# ("x", "x") is x squared. Linear just means every monomial has length <= 1.
CONST = ()


class NotPolynomial(ValueError):
    """Raised with the offending subterm, because "it failed" is useless."""


def _add(p: dict, q: dict, scale=1) -> dict:
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, Fraction(0)) + c * scale
        if out[m] == 0:
            del out[m]
    return out


def _mul(p: dict, q: dict) -> dict:
    out: dict = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            out[m] = out.get(m, Fraction(0)) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def polynomial(e) -> dict:
    """z3 arithmetic term -> {monomial: Fraction}.

    SUMS AND PRODUCTS ARE WALKED WITH A STACK, NOT BY RECURSION. A sum built
    as `out += term` is a chain as deep as it is long, and 1500 terms took
    0.34 past Python's recursion limit -- reported as a `ctypes.ArgumentError`
    that named neither the depth nor the sum. The same polynomial written with
    `z3.Sum` was read; now the shape of the term does not matter.
    """
    return _polynomial(e, {})


def _flatten(e, is_op):
    """The operands of a chain of one associative operator, left to right,
    without recursion."""
    out, stack = [], [e]
    while stack:
        x = stack.pop()
        if is_op(x):
            stack.extend(reversed(x.children()))
        else:
            out.append(x)
    return out


def _signed_terms(e):
    """A chain of `+`, `-` and unary minus as `[(sign, term)]`."""
    out, stack = [], [(1, e)]
    while stack:
        sign, x = stack.pop()
        if z3.is_add(x):
            stack.extend((sign, c) for c in reversed(x.children()))
        elif z3.is_sub(x):
            a, b = x.children()
            stack.append((-sign, b))
            stack.append((sign, a))
        elif z3.is_app_of(x, z3.Z3_OP_UMINUS):
            stack.append((-sign, x.arg(0)))
        else:
            out.append((sign, x))
    return out


def _kids(e):
    """The subterms `_combine` needs, in the order it reads them."""
    if z3.is_add(e) or z3.is_sub(e) or z3.is_app_of(e, z3.Z3_OP_UMINUS):
        return [c for _sign, c in _signed_terms(e)]
    if z3.is_mul(e):
        return _flatten(e, z3.is_mul)
    if z3.is_div(e) or z3.is_idiv(e):
        return list(e.children())
    if z3.is_app_of(e, z3.Z3_OP_POWER):
        return [e.children()[0]]
    return []


def _combine(e, memo):
    """`e`'s polynomial from its subterms', all already in `memo`."""
    if z3.is_int_value(e):
        return {CONST: Fraction(e.as_long())}
    if z3.is_rational_value(e):
        return {CONST: Fraction(e.as_fraction())}
    if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return {(str(e),): Fraction(1)}
    if z3.is_add(e) or z3.is_sub(e) or z3.is_app_of(e, z3.Z3_OP_UMINUS):
        out = {}
        for sign, c in _signed_terms(e):          # in place: a long sum is linear
            for m, v in memo[c.get_id()].items():
                out[m] = out.get(m, Fraction(0)) + v * sign
        return {m: v for m, v in out.items() if v != 0}
    if z3.is_mul(e):
        out = {CONST: Fraction(1)}
        for c in _flatten(e, z3.is_mul):
            out = _mul(out, memo[c.get_id()])
        return out
    if z3.is_div(e) or z3.is_idiv(e):
        a, b = e.children()
        db = memo[b.get_id()]
        if list(db) != [CONST] or db[CONST] == 0:
            raise NotPolynomial("division by a non-constant: {}".format(e))
        return {m: c / db[CONST] for m, c in memo[a.get_id()].items()}
    if z3.is_app_of(e, z3.Z3_OP_POWER):
        base, exp = e.children()
        n = _literal_exponent(exp)
        if n is None:
            raise NotPolynomial("non-constant or negative exponent: {}".format(e))
        b = memo[base.get_id()]
        out = {CONST: Fraction(1)}
        for _ in range(n):
            out = _mul(out, b)
        return out
    raise NotPolynomial("not polynomial arithmetic: {}".format(e))


def _polynomial(e, memo):
    """Post-order over the term with an explicit stack: no recursion at all,
    whatever mixes of sums, products and minus signs nest how deep."""
    stack = [(e, False)]
    while stack:
        node, ready = stack.pop()
        key = node.get_id()
        if key in memo:
            continue
        if ready:
            memo[key] = _combine(node, memo)
            continue
        stack.append((node, True))
        for c in _kids(node):
            if c.get_id() not in memo:
                stack.append((c, False))
    return memo[e.get_id()]


def _literal_exponent(exp):
    """A literal natural-number exponent, or None.

    `x**4` on a REAL x gives z3 a rational literal 4, not an integer one, so
    `is_int_value` says no and a perfectly ordinary quartic gets rejected. The
    exponent's SORT is not the question -- whether it is a literal natural
    number is.
    """
    if z3.is_int_value(exp):
        n = exp.as_long()
    elif z3.is_rational_value(exp):
        frac = exp.as_fraction()
        if frac.denominator != 1:
            return None
        n = frac.numerator
    else:
        return None
    return n if n >= 0 else None


def as_row(e):
    """A z3 comparison -> (polynomial, relation) normalised to `p REL 0`.

    REL is "<=", "<" or "=". Everything is moved to the left-hand side so the
    combination step has nothing to think about.
    """
    if z3.is_not(e):
        inner = e.arg(0)
        flip = {"<=": ">", "<": ">=", ">=": "<", ">": "<=", "=": "!="}
        p, rel = as_row(inner)
        if rel == "=":
            raise NotPolynomial("negated equality is not a single row: {}".format(e))
        # not (p <= 0) is p > 0, i.e. -p < 0
        neg = {m: -c for m, c in p.items()}
        return (neg, "<") if rel == "<=" else (neg, "<=")

    if not z3.is_app(e) or e.num_args() != 2:
        raise NotPolynomial("not a comparison: {}".format(e))
    lhs, rhs = e.children()
    diff = _add(polynomial(lhs), polynomial(rhs), scale=-1)     # lhs - rhs
    flipped = {m: -c for m, c in diff.items()}                  # rhs - lhs

    if z3.is_le(e):
        return diff, "<="
    if z3.is_lt(e):
        return diff, "<"
    if z3.is_ge(e):
        return flipped, "<="
    if z3.is_gt(e):
        return flipped, "<"
    if z3.is_eq(e):
        return diff, "="
    raise NotPolynomial("unsupported comparison: {}".format(e))


def rows_of(spec):
    """Named hypotheses plus the NEGATED goal, all as `p REL 0`.

    Equalities are split into two inequalities: the LP wants non-negative
    multipliers, and an equality's multiplier is free in sign.
    """
    out = []
    for name, f in spec.assumptions:
        p, rel = as_row(f)
        if rel == "=":
            out.append((name, p, "<="))
            out.append((name + "_rev", {m: -c for m, c in p.items()}, "<="))
        else:
            out.append((name, p, rel))
    if spec.goal is not None:
        p, rel = as_row(z3.Not(spec.goal))
        out.append(("__goal__", p, rel))
    return out


def products(rows):
    """The `nlinarith` preprocessing: pairwise products and squares.

    If `a <= 0` and `b <= 0` then `a*b >= 0`, i.e. `-a*b <= 0`. That is the
    whole trick, and it is the reason nlinarith is a heuristic: which products
    to add is a guess, not a search.
    """
    extra, origin = [], {}
    for (n1, p1, _), (n2, p2, _) in combinations(rows, 2):
        prod = _mul(p1, p2)
        extra.append(("{}*{}".format(n1, n2), {m: -c for m, c in prod.items()}, "<="))
        origin["{}*{}".format(n1, n2)] = {"kind": "product", "of": [n1, n2]}
    for name, p, _ in rows:                       # each hypothesis squared
        sq = _mul(p, p)
        extra.append(("{}^2".format(name), {m: -c for m, c in sq.items()}, "<="))
        origin["{}^2".format(name)] = {"kind": "square", "of": _ser(p)}
    atoms = sorted({v for _, p, _ in rows for m in p for v in m})
    for v in atoms:                               # x^2 >= 0
        extra.append(("sq_{}".format(v), {(v, v): Fraction(-1)}, "<="))
        origin["sq_{}".format(v)] = {"kind": "square",
                                     "of": _ser({(v,): Fraction(1)})}
    for a, b in combinations(atoms, 2):           # (x - y)^2 >= 0
        sq = _mul({(a,): Fraction(1), (b,): Fraction(-1)},
                  {(a,): Fraction(1), (b,): Fraction(-1)})
        extra.append(("sq_{}_{}".format(a, b), {m: -c for m, c in sq.items()},
                      "<="))
        origin["sq_{}_{}".format(a, b)] = {
            "kind": "square",
            "of": _ser({(a,): Fraction(1), (b,): Fraction(-1)})}
    # The names alone are ambiguous -- a variable may contain an underscore --
    # so what each derived row is a square OF travels as a polynomial.
    return extra, origin


def _ser(poly) -> dict:
    return {" ".join(m) if m else "1": str(c) for m, c in poly.items()}


def combination(rows, multipliers) -> dict:
    """Sum lambda_i * row_i. The certificate check, in one line of arithmetic."""
    out: dict = {}
    for (_, p, _), lam in zip(rows, multipliers):
        if lam:
            out = _add(out, {m: c * to_fraction(lam) for m, c in p.items()})
    return out


def is_contradiction(rows, multipliers):
    """Does the combination actually close? Returns (ok, constant, strict)."""
    total = combination(rows, multipliers)
    nonconst = {m: c for m, c in total.items() if m != CONST and c != 0}
    const = total.get(CONST, Fraction(0))
    strict = any(rel == "<" and to_fraction(lam) > 0
                 for (_, _, rel), lam in zip(rows, multipliers))
    if nonconst:
        return False, const, strict
    # every variable cancelled; now: `const REL 0` must be false
    if strict:
        return const >= 0, const, True      # `const < 0` with const >= 0
    return const > 0, const, False          # `const <= 0` with const > 0


def serialize_rows(rows) -> list:
    """Rows as JSON, so a certificate carries the arithmetic it claims."""
    return [{"name": n,
             "poly": {" ".join(m) if m else "1": str(c) for m, c in p.items()},
             "rel": rel}
            for n, p, rel in rows]


def parse_rows(data) -> list:
    out = []
    for r in data:
        poly = {}
        for key, c in r["poly"].items():
            m = CONST if key == "1" else tuple(key.split(" "))
            poly[m] = Fraction(c)
        out.append((r["name"], poly, r["rel"]))
    return out


def row_to_z3(poly, rel, sort_of=None):
    """A row back into a z3 formula, so it can be reasoned about again.

    `compose` needs this: to check that a lemma's statement really entails
    the rows a Farkas certificate combined, those rows have to become
    formulas again. `sort_of` maps a variable name to "Int" or "Real"; it
    comes from the statement, because the same name in the wrong sort would
    quietly become a different variable.
    """
    import z3

    sort_of = sort_of or {}

    def var(name):
        return z3.Int(name) if sort_of.get(name) == "Int" else z3.Real(name)

    terms = []
    for m, c in sorted(poly.items()):
        factors = [z3.RealVal(str(c))] if m else [z3.RealVal(str(c))]
        for v in m:
            factors.append(var(v))
        term = factors[0]
        for f in factors[1:]:
            term = term * f
        terms.append(term)
    lhs = terms[0] if terms else z3.RealVal(0)
    for tm in terms[1:]:
        lhs = lhs + tm
    return lhs <= 0 if rel == "<=" else (lhs < 0 if rel == "<" else lhs == 0)
