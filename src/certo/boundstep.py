"""A step between bounds, checked: `D <= f` and `x <= u` give `D <= g`?

A user turned `D <= B / (1 + B/n)` and `B <= y B1` into `D <= y B1 / (1 +
B1/n)`. It does not follow: `B / (1 + B/n)` is increasing in B, so the
substitution gives `y B1 / (1 + y B1/n)`, and the two differ exactly when
y != 1 -- the comparison with the chord runs the other way. Certifying the
coefficients that went in would not have caught it; checking the STEP does.

The rules, each one a sign on a closed box, certified by Bernstein
coefficients (no solver) and kept in the certificate:

  substitute x <= u   the bound is NONDECREASING in x on the box (its
                      derivative >= 0, wherever the conditions hold), and u
                      stays inside x's interval -- then f(x) <= f(u)
  conclude g          g - f >= 0 on the box, wherever the conditions hold

A step that fails comes back with the point where it fails, and with what
DOES follow: the bound after the substitutions, `D <= f(u)`.

Rational functions are pairs of polynomials `(N, D)`; nothing is
cancelled, and every denominator's sign is proved where it matters.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t
from .polynomials import Poly


class NotAStep(ValueError):
    """Raised with what is wrong with the spec."""


# --- rational functions as (N, D) -------------------------------------------


def normal(r):
    """Monic denominator, the way `rational_function` leaves it."""
    n, d = r
    if not d.terms:
        # a ZERO denominator read as 1 made `u / 0` a valid substitute
        raise ValueError("a rational function with denominator 0")
    lead = d.lead()
    if lead is not None and lead[1] != 1:
        n, d = n.scaled(1 / lead[1]), d.scaled(1 / lead[1])
    if d.degree <= 0:
        return n, Poly.const(n.vars, 1)
    return n, d


def sub(a, b):
    (n1, d1), (n2, d2) = a, b
    if d1 == d2:
        return n1 - n2, d1
    return n1 * d2 - n2 * d1, d1 * d2


def diff_poly(p, var):
    i = list(p.vars).index(var)
    out = {}
    for e, c in p.terms.items():
        if e[i]:
            e2 = list(e)
            e2[i] -= 1
            out[tuple(e2)] = out.get(tuple(e2), Fraction(0)) + c * e[i]
    return Poly(p.vars, out)


def diff(r, var):
    """d/dvar (N/D) = (N' D - N D') / D^2."""
    n, d = r
    return (diff_poly(n, var) * d - n * diff_poly(d, var), d * d)


def _subst_poly(p, var, u):
    """p with var := Nu/Du, as (numerator, Du^deg) -- deg the degree of p in var."""
    i = list(p.vars).index(var)
    nu, du = u
    k = max((e[i] for e in p.terms), default=0)
    out = Poly(p.vars)
    for e, c in p.terms.items():
        rest = list(e)
        rest[i] = 0
        mono = Poly(p.vars, {tuple(rest): c})
        out = out + mono * (nu ** e[i]) * (du ** (k - e[i]))
    return out, k


def subst(r, var, u):
    """N/D with var := Nu/Du."""
    n, d = r
    sn, kn = _subst_poly(n, var, u)
    sd, kd = _subst_poly(d, var, u)
    du = u[1]
    return sn * (du ** kd), sd * (du ** kn)


def to_z3(p):
    import z3

    total = z3.RealVal(0)
    for e, c in p.terms.items():
        term = z3.RealVal(c)
        for v, k in zip(p.vars, e):
            if k:
                term = term * (z3.Real(v) ** k if k > 1 else z3.Real(v))
        total = total + term
    return total


def rat_to_z3(r):
    n, d = r
    if d.degree <= 0:
        c = d.terms.get((0,) * len(d.vars), Fraction(1))
        return to_z3(n.scaled(1 / c))
    return to_z3(n) / to_z3(d)


def ser(r):
    return [r[0].serialize(), r[1].serialize()]


def parse(ring, data):
    """`[N, D]`, exactly two: a third entry was read past, not refused."""
    if not isinstance(data, list) or len(data) != 2:
        raise ValueError("a rational function is [numerator, denominator]")
    return Poly.parse(ring, data[0]), Poly.parse(ring, data[1])


def rat_of_nonneg(payload):
    """`(N, D)` a `polynomial_nonneg` payload certifies `N/D >= 0` of."""
    ring = tuple(payload["parameters"])
    cl = payload.get("cleared")
    if cl:
        return normal((Poly.parse(ring, cl["numerator"]),
                       Poly.parse(ring, cl["denominator"])))
    return normal((Poly.parse(ring, payload["poly"]), Poly.const(ring, 1)))


def same_rat(a, b) -> bool:
    """Equal as rational functions: N1 D2 == N2 D1."""
    return a[0] * b[1] == b[0] * a[1]
