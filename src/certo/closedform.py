"""A closed form PROPOSED for a floating-point number. Never a result.

Exploration answers in floating point -- `10.66666656003499`, `0.6180339887`
-- and the next thing a reader does is guess what the number IS. This makes
that guess the way mpmath's integer-relation search does (PSLQ, through
`findpoly`), and labels it for what it is: a conjecture from the digits. The
library proposes; certo certifies -- `certo promote` re-runs the exploration
exactly and says whether the proposal was the value.

Only two shapes are proposed, because only they can be checked by what
certo already has: a rational with a small denominator (every LP optimum is
one), and a quadratic irrational `(p + q*sqrt(d)) / r` (a threshold found by
`bisect` often is). Anything else -- pi, a logarithm, a root of a quintic --
gets no proposal rather than a fluent wrong one.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, isqrt

#: The largest denominator worth calling "small". Past it, a rational that
#: matches ten digits is not evidence of anything: there are too many.
MAX_DENOMINATOR = 10_000
#: The largest coefficient PSLQ may use for a quadratic.
MAX_COEFF = 1_000
#: How SIGNIFICANT a match must be: the residual times the proposal's
#: complexity -- the denominator squared, or the coefficient height cubed --
#: at most this. Without it, `(3 + 5*sqrt(7))/4` was "32563/8026" to nine
#: digits: with denominators up to ten thousand, some rational always comes
#: that close, and matching it says nothing.
SIGNIFICANCE = 1e-3


def guess(x, rel_tol: float = 1e-7):
    """`{"kind": "rational"|"quadratic", "value": text, ...}` or None.

    `rel_tol` is how close the proposal must come, relative to `1 + |x|`. CBC
    reports `10.66666656003499` for 32/3, about seven digits: the default.
    """
    try:
        x = float(x)
    except (TypeError, ValueError):
        return None
    if x != x or x in (float("inf"), float("-inf")):
        return None
    tol = rel_tol * (1 + abs(x))

    q = Fraction(x).limit_denominator(MAX_DENOMINATOR)
    residual = abs(float(q) - x)
    if residual <= tol and residual * q.denominator ** 2 <= SIGNIFICANCE:
        return {"kind": "rational", "value": str(q), "residual": residual}

    try:
        import mpmath
    except ImportError:          # an optional proposer, never a requirement
        return None
    with mpmath.workdps(30):
        coeffs = mpmath.findpoly(mpmath.mpf(x), 2, maxcoeff=MAX_COEFF,
                                 tol=tol)
    if not coeffs or len(coeffs) != 3 or coeffs[0] == 0:
        return None
    a, b, c = (int(v) for v in coeffs)
    disc = b * b - 4 * a * c
    if disc <= 0 or isqrt(disc) ** 2 == disc:
        return None              # not irrational: the rational test decides
    text, value = _root_text(a, b, disc, x)
    height = max(abs(a), abs(b), abs(c))
    if (text is None or abs(value - x) > tol
            or abs(value - x) * height ** 3 > SIGNIFICANCE):
        return None
    return {"kind": "quadratic", "value": text,
            "polynomial": [a, b, c], "residual": abs(value - x)}


def _root_text(a, b, disc, x):
    """The root of `a t^2 + b t + c` nearest `x`, as `(p ± q*sqrt(d))/r` in
    lowest terms with `d` square-free."""
    q, d = 1, disc
    f = 2
    while f * f <= d:
        while d % (f * f) == 0:
            d //= f * f
            q *= f
        f += 1
    best = None
    for sign in (1, -1):
        value = (-b + sign * q * d ** 0.5) / (2 * a)
        if best is None or abs(value - x) < abs(best[1] - x):
            best = (sign, value)
    sign, value = best
    p, s, r = -b, sign * q, 2 * a
    g = gcd(gcd(abs(p), abs(s)), abs(r))
    p, s, r = p // g, s // g, r // g
    if r < 0:
        p, s, r = -p, -s, -r
    root = "sqrt({})".format(d) if abs(s) == 1 else "{}*sqrt({})".format(abs(s), d)
    num = (("{} {} {}".format(p, "+" if s > 0 else "-", root)) if p
           else ("{}{}".format("" if s > 0 else "-", root)))
    text = num if r == 1 else "({})/{}".format(num, r)
    return text, value


def matches(proposal, exact) -> bool | None:
    """Did a proposal turn out to be the exact value? None when the two
    cannot be compared exactly here (a quadratic against a rational is
    simply False: a rational is never a quadratic irrational)."""
    if not proposal:
        return None
    try:
        exact = Fraction(str(exact))
    except (TypeError, ValueError, ZeroDivisionError):
        return None
    if proposal.get("kind") == "rational":
        return Fraction(proposal["value"]) == exact
    if proposal.get("kind") == "quadratic":
        return False
    return None
