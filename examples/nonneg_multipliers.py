"""nonneg: multipliers found ELSEWHERE, checked here -- and a product of three.

    (x - 1/4)(3/4 - x)(x - 1/2) >= 0   where   x >= 1/4, x <= 3/4, x >= 1/2

The polynomial is negative on most of [0, 1]; on the region it is a product
of three non-negative factors. Constant multipliers of the conditions and
their PAIRWISE products cannot show that, and certo says so. Two ways in:

  * `multipliers={"a*b*c": 1}` -- a witness from another tool, CHECKED, not
    searched: every multiplier >= 0, a known term, and the remainder
    `poly - sum(lambda * term)` non-negative by Bernstein;
  * `products=3` instead -- triples of the ACTIVE conditions are built on
    demand when pairs fail, and the multipliers found.

Either way the certificate is the ordinary `polynomial_nonneg`, and `verify`
builds the product `a*b*c` from the conditions themselves.

    certo nonneg examples/nonneg_multipliers.py --cert out/nonneg_mult.json
    certo verify out/nonneg_mult.json
"""
from fractions import Fraction

import z3

from certo import NonnegSpec

x = z3.Real("x")
a = x - Fraction(1, 4)
b = Fraction(3, 4) - x
c = x - Fraction(1, 2)


def spec():
    return NonnegSpec(
        title="a product of three conditions, on the region they cut",
        poly=a * b * c,
        box={"x": (0, 1)},
        region=[("a", a), ("b", b), ("c", c)],
        multipliers={"a*b*c": 1},
    )
