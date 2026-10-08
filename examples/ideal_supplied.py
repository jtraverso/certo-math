"""ideal with SUPPLIED cofactors: checked by expanding, nothing searched.

When the combination is already known -- written by hand, or found by another
tool -- there is nothing to search for: `x^2 - y^2 = (x + y)(x - y)` with the
cofactor `x + y` on the equation `x - y = 0`. certo expands the combination
and compares it with the claim, the same check `verify` makes; a wrong
cofactor is reported with its residue instead of being searched around. The
rationals are exact: `Fraction(1, 2)` stays one half.

    certo ideal examples/ideal_supplied.py
"""
from fractions import Fraction

import z3

from certo import IdealSpec


def spec():
    x, y = z3.Reals("x y")
    return IdealSpec(
        variables=["x", "y"],
        equations=[x - y, 2 * y - 1],
        claim=x * x - y * y + Fraction(1, 2) * (2 * y - 1),
        cofactors=[x + y, Fraction(1, 2)],
        title="a difference of squares, with the cofactors supplied",
    )
