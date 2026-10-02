"""nonneg: a polynomial >= 0 on a box -- with an algebraic endpoint, exactly.

The bound `x <= 3/10` on the interval `[0, sqrt(3/40)]` (about 0.2739). The
right end is not rational, and cutting at a rational nearby means proving two
bounds by hand and the gap between them. Here the interval is the box
`[0, 1/2]` cut by the region `3/40 - x^2 >= 0`, which IS `[0, sqrt(3/40)]`
there, and the certificate is Bernstein coefficients plus one constant
multiplier of that condition:

    $ certo nonneg examples/nonneg_box.py
    PROVED  [unsat]
      -x + 3/10 >= 0 for x in [0, 1/2]; -x^2 + 3/40 >= 0

Ask for `1/4 - x` instead and it is REFUTED, with the point `x = 17/64` --
inside the region, since (17/64)^2 < 3/40 -- and the exact value -1/64.
"""
from fractions import Fraction

from certo import NonnegSpec
from certo.polynomials import Poly

x = Poly.var(("x",), "x")


def spec():
    return NonnegSpec(poly=Fraction(3, 10) - x,
                      box={"x": (0, Fraction(1, 2))},
                      region=[("below_root", Fraction(3, 40) - x ** 2)],
                      title="x <= 3/10 on [0, sqrt(3/40)]")
