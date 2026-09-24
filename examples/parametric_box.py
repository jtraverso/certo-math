"""A parametric bound on a BOX, with the dual found by certo.

    max x   subject to   (2 - p) x <= 1,   x >= 0,   for every p in [0, 1]

The optimum is 1/(2-p), which is not a polynomial. A polynomial UPPER bound
on the box is what a proof usually needs, and a dual `y(p)` gives one by weak
duality -- as long as the residual `(2-p) y(p) - 1` is non-negative on the
whole box.

    $ certo parametric examples/parametric_box.py
    PROVED  [unsat]
      for all p in [0, 1], the optimum is at most 1/4*p^2 + 1/4*p + 1/2
      certificate: parametric_bound (no solver needed)

WHAT CHANGED. The shift test proves non-negativity on a RAY `p >= p0`, so a
bounded box used to be reparametrised by hand -- `p = lo + h t/(1+t)` -- and
the dual built from an LP at each control point. Here `box=` is declared, and
every non-negativity is decided by Bernstein coefficients on it, exactly.
`dual="bernstein"` has certo find the dual too: its Bernstein coefficients
are the unknowns of ONE exact LP whose constraints are the residuals'
coefficients, and the answer is checked like any dual somebody brought.

The bound found is tight at both ends of the box -- 1/2 at p=0, 1 at p=1 --
and above 1/(2-p) in between. `subdivide=d` would let the box be halved where
a single set of coefficients is not enough; the certificate records the splits
and `verify` recomputes every leaf.
"""
from certo import ParametricSpec
from certo.polynomials import Poly

RING = ("p",)
p = Poly.var(RING, "p")


def K(c):
    return Poly.const(RING, c)


def spec():
    return ParametricSpec(
        parameters={"p": 0},
        objective={"x": K(1)},
        constraints=[("cap", {"x": K(2) - p}, "<=", K(1))],
        dual="bernstein", dual_degree=2,
        box={"p": (0, 1)},
        title="1/(2-p) bounded by a quadratic on [0, 1]",
    )
