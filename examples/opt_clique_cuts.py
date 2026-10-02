"""opt --cuts clique --round: one inequality where branching was the cost.

Four items, any two in conflict -- each pair excluded by its own row. The LP
puts 1/2 on every item and bounds the integer optimum by 2; the best design
picks one item. Branch and bound closes that gap by search, and on a
symmetric instance the search is the cost.

The conflicts form a clique, and a clique's cut, `x0 + x1 + x2 + x3 <= 1`,
holds at every INTEGER point. With it the LP bound is 1, and rounding makes
it the integer optimum, proved:

    $ certo opt examples/opt_clique_cuts.py --cuts clique --round
    SATISFIABLE  [sat]
      with 1 clique cut(s) of the conflict graph -- the bound is on the
      INTEGER optimum. integer optimum 1, PROVED: an integral point reaches
      it, and the exact LP bound 1 rounds to it

`verify` re-derives the cut: every pair it joins must be excluded by a row of
the program itself, named in the certificate. A cut no row forces is refused.
"""
from itertools import combinations

from certo import LPSpec


def spec():
    lp = LPSpec(sense="max", title="four items, pairwise in conflict")
    for i in range(4):
        lp.variable("x%d" % i, 0, 1, kind="binary")
    lp.objective({"x%d" % i: 1 for i in range(4)})
    for i, j in combinations(range(4), 2):
        lp.constraint({"x%d" % i: 1, "x%d" % j: 1}, "<=", 1,
                      name="conflict_%d%d" % (i, j))
    return lp
