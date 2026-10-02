"""pin: a value pinned from both sides -- cp_3(K_7) = 7.

The 21 edges of K_7 split into the 7 lines of the Fano plane, each a
triangle: a partition into 7 cliques of order <= 3, so cp_3(K_7) <= 7. The
LP over every clique of order 2 or 3, counting cliques with each edge covered
once, has optimum 21/3 = 7, so every such partition has at least 7 parts.

    $ certo pin examples/pin_fano.py
    PROVED  [unsat]
      cp_3(G) = 7, PROVED from both sides

What `pin` adds over the two certificates side by side is the TIE: both are
re-verified and both are shown to be about the same edge list and the same
quantity -- pieces of order <= 3 above, an LP that allows every such piece
below -- before 7 and ceil(7) are compared. A cover of another graph, or an
LP over triangles only, is refused by name.
"""
from itertools import combinations

from certo import CoverSpec, PinSpec
from certo.spec import CliqueLPSpec

EDGES = list(combinations(range(7), 2))
FANO = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1),
        (6, 0, 2)]


def spec():
    return PinSpec(
        edges=EDGES, max_size=3,
        upper=CoverSpec(universe=EDGES, parts=FANO, cliques=True, max_size=3),
        lower=CliqueLPSpec(edges=EDGES, problem="partition",
                           weight={"constant": 1}, max_size=3),
        title="cp_3(K_7) = 7")
