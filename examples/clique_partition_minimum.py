"""cover --minimum: the clique partition number, proved by a recurrence.

The octahedron's twelve edges, with every clique as a candidate. A cover of
four triangles shows four suffice; this proves no THREE do, and does it
without a solver: the lowest edge left must lie in some chosen clique, so
the recurrence over masks branches only on those, and its table -- every
subset of edges it reaches, each with its value and choice -- is checked
entry by entry by `verify`.

    certo cover examples/clique_partition_minimum.py --minimum
"""
from certo import CoverSpec
from certo.existence import cliques_of


def spec():
    n = 6
    opposite = {(0, 1), (2, 3), (4, 5)}
    edges = [(a, b) for a in range(n) for b in range(a + 1, n)
             if (a, b) not in opposite]
    return CoverSpec(
        universe=[list(e) for e in edges],
        parts=[],
        candidates=[[list(e) for e in k] for k in cliques_of(n, edges)],
        exact=True,
        title="the clique partition number of the octahedron",
    )
