"""cover --maximum: nu(G) by SAT, with a proof that one more is impossible.

The octahedron's triangles as a hypergraph on its edges: the most
edge-disjoint triangles is a maximum PACKING of it. A SAT search finds four;
certo's own encoding of "at least five, pairwise disjoint" is refuted by a
DRUP proof that `verify` re-encodes and checks by unit propagation
(`sat_optimum`). The same route gives a minimum cover or partition past the
62 elements the recurrence over masks can index:

    certo cover examples/triangle_cover_sat.py --maximum
"""
from itertools import combinations

from certo.hypergraph import triangle_packing


def spec():
    edges = [(a, b) for a, b in combinations(range(6), 2)
             if (a, b) not in {(0, 1), (2, 3), (4, 5)}]
    return triangle_packing(6, edges)
