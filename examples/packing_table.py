"""cover --maximum: the most pairwise disjoint candidates, by a table.

The octahedron's triangles, as a packing on its 12 edges: the most
edge-disjoint triangles. Up to 62 elements the packing recurrence over masks
settles it with no solver at all --

    g(M) = max( g(M - {e}),  1 + g(M - C) for C containing e inside M )

where e is the lowest element left: either no chosen triangle uses it, or
exactly one does. Every state's value is in the certificate, and `verify`
checks each against its children. (Past 62 elements, or with --sat, the same
optimum comes by SAT with a DRUP proof: examples/triangle_cover_sat.py.)

    certo cover examples/packing_table.py --maximum
    certo verify out/packing_table.json
"""
from itertools import combinations

from certo.hypergraph import triangle_packing


def spec():
    edges = [(a, b) for a, b in combinations(range(6), 2)
             if (a, b) not in {(0, 1), (2, 3), (4, 5)}]
    return triangle_packing(6, edges, title="the octahedron's triangle packing, by table")
