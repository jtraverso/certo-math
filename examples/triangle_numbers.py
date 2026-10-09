"""Triangle packing and covering of a graph: nu(G) and tau(G), certified.

The octahedron K(2,2,2): its 8 triangles, the hypergraph whose vertices are
its 12 edges. nu(G), the most edge-disjoint triangles, is a MATCHING of that
hypergraph; tau(G), the fewest edges meeting every triangle, a TRANSVERSAL.
Tuza's conjecture is tau <= 2 nu.

    certo opt examples/triangle_numbers.py            # nu* with its dual
    certo mixed examples/triangle_numbers.py --prove-optimal   # nu, by B&B

and `triangle_cover` in place of `triangle_packing` for tau --
`certo cover ... --minimum` proves it by the recurrence over masks.
"""
from certo.hypergraph import triangle_packing


def spec():
    n = 6
    opposite = {(0, 1), (2, 3), (4, 5)}
    edges = [(a, b) for a in range(n) for b in range(a + 1, n)
             if (a, b) not in opposite]
    return triangle_packing(n, edges)
