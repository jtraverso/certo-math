"""exists: no partition of the octahedron's edges into three cliques.

The octahedron K(2,2,2) has 12 edges and 8 triangles, and no K4. Four
edge-disjoint triangles cover it -- alternate faces -- so its clique partition
number is at most 4. Is it 3?

The claim "no partition into at most 3 cliques" is only as strong as the
candidate set: a list of the cliques somebody thought of would prove less.
`cliques_of` builds EVERY clique (every edge, every triangle), so the
candidates are complete by construction, and the DRAT refutation is about the
octahedron and not about a list.

    certo exists examples/clique_partition.py --max-parts 3
    certo verify out/clique_partition.json
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
        title="the octahedron's edges in at most 3 cliques",
    )
