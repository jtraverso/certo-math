"""solve a DivisibilitySpec: K4's edges by triangles -- over Q yes, over Z no.

Each triangle of K4 taken with weight 1/2 covers every edge exactly once, so
the edge set is a RATIONAL combination of triangles. It is not an INTEGER
one, and the certificate says why: weights on the edges under which every
triangle totals an integer and the whole edge set totals 1/2. certo builds
the incidence matrix (edges by triangles) and runs `solve` over Q and Z:

    certo solve examples/divisibility_triangles.py
    certo verify out/divisibility_triangles.json
"""
from itertools import combinations

from certo import DivisibilitySpec


def spec():
    n = 4
    edges = ["%d%d" % e for e in combinations(range(n), 2)]
    triangles = {"t%d%d%d" % t: ["%d%d" % (t[0], t[1]), "%d%d" % (t[0], t[2]),
                                  "%d%d" % (t[1], t[2])]
                 for t in combinations(range(n), 3)}
    return DivisibilitySpec(title="K4 by triangles", pieces=triangles, target=edges)
