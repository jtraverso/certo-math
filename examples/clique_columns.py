"""An LP over every clique of a graph, without listing the cliques.

The fractional clique partition number of a graph's edges is

    min  sum_Q x_Q   s.t.   sum_{Q containing e} x_Q = 1  for every edge e,
                            x >= 0,  Q ranging over EVERY clique

and "every clique" is the problem: a graph on thirty vertices can have
thousands, a denser one millions. `certo columns` solves the LP over a few of
them, generated as they are needed, and proves the rest would not help:

    $ certo columns examples/clique_columns.py
    SATISFIABLE  [sat]
      EXACT optimum over every clique: 3 (partition). 13 columns generated
      in 1 rounds; a pricing search of 16 nodes finds no clique with
      positive reduced cost
      certificate: clique_lp (no solver needed)

WHAT MAKES IT THE OPTIMUM OVER ALL CLIQUES. The certificate holds the exact
dual `z` of every edge row, and the claim that no clique has positive reduced
cost against it. That claim is decided by an exact search over the cliques
with a pruning bound, and `certo verify` runs the same search again rather
than believing it. Weak duality does the rest.

The graph is the 3-sun: a triangle 0-1-2, with a vertex on each side joined
to that side's two ends. Its nine edges split into the three outer triangles,
and the LP says no fractional combination of cliques does better -- here the
fractional optimum is also the integer one, and the certificate is what says
the first; the three triangles are what say the second. `packing()` asks the
other question the same machinery answers: the most edges covered, minus one
per clique, by cliques of three or more.
"""
from certo import CliqueLPSpec

SUN = [(0, 1), (1, 2), (0, 2),
       (0, 3), (1, 3),
       (1, 4), (2, 4),
       (0, 5), (2, 5)]


def spec():
    return CliqueLPSpec(edges=SUN, problem="partition",
                        weight={"constant": 1}, min_size=2,
                        title="fractional clique partition of the 3-sun")


def packing():
    return CliqueLPSpec(edges=SUN, problem="packing",
                        weight={"edges": 1, "constant": -1}, min_size=3,
                        title="edges covered minus cliques used, the 3-sun")
