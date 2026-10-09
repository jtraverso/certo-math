"""Hypergraph matching and transversal, and triangle packing and covering.

A user modelling packing and transversal problems had to generate `.py`
files with JSON inside them, and looked for a hitting set under `cover`,
which partitions into cliques. These are the two problems, said once:

    matching      choose hyperedges, pairwise disjoint, of greatest weight
    transversal   choose vertices meeting every hyperedge, of least weight

and, for a graph, the two triangle numbers behind Tuza's conjecture:

    nu(G)   the most edge-disjoint triangles   -- a matching in the
            hypergraph whose vertices are the edges and whose hyperedges
            are the triangles;
    tau(G)  the fewest edges meeting every triangle -- a transversal of it.

No new engine: a `HypergraphSpec` is the linear program, and the existing
commands answer it with their own certificates --

    certo opt        the fractional value (nu*, tau*) with its exact dual;
    certo mixed --prove-optimal
                     the integer optimum by certified branch and bound;
    certo cover --minimum
                     (a transversal) the minimum by the recurrence over
                     masks, every state checked, solver-free.

It is also a JSON spec: `{"type": "HypergraphSpec", "edges": [[...], ...],
"problem": "transversal"}` runs with nothing executed.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

from .i18n import t as _t

PROBLEMS = ("matching", "transversal")


@dataclass
class HypergraphSpec:
    """Hyperedges (lists of vertices) and the problem asked of them.

        HypergraphSpec(edges=[[1, 2, 3], [3, 4, 5], [1, 5]],
                       problem="transversal")

    `weights`: per hyperedge for a matching, per vertex for a transversal;
    1 each when absent. `vertices` adds vertices no hyperedge names."""

    edges: list
    problem: str = "matching"
    weights: object = None
    vertices: object = None
    title: str = ""

    def _check(self):
        if self.problem not in PROBLEMS:
            raise ValueError(_t("hypergraph.bad_problem", problem=self.problem,
                                known=", ".join(PROBLEMS)))
        if not self.edges:
            raise ValueError(_t("hypergraph.no_edges"))

    def vertex_list(self) -> list:
        seen, out = set(), []
        for v in list(self.vertices or []) + [v for e in self.edges for v in e]:
            k = _label(v)
            if k not in seen:
                seen.add(k)
                out.append(v)
        return out

    def to_lp(self, integer: bool = True):
        """The 0-1 program (binary variables), or its relaxation."""
        from .spec import LPSpec

        self._check()
        kind = "binary" if integer else "continuous"
        w = dict(self.weights or {})
        if self.problem == "matching":
            lp = LPSpec(sense="max", title=self.title or "hypergraph matching")
            names = ["e{}".format(i) for i in range(len(self.edges))]
            for i, n in enumerate(names):
                lp.variable(n, 0, 1, kind=kind)
            lp.objective({n: w.get(i, w.get(n, 1)) for i, n in enumerate(names)})
            for v in self.vertex_list():
                row = {names[i]: 1 for i, e in enumerate(self.edges)
                       if _label(v) in {_label(x) for x in e}}
                if row:
                    lp.constraint(row, "<=", 1, name="v:" + _label(v))
            return lp
        lp = LPSpec(sense="min", title=self.title or "hypergraph transversal")
        verts = self.vertex_list()
        names = {_label(v): "v:" + _label(v) for v in verts}
        for v in verts:
            lp.variable(names[_label(v)], 0, 1, kind=kind)
        lp.objective({names[_label(v)]: w.get(_label(v), 1) for v in verts})
        for i, e in enumerate(self.edges):
            lp.constraint({names[_label(v)]: 1 for v in e}, ">=", 1,
                          name="e{}".format(i))
        return lp

    def to_cover(self):
        """A transversal as a COVER: the universe is the hyperedges, each
        vertex the set of hyperedges it meets -- for `cover --minimum`."""
        from .spec import CoverSpec

        self._check()
        if self.problem != "transversal":
            raise ValueError(_t("hypergraph.cover_needs_transversal"))
        if self.weights:
            raise ValueError(_t("hypergraph.cover_unweighted"))
        universe = ["e{}".format(i) for i in range(len(self.edges))]
        cands = []
        for v in self.vertex_list():
            hit = ["e{}".format(i) for i, e in enumerate(self.edges)
                   if _label(v) in {_label(x) for x in e}]
            if hit:
                cands.append(hit)
        return CoverSpec(universe=universe, parts=[], candidates=cands,
                         exact=False, title=self.title or "hypergraph transversal")


def _label(v) -> str:
    if isinstance(v, (list, tuple)):
        return "-".join(map(str, sorted(v)))
    return str(v)


def triangles(n: int, edges) -> list:
    """Every triangle of a graph, as its three edges `"a-b"`."""
    present = {tuple(sorted(map(int, e))) for e in edges}
    out = []
    for a, b, c in combinations(range(n), 3):
        tri = [(a, b), (a, c), (b, c)]
        if all(p in present for p in tri):
            out.append(["{}-{}".format(*p) for p in tri])
    return out


def triangle_packing(n: int, edges, title="") -> HypergraphSpec:
    """nu(G): the most edge-disjoint triangles."""
    return HypergraphSpec(edges=triangles(n, edges), problem="matching",
                          vertices=["{}-{}".format(*sorted(map(int, e))) for e in edges],
                          title=title or "triangle packing nu(G)")


def triangle_cover(n: int, edges, title="") -> HypergraphSpec:
    """tau(G): the fewest edges meeting every triangle."""
    return HypergraphSpec(edges=triangles(n, edges), problem="transversal",
                          vertices=["{}-{}".format(*sorted(map(int, e))) for e in edges],
                          title=title or "triangle cover tau(G)")
