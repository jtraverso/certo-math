"""Does one exist? And when it does not, the refutation that says so.

certo can say "here is an exact cover, and here is why it is one". It could
not say the other thing, which in a write-up is often the interesting half:

    the 6-cycle has all degrees even and an edge count divisible by three,
    and it has NO triangle decomposition

A sentence like that is a NON-EXISTENCE over a finite domain, and the honest
artefact for it is a refutation, not an absence. "I looked and found nothing"
is a report about a search; "here is a proof that the search could not have
found anything" is a certificate, and the difference is the whole project.

The encoding is small enough to read. One boolean per candidate part, one
constraint per element of the universe:

    exactly one chosen part contains e          (an exact cover)
    at least one chosen part contains e         (a cover)

and, optionally, a cap on how many parts may be chosen. The cap is a
sequential counter whose auxiliary variables are named after the count they
hold, so a DRAT proof over the formula stays readable. It is not pairwise:
"at most k of n" written pairwise is `C(n, k+1)` clauses, which is 6,724,520
at thirty-five candidates and a cap of six, and that is where it was found.

WHAT COMES BACK is one of two things, and both are certificates:

  * a cover exists -- the model names the parts, and it is handed to the
    ordinary `cover` verifier, which checks it by counting. The SAT solver's
    answer is not trusted; it is a suggestion that gets checked.
  * none exists -- a DRAT refutation of the encoding, checked by unit
    propagation, with no solver and no search.

WHAT IT DOES NOT SAY, and `verify` repeats it: that no cover exists AT ALL.
It says no cover exists USING THESE CANDIDATE PARTS. Those are the same
statement only when the candidates are every part that could have been used,
which is a modelling fact about the spec and not something visible from here.
For a triangle decomposition they coincide, because the candidates are every
triangle of the graph -- and the encoder can build exactly that set, so the
coincidence is arranged rather than hoped for.
"""
from __future__ import annotations

from itertools import combinations

from .i18n import t as _t


class NotEncodable(ValueError):
    """Raised with the reason, because a bare failure helps nobody."""


def triangles_of(n: int, edges) -> list:
    """Every triangle of a graph, as its three edges. The candidate set.

    Built here rather than asked for, because "no triangle decomposition"
    means no decomposition using ANY triangle, and a candidate list somebody
    typed by hand would silently weaken the claim to the ones they thought of.
    """
    present = {tuple(sorted(e)) for e in edges}
    out = []
    for a, b, c in combinations(range(n), 3):
        tri = [(a, b), (a, c), (b, c)]
        if all(tuple(sorted(p)) in present for p in tri):
            out.append([tuple(sorted(p)) for p in tri])
    return out


#: How many cliques `cliques_of` builds before refusing: each one becomes a
#: SAT variable, and the count grows exponentially with the clique number.
MAX_CLIQUES = 200_000


def cliques_of(n: int, edges, min_size: int = 2, max_size=None,
               as_vertices: bool = False) -> list:
    """Every clique of a graph with `min_size <= |K| <= max_size` vertices --
    as its edges (a part of an EDGE partition), or as its vertices.

    `triangles_of` is the case `min_size = max_size = 3`. A clique partition
    of the edges needs EVERY clique as a candidate -- every edge (K2), every
    triangle, every K4 -- or "no partition into at most k cliques" is about
    the cliques somebody listed. Built here for the same reason: the claim
    is only as strong as the candidate set, and this one is complete by
    construction. Every clique, not only the maximal ones: a partition uses
    sub-cliques of maximal cliques all the time.
    """
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        a, b = int(a), int(b)
        if a != b:
            adj[a].add(b)
            adj[b].add(a)
    top = n if max_size is None else int(max_size)
    out = []

    def grow(clique, cands):
        if len(clique) >= min_size:
            if len(out) >= MAX_CLIQUES:
                raise NotEncodable(_t("exists.too_many_cliques", n=MAX_CLIQUES))
            out.append(list(clique) if as_vertices
                       else [tuple(sorted(p)) for p in combinations(clique, 2)])
        if len(clique) == top:
            return
        for v in sorted(cands):
            # only larger vertices: each clique is built once, in order
            grow(clique + [v], {u for u in cands & adj[v] if u > v})

    for v in range(n):
        grow([v], {u for u in adj[v] if u > v})
    return out


#: Bytes a column costs once expanded, measured on CPython 3.12: a dense
#: row of `Fraction` pointers, and a sparse non-zero as a (column, Fraction)
#: pair in a dict. Order-of-magnitude figures, said as such.
DENSE_BYTES_PER_ENTRY = 8
SPARSE_BYTES_PER_NONZERO = 180


def estimate_cliques(n: int, edges, min_size: int = 2, max_size=None,
                     stop_at: int = 10_000_000) -> dict:
    """How big the clique LP over this graph would be, BEFORE building it:
    cliques by size, columns, rows, non-zeros, and the memory a dense and a
    sparse expansion would take -- counted, nothing materialised. A user's
    own expansion of local clique LPs passed 2 GiB before anything said so.

    `stop_at` bounds the count itself: past it the result says `at_least`.
    The advice names the route that never expands: `certo columns` (the
    columns generated by pricing) or the sparse path."""
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        a, b = int(a), int(b)
        if a != b:
            adj[a].add(b)
            adj[b].add(a)
    top = n if max_size is None else int(max_size)
    by_size, total, nonzeros = {}, [0], [0]
    stopped = [False]

    def grow(size, cands):
        if stopped[0]:
            return
        if size >= min_size:
            by_size[size] = by_size.get(size, 0) + 1
            total[0] += 1
            nonzeros[0] += size * (size - 1) // 2
            if total[0] >= stop_at:
                stopped[0] = True
                return
        if size == top:
            return
        for v in sorted(cands):
            grow(size + 1, {u for u in cands & adj[v] if u > v})
            if stopped[0]:
                return

    for v in range(n):
        grow(1, {u for u in adj[v] if u > v})
        if stopped[0]:
            break
    rows = len({frozenset((int(a), int(b))) for a, b in edges if int(a) != int(b)})
    cols = total[0]
    dense = rows * cols * DENSE_BYTES_PER_ENTRY
    sparse = nonzeros[0] * SPARSE_BYTES_PER_NONZERO
    advice = None
    if dense > 1 << 30:
        advice = _t("exists.estimate.advice_columns", gib=round(dense / (1 << 30), 1))
    elif cols > MAX_CLIQUES:
        advice = _t("exists.estimate.advice_many", n=MAX_CLIQUES)
    return {"cliques_by_size": dict(sorted(by_size.items())), "columns": cols,
            "rows": rows, "nonzeros": nonzeros[0], "at_least": stopped[0],
            "dense_bytes": dense, "sparse_bytes": sparse, "advice": advice}


def encode(universe, candidates, exact=True, max_parts=None, title=""):
    """The cover question as a CNF. One variable per candidate part.

    Returns `(cnf, names)` where `names[i]` is the part variable `i + 1`
    stands for, so a model reads back as a list of parts rather than as a
    list of integers.
    """
    from .cnf import CNF

    universe = [u if isinstance(u, (str, int)) else tuple(u) for u in universe]
    parts = [[e if isinstance(e, (str, int)) else tuple(e) for e in part]
             for part in candidates]
    if not universe:
        raise NotEncodable(_t("exists.empty_universe"))

    seen = set(universe)
    foreign = sorted({str(e) for part in parts for e in part if e not in seen})
    if foreign:
        raise NotEncodable(_t("exists.foreign", n=len(foreign),
                              names=", ".join(foreign[:4])))

    cnf = CNF(title=title)
    var = [cnf.var("part_{}".format(i)) for i in range(len(parts))]

    covering = {e: [] for e in universe}
    for i, part in enumerate(parts):
        for e in part:
            covering[e].append(var[i])

    for e in universe:
        lits = covering[e]
        if not lits:
            # Nothing can cover this element, so the question is settled
            # before the solver starts. Written as two unit clauses on a
            # variable NAMED AFTER THE ELEMENT rather than as the empty
            # clause: an empty clause does not survive a round trip through
            # DIMACS, so the refutation would not have been re-checkable --
            # and this way a reader of the formula sees which element it was.
            u = cnf.var("uncoverable_{}".format(e))
            cnf.add(u)
            cnf.add(-u)
            continue
        if exact:
            cnf.exactly_one(lits)
        else:
            cnf.at_least_one(lits)

    if max_parts is not None:
        if max_parts < 0:
            raise NotEncodable(_t("exists.negative_cap", k=max_parts))
        # At most `max_parts` chosen. A sequential counter, not pairwise: the
        # pairwise form of "at most k" is C(n, k+1) clauses, and 35 candidates
        # with k = 6 is 6,724,520 of them.
        cnf.at_most_k(var, max_parts)

    return cnf, parts
