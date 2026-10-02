"""Clique cuts of the conflict graph: derived here, re-derived by `verify`.

A user's branch and bound stalled on a symmetric instance -- 18 497 nodes in
600 s, no verdict -- and one inequality closed it: no two items sharing a
resource of capacity one, written over every such group at once. That is a
CLIQUE CUT of the conflict graph, and it is the cheapest valid inequality
there is to check.

  CONFLICT   binaries x_i, x_j conflict when some row  sum a_k x_k <= b
             with every a_k >= 0 has a_i + a_j > b: with both at 1 the row
             fails whatever the others are, since x >= 0.
  CUT        for a clique K of conflicts, sum_{i in K} x_i <= 1 holds at
             every INTEGER point: at most one of them can be 1.

The cut LP is a relaxation of the INTEGER program, not of its LP: its optimum
bounds the integer optimum and may cut off fractional points the original LP
allows. The certificate says so, and `verify` re-derives every pair of every
cut from the row in the same payload that forces it -- a cut whose pair no
row forces is a constraint added to make the bound smaller, and is refused.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

#: How many cliques are added at most. Maximal cliques can be exponentially
#: many; a cap that is reported is better than a run that never ends.
MAX_CUTS = 200


def _binary_columns(var_names, kinds, A, b):
    """Columns that are 0/1 at every integer point: `binary`, or `integer`
    with a bound row `x <= 1` in the system."""
    out = set()
    for j, v in enumerate(var_names):
        kind = kinds.get(v, "continuous")
        if kind == "binary":
            out.add(j)
        elif kind == "integer":
            for row, rhs in zip(A, b):
                if row[j] == 1 and rhs <= 1 and all(
                        x == 0 for k, x in enumerate(row) if k != j):
                    out.add(j)
                    break
    return out


def conflicts(A, b, names, var_names, kinds, skip=()):
    """`{(i, j): row name}` for every conflicting pair of 0/1 columns."""
    zero_one = _binary_columns(var_names, kinds, A, b)
    out = {}
    for row, rhs, name in zip(A, b, names):
        if name in skip or any(a < 0 for a in row):
            continue
        cols = [j for j in sorted(zero_one) if row[j] > 0]
        for i, j in combinations(cols, 2):
            if row[i] + row[j] > rhs:
                out.setdefault((i, j), name)
    return out


def maximal_cliques(n, pairs, limit=MAX_CUTS) -> list:
    """Bron-Kerbosch with a pivot, in a fixed order; at most `limit`."""
    adj = {i: set() for i in range(n)}
    for i, j in pairs:
        adj[i].add(j)
        adj[j].add(i)
    out = []

    def grow(R, P, X):
        if len(out) >= limit:
            return
        if not P and not X:
            if len(R) >= 2:
                out.append(sorted(R))
            return
        pivot = max(P | X, key=lambda u: (len(adj[u] & P), -u))
        for v in sorted(P - adj[pivot]):
            grow(R | {v}, P & adj[v], X & adj[v])
            P = P - {v}
            X = X | {v}

    grow(set(), {i for i in range(n) if adj[i]}, set())
    return out


def clique_cuts(spec, limit=MAX_CUTS):
    """`(spec with the cuts, cuts)` for an LPSpec. Each cut records, for
    every pair it covers, the row that forces the conflict."""
    from copy import deepcopy

    A, b, _c, names = spec.as_leq_system()
    var_names = list(spec.var_names)
    kinds = {v: spec.kind_of(v) for v in var_names}
    pairs = conflicts(A, b, names, var_names, kinds)
    cliques = maximal_cliques(len(var_names), pairs, limit)
    out = deepcopy(spec)
    cuts = []
    taken = {n for n, *_r in spec.cons}
    for k, K in enumerate(cliques):
        name = "cut_clique_{}".format(k)
        while name in taken:
            name += "_"
        taken.add(name)
        out.constraint({var_names[j]: 1 for j in K}, "<=", 1, name=name)
        cuts.append({"name": name, "vars": [var_names[j] for j in K],
                     "why": {"{}|{}".format(var_names[i], var_names[j]):
                             pairs[(i, j)] for i, j in combinations(K, 2)}})
    return out, cuts


def check(payload, A, b) -> list:
    """Every cut of an `lp_dual` payload, re-derived. Returns the names of
    the cuts that do not hold."""
    names = list(payload.get("names") or [])
    var_names = list(payload.get("var_names") or [])
    kinds = payload.get("kinds") or {}
    index = {v: j for j, v in enumerate(var_names)}
    cut_names = [c.get("name") for c in payload.get("cuts") or []]
    if len(set(cut_names)) != len(cut_names):
        return ["duplicate"]
    rows = {n: i for i, n in enumerate(names)}
    # The rows a conflict may come from are the program's own, never a cut.
    original = [i for i, n in enumerate(names) if n not in set(cut_names)]
    zero_one = _binary_columns(var_names, kinds, [A[i] for i in original],
                               [b[i] for i in original])
    bad = []
    for cut in payload.get("cuts") or []:
        try:
            r = rows[cut["name"]]
            K = [index[v] for v in cut["vars"]]
        except (KeyError, TypeError):
            bad.append(str(cut.get("name")))
            continue
        want = [Fraction(1) if j in set(K) else Fraction(0)
                for j in range(len(var_names))]
        ok = (len(set(K)) == len(K) >= 2 and A[r] == want and b[r] == 1
              and names.count(cut["name"]) == 1
              and all(j in zero_one for j in K))
        for i, j in combinations(sorted(K), 2):
            key = "{}|{}".format(var_names[i], var_names[j])
            alt = "{}|{}".format(var_names[j], var_names[i])
            w = (cut.get("why") or {}).get(key) or (cut.get("why") or {}).get(alt)
            if w not in rows or w in set(cut_names) or names.count(w) != 1:
                ok = False
                break
            row, rhs = A[rows[w]], b[rows[w]]
            if any(a < 0 for a in row) or not row[i] + row[j] > rhs:
                ok = False
                break
        if not ok:
            bad.append(str(cut.get("name")))
    return bad
