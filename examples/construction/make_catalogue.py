"""The ENUMERATOR for `construction_split.json`'s catalogue -- not part of the
proof.

It lists the split graphs up to N vertices (no induced 2K2, C4 or C5), one
representative per isomorphism class, and for every one-vertex extension of a
representative either the isomorphism to a representative or the forbidden
induced subgraph it contains, with a triangle packing and cover for each
representative. `certo compose` does not trust any of it: the checker
GENERATES the extensions itself and checks each map, exclusion and witness,
so an extension this script forgot invalidates the catalogue.

    python examples/construction/make_catalogue.py 4 > catalogue.json
"""
from __future__ import annotations

import json
import sys
from itertools import combinations, permutations

FORBIDDEN = {
    "2K2": (4, {(0, 1), (2, 3)}),
    "C4": (4, {(0, 1), (1, 2), (2, 3), (0, 3)}),
    "C5": (5, {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}),
}


def norm(E):
    return {(min(a, b), max(a, b)) for a, b in E}


def canon(n, E):
    best = None
    for p in permutations(range(n)):
        key = tuple(sorted(norm((p[a], p[b]) for a, b in E)))
        if best is None or key < best:
            best = key
    return best


def iso_map(n, E, F):
    """A permutation p with p(E) = F, or None."""
    F = norm(F)
    for p in permutations(range(n)):
        if norm((p[a], p[b]) for a, b in E) == F:
            return list(p)
    return None


def forbidden_in(n, E):
    for name, (k, F) in FORBIDDEN.items():
        if k > n:
            continue
        for at in permutations(range(n), k):
            if all(((min(at[i], at[j]), max(at[i], at[j])) in E) == ((i, j) in F)
                   for i in range(k) for j in range(i + 1, k)):
                return name, list(at)
    return None


def triangles(n, E):
    return [t for t in combinations(range(n), 3)
            if all((a, b) in E for a, b in combinations(t, 2))]


def witness(n, E):
    tris = triangles(n, E)
    best = []
    for k in range(len(tris), 0, -1):
        for pack in combinations(tris, k):
            used = [e for t in pack for e in combinations(t, 2)]
            if len(used) == len(set(used)):
                best = list(pack)
                break
        if best:
            break
    edges = sorted(E)
    for k in range(0, len(edges) + 1):
        for cover in combinations(edges, k):
            if all(any(e in cover for e in combinations(t, 2)) for t in tris):
                return {"packing": [list(t) for t in best],
                        "cover": [list(e) for e in cover]}
    raise AssertionError


def main(N):
    reps = {}                      # name -> (n, E)
    by_canon = {}
    order = []
    for n in range(1, N + 1):
        for k in range(n * (n - 1) // 2 + 1):
            for E in combinations(list(combinations(range(n), 2)), k):
                E = set(E)
                c = canon(n, E)
                if (n, c) in by_canon or forbidden_in(n, E):
                    continue
                name = "R{}_{}".format(n, len([r for r in reps if r.startswith("R{}_".format(n))]))
                by_canon[(n, c)] = name
                reps[name] = (n, E)
                order.append(name)
    exts = []
    for name in order:
        n, E = reps[name]
        if n >= N:
            continue
        for k in range(n + 1):
            for S in combinations(range(n), k):
                F = set(E) | {(s, n) for s in S}
                bad = forbidden_in(n + 1, F)
                if bad:
                    exts.append({"from": name, "neighbours": list(S),
                                 "excluded": bad[0], "at": bad[1]})
                    continue
                to = by_canon[(n + 1, canon(n + 1, F))]
                exts.append({"from": name, "neighbours": list(S), "to": to,
                             "map": iso_map(n + 1, F, reps[to][1])})
    return {
        "id": "split_catalogue", "contract": "catalogue", "max_vertices": N,
        "forbidden": {k: {"n": n, "edges": [list(e) for e in sorted(F)]}
                      for k, (n, F) in FORBIDDEN.items()},
        "representatives": {k: {"n": reps[k][0], "edges": [list(e) for e in sorted(reps[k][1])]}
                            for k in order},
        "extensions": exts,
        "ratio": 2,
        "witnesses": {k: witness(*reps[k]) for k in order},
    }


if __name__ == "__main__":
    print(json.dumps(main(int(sys.argv[1]) if len(sys.argv) > 1 else 4), indent=1))
