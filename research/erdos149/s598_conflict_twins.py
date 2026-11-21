"""S598: exact true-twin quotient of strong-conflict demand edges.

Every independent-set palette remains valid through quotient/pullback.
Physical edges remain fixed; equal closed conflict neighborhoods and equal
root-marker signatures allow merging edge demands by weight sum.
"""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product


def edge(u, v):
    u, v = str(u), str(v)
    assert u != v
    return tuple(sorted((u, v)))


def quotient(data, support=None):
    m = {str(v): F(str(w)) for v, w in data["masses"].items()}
    E = sorted({edge(*f) for f in data["edges"]})
    adj = {v: set() for v in m}
    incident = defaultdict(set)
    for i, (u, v) in enumerate(E):
        adj[u].add(v);adj[v].add(u)
        incident[u].add(i);incident[v].add(i)
    conflicts = []
    for u, v in E:
        C = {u, v} | adj[u] | adj[v]
        conflicts.append(frozenset(j for z in C for j in incident[z]))
    marks = [(int(data["s"] in e), int(data["t"] in e)) for e in E]
    weights = [m[u] * m[v] for u, v in E]
    S = frozenset(range(len(E)) if support is None else support)
    groups = defaultdict(list)
    for i in sorted(S):
        groups[(marks[i], conflicts[i] & S)].append(i)
    classes = sorted((tuple(ids) for ids in groups.values()), key=lambda v: v[0])
    ix = {i: k for k, ids in enumerate(classes) for i in ids}
    assert len(ix) == len(S)
    qconf = [frozenset(ix[j] for j in conflicts[ids[0]] & S) for ids in classes]
    qweights = [sum((weights[i] for i in ids), F()) for ids in classes]
    qmarks = [marks[ids[0]] for ids in classes]
    assert all(k in qconf[k] for k in range(len(classes)))
    assert all((j in qconf[i]) == (i in qconf[j])
               for i in range(len(classes)) for j in range(len(classes)))
    return {"edges": E, "old_weights": weights, "support": S,
            "classes": classes, "ix": ix, "qconf": qconf,
            "qweights": qweights, "qmarks": qmarks}


def project(palette, q):
    edge_to_type = {q["edges"][i]: q["ix"][i] for i in q["support"]}
    answer = []
    for c in palette:
        T = [edge_to_type[edge(*e)] for e in c["edges"]]
        assert len(T) == len(set(T)), "two true twins cannot co-occur"
        answer.append({"width": str(c["width"]), "types": sorted(T)})
    return answer


def verify_quotient(palette, q, K=F(5, 4)):
    got = [F() for _ in q["qweights"]]
    J = F();total = F()
    for c in palette:
        width = F(str(c["width"]))
        T = list(c["types"])
        assert width > 0 and len(T) == len(set(T))
        assert all(j not in q["qconf"][i]
                   for k, i in enumerate(T) for j in T[k + 1:])
        for i in T:got[i] += width
        if any(q["qmarks"][i][0] for i in T) and any(q["qmarks"][i][1] for i in T):
            J += width
        total += width
    assert got == q["qweights"] and total == K
    return J


def lift(palette, q):
    answer = []
    for c in palette:
        choices = [[(i, q["old_weights"][i] / q["qweights"][k])
                    for i in q["classes"][k]] for k in c["types"]]
        for selection in product(*choices):
            factor = F(1)
            for _, ratio in selection:factor *= ratio
            answer.append({"width": str(F(str(c["width"])) * factor),
                           "edges": [list(q["edges"][i]) for i, _ in selection]})
    return answer
