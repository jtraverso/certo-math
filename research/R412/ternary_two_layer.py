"""Exhaust the 256 triangle families supported on a 2x2x2 tripartite gadget.

Certo proves the rational fractional optimum of each packing LP.
An explicit brute-force integer witness is computed independently.
Scope: triangle-only sources, with no intra-base edges.
"""
from itertools import product
from fractions import Fraction
from certo import LPSpec, Outcome, DomainSpec
from certo.engines import lp

TRIANGLES = list(product((0, 1), repeat=3))
EDGES = sorted({(i, j, t[i], t[j]) for t in TRIANGLES
                for i, j in ((0, 1), (0, 2), (1, 2))})
INCIDENCE = {e: tuple(k for k, t in enumerate(TRIANGLES)
                 if t[e[0]] == e[2] and t[e[1]] == e[3]) for e in EDGES}

def integral_witness(mask):
    ids = [i for i in range(8) if (mask >> i) & 1]
    best = ()
    for v in range(1 << len(ids)):
        chosen = tuple(ids[j] for j in range(len(ids)) if (v >> j) & 1)
        if len(chosen) <= len(best):
            continue
        if all(sum(k in INCIDENCE[e] for k in chosen) <= 1 for e in EDGES):
            best = chosen
    return best

def packing(mask):
    ids = [i for i in range(8) if (mask >> i) & 1]
    s = LPSpec(sense="max", title=f"two-clones-{mask}")
    for i in ids:
        s.variable(f"t{i}", 0, 1)
    s.objective({f"t{i}": 1 for i in ids})
    for j, e in enumerate(EDGES):
        co = {f"t{i}": 1 for i in INCIDENCE[e] if i in ids}
        if co:
            s.constraint(co, "<=", 1, name=f"edge_{j}")
    return s

def check(mask):
    if mask == 0:
        return Outcome(ok=True, detail="both optima are 0")
    integral = integral_witness(mask)
    result = lp.opt(packing(mask))
    if not result.meta.get("exact") or not result.certificate:
        return Outcome(ok=None, detail=f"LP not certified mask={mask}")
    fractional = Fraction(str(result.meta["objective"]))
    return Outcome(ok=(fractional == len(integral)),
                   cert=result.certificate,
                   detail=f"LP {fractional}; integer {len(integral)}; witness {integral}")

def spec():
    return DomainSpec(
        items=range(1,256),
        predicate=check,
        key=lambda mask: f"mask-{mask:03d}",
        title="All nonempty triangle families on K(2,2,2) have integral maximum packing")
