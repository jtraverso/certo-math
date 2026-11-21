"""S598: exact rational proof replay of conflict-type quotient.

Uses static 18-vertex 3-connected original H certificate from S597.
Counts physical induced matchings and checks projection and lift exactly.
"""
from s598_conflict_twins import quotient, project, verify_quotient, lift
from s597_verify_static_palettes import decode
from fractions import Fraction as F
import json


def edge(a, b):
    return tuple(sorted((a, b)))


def check_physical(data, palette):
    E = {edge(*f) for f in data["edges"]}
    m = {v: F(str(w)) for v, w in data["masses"].items()}
    got = {e: F() for e in E}
    total = F();J = F()
    for c in palette:
        w = F(str(c["width"]))
        M = [edge(*e) for e in c["edges"]]
        assert w > 0 and len(M) == len(set(M)) and all(e in E for e in M)
        for i, e in enumerate(M):
            for f in M[i + 1:]:
                assert len(set(e) | set(f)) == 4
                assert all(edge(u, v) not in E for u in e for v in f)
        for e in M:got[e] += w
        total += w
        if any(data["s"] in e for e in M) and any(data["t"] in e for e in M):
            J += w
    assert all(got[e] == m[e[0]] * m[e[1]] for e in E)
    assert total == F(5, 4)
    return J


data = decode("core18")
q = quotient(data)
assert len(q["edges"]) == 39 and len(q["classes"]) == 33
assert sum(len(c) - 1 for c in q["classes"]) == 6
original = check_physical(data, data["palette"])
compressed = project(data["palette"], q)
assert verify_quotient(compressed, q) == original == F(133, 200)
pulled = lift(compressed, q)
assert check_physical(data, pulled) == original
print(json.dumps({"status": "PASS", "physical_graph": "18 vertices, 39 edges",
                  "quotient_demand_types": 33, "merged": 6,
                  "root_overlap_J": str(original),
                  "original_palette_colors": len(data["palette"]),
                  "lifted_physical_palette_colors": len(pulled),
                  "scope": "exact one-instance check of universal quotient theorem"}))
