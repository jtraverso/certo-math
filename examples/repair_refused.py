"""cover: a refused repair, sealed as a certificate.

A partition of the edges of a small graph into owners, and a change that
takes an edge from an owner it did not withdraw. The final cover would be
valid -- the edge is in the graph -- and the CHANGE is not: the refusal names
the edge and the owner, and the certificate (`repair_refusal`) is re-checked
by the same rules that accept a repair, so a negative is kept like a
positive.

    certo cover examples/repair_refused.py
    certo verify out/repair_refused.json
"""
from certo import CoverSpec


def spec():
    edges = [(0, 1), (1, 2), (0, 2), (2, 3), (3, 4), (2, 4)]
    before = {"A": [0, 1, 2], "B": [2, 3, 4]}
    return CoverSpec(
        universe=[list(e) for e in edges],
        parts=[],
        cliques=True,
        repair={"before": before,
                "withdraw": ["A"],
                # (2, 3) belongs to B, which is not withdrawn
                "insert": {"A1": [0, 1], "A2": [1, 2], "A3": [0, 2], "C": [2, 3]},
                "balance": 3},
        title="a repair that takes an edge from an owner it kept",
    )
