"""assign: pages to the hosts each may use, and why no more fit.

Six pages, three hosts with capacities 2, 1 and 2. Pages p1-p4 may only go
to a or b, which hold three between them -- so one of those four cannot be
placed, whatever the rest do. The engine places five and names the reason:
the Hall set U = {a, b} has capacity 3, and two pages (p5, p6) are not
confined to it, so no assignment places more than 3 + 2 = 5. The target of
six is REFUTED with that bottleneck; checking it is counting.

    certo assign examples/assignment_hall.py
    certo verify out/assignment.json
"""
from certo import AssignmentSpec


def spec():
    return AssignmentSpec(
        title="six pages, three hosts",
        items=["p1", "p2", "p3", "p4", "p5", "p6"],
        allowed={"p1": ["a"], "p2": ["a", "b"], "p3": ["b"], "p4": ["a", "b"],
                 "p5": ["b", "c"], "p6": ["c"]},
        capacities={"a": 2, "b": 1, "c": 2},
        target=6,
    )
