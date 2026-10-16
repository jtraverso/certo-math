"""roles: exchange roles on one graph without changing the graph.

The 4-cycle 0-1-2-3-0 with T = {0}, S = {1, 3}, Q = {2}, and the roles moved
to T = {1}, S = {0, 2}, Q = {3}. That is not a scalar identity: it is a
permutation of the vertices that maps the edge set onto itself and each old
role onto its new one -- found by VF2 here, checked by certo -- with every
declared property checked before and after.

    certo roles examples/roles_square.py
    certo verify out/roles_square.json
"""
from certo import RoleSpec


def spec():
    return RoleSpec(
        title="T, S, Q rotated on the 4-cycle",
        edges=[(0, 1), (1, 2), (2, 3), (3, 0)],
        roles={"T": [0], "S": [1, 3], "Q": [2]},
        roles_after={"T": [1], "S": [0, 2], "Q": [3]},
        properties=[("independent", "S"), ("complete_to", "T", "S"),
                    ("neighbourhood_within", "Q", ["S"])],
    )
