"""Roles moved, the graph kept: a vertex relabelling that is an automorphism.

A user exchanged vertices between roles T, S and Q of one graph and wrote
`q' = q` -- a scalar identity, which says nothing about whether the graph
under the new roles is the same graph with the same structure. What says it
is a permutation `sigma` of the vertices that maps the edge set ONTO itself
and each old role onto its new one: then every property of the roles
transports, because the new configuration is the old one renamed.

`check(edges, vertices, roles, roles_after, mapping, properties)` decides
exactly that, and each declared property on both sides as well, so a reader
sees the property and not only the argument for it:

    ("independent", R)                  no edge inside R
    ("clique", R)                       every pair in R is an edge
    ("disjoint", R1, R2)                no vertex in both
    ("complete_to", R1, R2)             every u in R1, v in R2, u != v, adjacent
    ("anticomplete_to", R1, R2)         no edge between R1 and R2
    ("neighbourhood_within", R, [R...]) every neighbour of R lies in the union
"""
from __future__ import annotations

from .i18n import t

PROPERTIES = ("independent", "clique", "disjoint", "complete_to",
              "anticomplete_to", "neighbourhood_within")


class NotRoles(ValueError):
    """Raised with what is wrong with the spec."""


def _key(v):
    return str(v)


def edge_set(edges) -> set:
    out = set()
    for e in edges:
        a, b = list(e)
        if _key(a) == _key(b):
            raise NotRoles(t("roles.loop", v=str(a)))
        out.add(frozenset((_key(a), _key(b))))
    return out


def prop_holds(prop, roles, E, adj) -> bool:
    kind = prop[0]
    R = lambda n: set(roles.get(n, ()))  # noqa: E731
    if kind == "independent":
        A = R(prop[1])
        return not any(frozenset((u, v)) in E for u in A for v in A if u < v)
    if kind == "clique":
        A = R(prop[1])
        return all(frozenset((u, v)) in E for u in A for v in A if u < v)
    if kind == "disjoint":
        return not (R(prop[1]) & R(prop[2]))
    if kind == "complete_to":
        return all(frozenset((u, v)) in E for u in R(prop[1]) for v in R(prop[2]) if u != v)
    if kind == "anticomplete_to":
        return not any(frozenset((u, v)) in E for u in R(prop[1]) for v in R(prop[2]) if u != v)
    if kind == "neighbourhood_within":
        allowed = set().union(*[R(n) for n in prop[2]]) if prop[2] else set()
        return all(adj.get(u, set()) <= allowed for u in R(prop[1]))
    raise NotRoles(t("roles.bad_property", kind=str(kind), known=", ".join(PROPERTIES)))


def normalise(edges, vertices, roles, roles_after, mapping, properties):
    E = edge_set(edges)
    V = {_key(v) for v in (vertices or [])}
    for e in E:
        V |= set(e)
    roles = {str(n): sorted({_key(v) for v in vs}) for n, vs in (roles or {}).items()}
    for vs in roles.values():
        V |= set(vs)
    after = None if roles_after is None else {
        str(n): sorted({_key(v) for v in vs}) for n, vs in roles_after.items()}
    if after is not None:
        if set(after) != set(roles):
            raise NotRoles(t("roles.role_names"))
        for vs in after.values():
            V |= set(vs)
    sigma = None if mapping is None else {_key(a): _key(b) for a, b in dict(mapping).items()}
    props = []
    for pr in properties or []:
        pr = list(pr)
        if not pr or pr[0] not in PROPERTIES:
            raise NotRoles(t("roles.bad_property", kind=str(pr[:1]), known=", ".join(PROPERTIES)))
        if pr[0] == "neighbourhood_within":
            pr = [pr[0], str(pr[1]), [str(x) for x in pr[2]]]
        else:
            pr = [pr[0]] + [str(x) for x in pr[1:]]
        props.append(pr)
    return E, sorted(V), roles, after, sigma, props


def find_mapping(E, V, roles, after, max_nodes=2_000_000):
    """An automorphism sending each role onto its new self, or None -- a
    backtracking search of certo's own (no networkx), pruned by role labels
    and degrees, and checked below like any supplied mapping. Exhaustive
    within `max_nodes`; past it, None says "not found", not "none exists"."""
    adj = {v: set() for v in V}
    for e in E:
        a, b = tuple(e)
        adj[a].add(b)
        adj[b].add(a)

    def label(rs, v):
        return tuple(sorted(n for n, vs in rs.items() if v in vs))

    src = {v: (label(roles, v), len(adj[v])) for v in V}
    dst = {v: (label(after, v), len(adj[v])) for v in V}
    if sorted(src.values()) != sorted(dst.values()):
        return None
    order = sorted(V, key=lambda v: (sum(1 for w in V if src[w] == src[v]), -len(adj[v]), v))
    sigma, used, nodes = {}, set(), [0]

    def extend(k):
        if k == len(order):
            return True
        v = order[k]
        for w in V:
            nodes[0] += 1
            if nodes[0] > max_nodes:
                return False
            if w in used or dst[w] != src[v]:
                continue
            if any((sigma[u] in adj[w]) != (u in adj[v]) for u in sigma):
                continue
            sigma[v] = w
            used.add(w)
            if extend(k + 1):
                return True
            del sigma[v]
            used.discard(w)
        return False

    return dict(sigma) if extend(0) else None


def check(E, V, roles, after, sigma, props) -> dict:
    """Every part of the claim, as data."""
    adj = {}
    for e in E:
        a, b = tuple(e)
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    bijective = (sigma is not None and set(sigma) == set(V)
                 and set(sigma.values()) == set(V))
    image = {frozenset(sigma[x] for x in e) for e in E} if bijective else set()
    automorphism = bijective and image == E
    moved = ({n: sorted(sigma[v] for v in vs) for n, vs in roles.items()}
             if bijective else None)
    onto = bijective and after is not None and moved == after
    results = [{"property": p, "before": prop_holds(p, roles, E, adj),
                "after": prop_holds(p, after or {}, E, adj) if after is not None else None}
               for p in props]
    return {"bijective": bijective, "automorphism": automorphism,
            "roles_onto": onto, "lost_edges": len(E - image) if bijective else None,
            "properties": results}
