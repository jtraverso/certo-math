"""Contracts across a construction: the objects, not only the counts.

A cost inequality can be right while the packing it adds reuses a base of
the child, while the cover misses a triangle that comes back, while a
catalogue that "has a witness for every file" is missing a case, while two
local refunds charge the same base. Each certificate certo had checked a
COUNT; none checked that the counts were about the same objects. That was the
user's glue code, and it was where their errors lived.

A `ConstructionSpec` is data: graphs and resources under stable names, and
STEPS, each a contract over those names. `verify` re-derives every step from
the data the certificate carries -- nothing is re-run through the constructor
that proposed it -- and a step can use what an earlier one established.

    lift          resources transported from a child graph to its parent: the
                  final packing and cover REBUILT and checked against the parent
    catalogue     every one-vertex extension of every representative mapped to
                  a representative by an explicit isomorphism, or excluded by
                  a forbidden induced subgraph -- generated here, not listed by
                  the enumerator; one omitted extension invalidates it
    credit        a common cut distribution, owners partitioning the bases,
                  every local state declared, local covers checked, the global
                  sum exact -- with no LP re-solved
    hosting       an assignment of bases to hosts with a matching per host: no
                  resource (spoke) used twice on one host
    glue          blocks joined at ports: every port consumed exactly once,
                  every interior with exactly one owner, a perforated cover
                  never taken for a closed one, and a joint value only from a
                  global witness -- never a sum of local minima
    certificate   another certificate, embedded, verified again, and tied by
                  fingerprint to the obligation it was meant to discharge
    cegis         a synthesised parameter BACKED by a resource another step
                  certified: a scalar that pays is not yet a page that exists
    charts        an atlas: selectors whose union covers a box (the leaves
                  recomputed), each chart's sign certificates tied to it
    substitution  a change of coordinates with a denominator: the pulled-back
                  polynomial, the denominator's sign, the inverse map and the
                  inclusion of the old domain, all checked

WHAT A CONSTRUCTION ESTABLISHES is the conjunction of its steps about THIS
data. A `lift` checked on one parent graph is a fact about that graph, not a
rule for a family; that the data is the graph of your theorem is yours, and
the report says so every time.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

from .i18n import t

CONTRACTS = ("lift", "catalogue", "credit", "hosting", "glue", "certificate",
             "cegis", "charts", "substitution")

#: degrees of a step, strongest first
DEGREES = ("complete", "with_solver", "relative")


class NotAConstruction(ValueError):
    """The data cannot be read as the contract it names; says why."""


# --- small readers -----------------------------------------------------------

def _q(v, what="") -> Fraction:
    """An exact rational: an int, a Fraction, or a string like `"3/4"`."""
    if isinstance(v, bool) or isinstance(v, float):
        raise NotAConstruction(t("construction.not_exact", what=what, value=v))
    try:
        return Fraction(str(v)) if not isinstance(v, Fraction) else v
    except (ValueError, ZeroDivisionError):
        raise NotAConstruction(t("construction.not_exact", what=what, value=v))


def _same_label(a, b) -> bool:
    """Two raw labels name the same object: equal as values (`1` and
    `Fraction(1)`), never merely alike in print (`1` and `"1"`)."""
    try:
        return a == b
    except Exception:  # noqa: BLE001
        return False


def _distinct(values, what):
    """The labels as text, REFUSED when two different labels print alike.
    `str()` then deduplication used to merge `1` and `"1"` -- a path of four
    vertices read as a triangle."""
    seen = {}
    for v in values:
        if isinstance(v, (bool, float)):
            raise NotAConstruction(t("construction.label_type", what=what, value=v))
        k = str(v)
        if k in seen and not _same_label(seen[k], v):
            raise NotAConstruction(t("construction.labels_collide", what=what,
                                     a=repr(seen[k]), b=repr(v)))
        seen.setdefault(k, v)
    return seen


def _nat(v, what) -> int:
    """A natural number, as written: an int (or an integral Fraction). A
    float, a bool, text or a non-integral rational is REFUSED -- `int(1.9)`
    is 1, and a target of 1.9 used to be checked as 1."""
    if isinstance(v, bool) or not (isinstance(v, int) or
                                   (isinstance(v, Fraction) and v.denominator == 1)):
        raise NotAConstruction(t("construction.not_natural", what=what, value=v))
    n = int(v)
    if n < 0:
        raise NotAConstruction(t("construction.not_natural", what=what, value=v))
    return n


def _s(x) -> str:
    return str(x)


def _edge(u, v):
    a, b = _s(u), _s(v)
    if a == b:
        raise NotAConstruction(t("construction.loop", v=a))
    return (a, b) if a <= b else (b, a)


def _tri(xs):
    xs = sorted(_s(x) for x in xs)
    if len(xs) != 3 or len(set(xs)) != 3:
        raise NotAConstruction(t("construction.not_triangle", t=xs))
    return tuple(xs)


def _tri_edges(tr):
    a, b, c = tr
    return [_edge(a, b), _edge(a, c), _edge(b, c)]


def graph(raw) -> tuple:
    """`(vertices, edges)` from `[[u, v], ...]` or `{"edges": ..., "vertices": ...}`."""
    if isinstance(raw, dict):
        es = raw.get("edges") or []
        listed = list(raw.get("vertices") or [])
    else:
        es, listed = raw or [], []
    _distinct(listed + [x for e in es for x in (e if isinstance(e, (list, tuple)) else [e])],
              "vertices")
    vs = {_s(v) for v in listed}
    E = set()
    for e in es:
        if len(e) != 2:
            raise NotAConstruction(t("construction.bad_edge", e=e))
        E.add(_edge(*e))
    for a, b in E:
        vs.update((a, b))
    return vs, E


def triangles(V, E):
    adj = {v: set() for v in V}
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    out = []
    for a, b in sorted(E):
        for c in sorted(adj[a] & adj[b]):
            if c > b:
                out.append((a, b, c))
    return out


def _row(key, ok, detail="", **kw):
    return (t("construction." + key, **kw), bool(ok), str(detail))


def _first(xs, k=3):
    xs = list(xs)
    return ", ".join(map(str, xs[:k])) + (" ..." if len(xs) > k else "")


# --- the fields each contract reads: anything else is REFUSED -----------------
#
# A step is a dictionary, and `dataspec` checked only the spec's own fields: a
# `targte` in a hosting step was ignored, and the threshold went unchecked. A
# schema per contract: `None` -- read by the contract itself; a dict -- the
# fields of a nested object; ("each", {...}) -- the fields of every element of
# a list; ("values", {...}) -- of every value of a mapping. A key starting with
# `_` is a comment, as everywhere in a data spec.

_EDGES = None
SCHEMAS = {
    "lift": {"parent": None, "child": None, "vertex_map": None, "child_packing": None,
             "child_cover": None, "from": None, "cover_added": None,
             "package": ("each", {"triangle": None, "owner": None}),
             "budget": {"paid_by": None, "ratio": None}},
    "catalogue": {"max_vertices": None, "ratio": None,
                  "forbidden": ("values", {"n": None, "edges": None}),
                  "representatives": ("values", {"n": None, "edges": None}),
                  "extensions": ("each", {"from": None, "neighbours": None, "to": None,
                                          "map": None, "excluded": None, "at": None}),
                  "witnesses": ("values", {"packing": None, "cover": None})},
    "credit": {"bases": None, "bases_from": None, "owners": None, "weights": None,
               "states": None, "covers": None, "relation": None, "target": None,
               "slots": ("values", {"allowed": None}),
               "cuts": ("values", {"p": None, "states": None})},
    "hosting": {"graph": None, "bases": None, "items": None, "allowed": None,
                "capacities": None, "resources": None, "assignment": None,
                "target": None, "occupied": None, "occupied_from": None},
    "glue": {"matching": None, "open": None, "owners": None,
             "blocks": ("values", {"ports": None, "interiors": None}),
             "covers": ("values", {"closed": None, "removed": None, "block": None}),
             "value": {"claim": None, "from": None, "quantity": None}},
    "certificate": {"path": None, "digest": None, "embedded": None,
                    "declared_digest": None, "obligation": None},
    "cegis": {"certificate": None, "required_backing": None, "declared_only": None,
              "backed_by": ("values", {"step": None, "quantity": None, "relation": None})},
    "charts": {"domain": None, "depth": None, "leaves": None, "unresolved": None,
               "charts": ("values", {"selectors": None, "certificates": None})},
    "substitution": {"certificate": None, "map": None, "denominator": None,
                     "inverse": None, "inverse_denominator": None, "obligation": None,
                     "power": None, "depth": None, "inclusion_trees": None,
                     "inverse_denominator_tree": None,
                     "old": {"variables": None, "box": None, "conditions": None},
                     "new": {"variables": None}},
}


def _fields(obj, schema, where):
    if not isinstance(obj, dict):
        raise NotAConstruction(t("construction.not_object", where=where))
    unknown = sorted(k for k in obj if not str(k).startswith("_") and k not in schema)
    if unknown:
        raise NotAConstruction(t("construction.unknown_field", where=where,
                                 names=", ".join(map(str, unknown)),
                                 known=", ".join(sorted(schema))))
    for k, sub in schema.items():
        if sub is None or k not in obj or obj[k] is None:
            continue
        if isinstance(sub, dict):
            _fields(obj[k], sub, "{}.{}".format(where, k))
        elif sub[0] == "each":
            for i, x in enumerate(obj[k] or []):
                _fields(x, sub[1], "{}.{}[{}]".format(where, k, i))
        elif sub[0] == "values":
            for n, x in (obj[k] or {}).items():
                _fields(x, sub[1], "{}.{}.{}".format(where, k, n))


def _no_floats(x, where):
    """Numbers are exact or refused, at every depth: `_label` used to stop at
    the first dictionary."""
    if isinstance(x, float):
        raise NotAConstruction(t("construction.not_exact", what=where, value=x))
    if isinstance(x, dict):
        for k, v in x.items():
            _no_floats(v, "{}.{}".format(where, k))
    elif isinstance(x, (list, tuple)):
        for i, v in enumerate(x):
            _no_floats(v, "{}[{}]".format(where, i))


def validate(step):
    """Refuse a step whose fields its contract does not read, or with an
    inexact number anywhere in it."""
    contract = _s(step.get("contract"))
    schema = dict(SCHEMAS[contract], id=None, contract=None)
    _fields(step, schema, _s(step.get("id")))
    if contract != "certificate":          # an embedded certificate is its own
        _no_floats(step, _s(step.get("id")))


# --- lift ----------------------------------------------------------------------

def check_lift(step, ctx):
    rows, out = [], {}
    G = ctx["graphs"]
    pid, cid = _s(step.get("parent")), _s(step.get("child"))
    if pid not in G or cid not in G:
        rows.append(_row("graph_known", False, _first([g for g in (pid, cid) if g not in G])))
        return rows, out, "complete"
    (PV, PE), (CV, CE) = G[pid], G[cid]

    vmap = {_s(k): _s(v) for k, v in (step.get("vertex_map") or {v: v for v in CV}).items()}
    unmapped = sorted(CV - set(vmap))
    not_parent = sorted(v for v in vmap.values() if v not in PV)
    injective = len(set(vmap.values())) == len(vmap)
    lost = [e for e in sorted(CE) if _edge(vmap.get(e[0], "?"), vmap.get(e[1], "?")) not in PE] \
        if not unmapped else []
    rows.append(_row("lift.map", not unmapped and not not_parent and injective and not lost,
                     _first(unmapped or not_parent or lost) or
                     t("construction.lift.map_detail", n=len(vmap), e=len(CE))))

    def up(e):
        return _edge(vmap[e[0]], vmap[e[1]])

    # the child's witnesses: given, or what an earlier lift ended with
    src = step.get("from")
    if src is not None:
        prev = ctx["outputs"].get(_s(src)) or {}
        if prev.get("graph") != cid:
            rows.append(_row("lift.from", False, t("construction.lift.from_wrong",
                                                   step=src, child=cid)))
            return rows, out, "complete"
        cpack = [tuple(x) for x in prev["packing"]]
        ccover = [tuple(x) for x in prev["cover"]]
        rows.append(_row("lift.from", True, t("construction.lift.from_detail", step=src)))
    else:
        cpack = [_tri(x) for x in step.get("child_packing") or []]
        ccover = [_edge(*e) for e in step.get("child_cover") or []]

    ctri = set(triangles(CV, CE))
    bad = [x for x in cpack if x not in ctri]
    used, shared = set(), []
    for x in cpack:
        for e in _tri_edges(x):
            if e in used:
                shared.append(e)
            used.add(e)
    rows.append(_row("lift.child_packing", not bad and not shared,
                     _first(bad or shared) or t("construction.n_triangles", n=len(cpack))))
    off = [e for e in ccover if e not in CE]
    missed = [x for x in ctri if not any(e in set(ccover) for e in _tri_edges(x))]
    rows.append(_row("lift.child_cover", not off and not missed,
                     _first(off or missed) or t("construction.n_edges", n=len(ccover))))
    if unmapped or not injective:
        return rows, out, "complete"

    image = set(vmap.values())
    package = []
    for item in step.get("package") or []:
        tri = _tri(item["triangle"] if isinstance(item, dict) else item)
        owner = _s(item.get("owner")) if isinstance(item, dict) and item.get("owner") is not None else None
        package.append((tri, owner))
    ptri = set(triangles(PV, PE))
    used = {up(e) for x in cpack for e in _tri_edges(x)}
    not_tri = [x for x, _o in package if x not in ptri]
    clash = []
    for x, _o in package:
        for e in _tri_edges(x):
            if e in used:
                clash.append("-".join(e))
            used.add(e)
    rows.append(_row("lift.package", not not_tri and not clash,
                     (t("construction.lift.shares", e=_first(clash)) if clash else _first(not_tri))
                     or t("construction.n_triangles", n=len(package))))
    wrong = [(x, o) for x, o in package if o is not None and (o not in x or o in image)]
    rows.append(_row("lift.owners", not wrong,
                     t("construction.lift.owner_wrong", t="-".join(wrong[0][0]), o=wrong[0][1])
                     if wrong else t("construction.lift.owners_detail",
                                     n=sum(1 for _x, o in package if o is not None))))

    final_pack = sorted({tuple(sorted(vmap[v] for v in x)) for x in cpack} | {x for x, _o in package})
    cover = {up(e) for e in ccover} | {_edge(*e) for e in step.get("cover_added") or []}
    off = [e for e in cover if e not in PE]
    missed = [x for x in ptri if not any(e in cover for e in _tri_edges(x))]
    rows.append(_row("lift.cover", not off and not missed,
                     _first(["-".join(e) for e in off] or ["-".join(x) for x in missed])
                     or t("construction.lift.cover_detail", n=len(cover), tris=len(ptri))))

    budget = step.get("budget") or {}
    ratio = _q(budget.get("ratio", 2), "ratio")
    paid = _s(budget.get("paid_by", cid))
    added = len(step.get("cover_added") or [])
    ok_paid = paid == cid
    ok_local = added <= ratio * len(package)
    ok_final = len(cover) <= ratio * len(final_pack)
    rows.append(_row("lift.budget", ok_paid and ok_local and ok_final,
                     t("construction.lift.paid_by", paid=paid, child=cid) if not ok_paid else
                     t("construction.lift.budget_detail", added=added, ratio=ratio,
                       package=len(package), cover=len(cover), packing=len(final_pack))))
    out = {"graph": pid, "packing": [list(x) for x in final_pack],
           "cover": [list(e) for e in sorted(cover)], "packing_size": len(final_pack),
           "cover_size": len(cover), "ratio": str(ratio),
           "established": {
               "object": pid,
               # a TRANSVERSAL: every triangle meets the cover -- not a
               # partition of the edges, which is another notion entirely
               "coverage_kind": "triangle transversal (every triangle meets the cover)",
               "verified_cost": "{} <= {} x {}".format(len(cover), ratio, len(final_pack)),
               "dependencies": [_s(src)] if src is not None else [],
               "unproved_bridges": []}}
    return rows, out, "complete"


# --- catalogue -------------------------------------------------------------------

def _small(raw, what):
    """`(n, set of (i, j))` on vertices 0..n-1."""
    n = _nat(raw["n"], what + ".n")
    E = set()
    for e in raw.get("edges") or []:
        i, j = _nat(e[0], what), _nat(e[1], what)
        if not (0 <= i < n and 0 <= j < n) or i == j:
            raise NotAConstruction(t("construction.catalogue.bad_graph", g=what, e=e))
        E.add((min(i, j), max(i, j)))
    return n, E


def _extended(n, E, S):
    return n + 1, set(E) | {(int(s), n) for s in S}


def _iso(n, E, m, F, mp):
    if n != m or len(E) != len(F) or sorted(mp) != list(range(n)):
        return False
    return all((min(mp[i], mp[j]), max(mp[i], mp[j])) in F for i, j in E)


def _induces(n, E, at, k, F):
    if len(at) != k or len(set(at)) != k or any(not (0 <= a < n) for a in at):
        return False
    for i in range(k):
        for j in range(i + 1, k):
            a, b = at[i], at[j]
            if (((min(a, b), max(a, b)) in E)) != ((i, j) in F):
                return False
    return True


def _small_witness(n, E, w, ratio):
    V = {str(i) for i in range(n)}
    SE = {_edge(str(a), str(b)) for a, b in E}
    tris = set(triangles(V, SE))
    pack = [_tri([str(x) for x in tr]) for tr in w.get("packing") or []]
    cover = {_edge(str(a), str(b)) for a, b in w.get("cover") or []}
    used = set()
    for x in pack:
        if x not in tris:
            return False
        for e in _tri_edges(x):
            if e in used:
                return False
            used.add(e)
    if any(e not in SE for e in cover):
        return False
    if any(not any(e in cover for e in _tri_edges(x)) for x in tris):
        return False
    return len(cover) <= ratio * len(pack)


def check_catalogue(step, ctx):
    rows = []
    N = _nat(step["max_vertices"], "max_vertices")
    reps = {_s(k): _small(v, k) for k, v in (step.get("representatives") or {}).items()}
    forb = {_s(k): _small(v, k) for k, v in (step.get("forbidden") or {}).items()}
    big = [k for k, (n, _e) in reps.items() if n > N]
    rows.append(_row("catalogue.reps", not big and any(n == 1 for n, _e in reps.values()),
                     _first(big) if big else
                     t("construction.catalogue.reps_detail", n=len(reps), N=N)))
    entries = {}
    for x in step.get("extensions") or []:
        key = (_s(x["from"]), tuple(sorted(_nat(s, "neighbours")
                                           for s in x.get("neighbours") or [])))
        entries.setdefault(key, []).append(x)
    missing, invalid, checked = [], [], 0
    for name, (n, E) in sorted(reps.items()):
        if n >= N:
            continue
        for k in range(n + 1):
            for S in combinations(range(n), k):
                xs = entries.get((name, S))
                if not xs:
                    missing.append("{}+{}".format(name, list(S)))
                    continue
                m, F = _extended(n, E, S)
                for x in xs:
                    checked += 1
                    if x.get("excluded") is not None:
                        fn = _s(x["excluded"])
                        good = fn in forb and _induces(m, F, [_nat(a, "at") for a in x.get("at") or []],
                                                       forb[fn][0], forb[fn][1])
                    else:
                        to = _s(x.get("to"))
                        good = to in reps and _iso(m, F, reps[to][0], reps[to][1],
                                                   [_nat(a, "map") for a in x.get("map") or []])
                    if not good:
                        invalid.append("{}+{}".format(name, list(S)))
    unknown = [k for k in entries if k[0] not in reps]
    rows.append(_row("catalogue.complete", not missing,
                     t("construction.catalogue.missing", n=len(missing), which=_first(missing))
                     if missing else t("construction.catalogue.complete_detail", n=checked)))
    rows.append(_row("catalogue.valid", not invalid and not unknown,
                     _first(invalid or ["{}+{}".format(a, list(b)) for a, b in unknown])
                     or t("construction.catalogue.valid_detail", n=checked)))
    ratio = step.get("ratio")
    out = {"representatives": len(reps), "max_vertices": N, "extensions": checked}
    if ratio is not None:
        r = _q(ratio, "ratio")
        ws = step.get("witnesses") or {}
        bad = [k for k, (n, E) in reps.items()
               if k not in ws or not _small_witness(n, E, ws[k], r)]
        rows.append(_row("catalogue.property", not bad,
                         _first(bad) or t("construction.catalogue.property_detail",
                                          n=len(reps), r=r)))
        out["ratio"] = str(r)
    return rows, out, "complete"


# --- credit ----------------------------------------------------------------------

def check_credit(step, ctx):
    rows = []
    owners = {_s(h): [_s(b) for b in bs] for h, bs in (step.get("owners") or {}).items()}
    seen, twice = {}, []
    for h, bs in owners.items():
        for b in bs:
            if b in seen:
                twice.append("{} ({} / {})".format(b, seen[b], h))
            seen[b] = h
    declared = step.get("bases")
    src = step.get("bases_from")
    if src is not None:
        # THE SAME BASES the hosting step placed, owned by ITS hosts
        prev = ctx["outputs"].get(_s(src)) or {}
        same = (sorted(prev.get("items") or []) == sorted(seen)
                and set(owners) <= set(prev.get("hosts") or []))
        rows.append(_row("credit.same_bases", same,
                         t("construction.credit.same_bases_detail", step=src)))
        declared = prev.get("items") or declared
    orphan = [b for b in (declared or []) if _s(b) not in seen] if declared is not None else []
    rows.append(_row("credit.owners", not twice and not orphan,
                     (t("construction.credit.twice", which=_first(twice)) if twice else _first(orphan))
                     or t("construction.credit.owners_detail", b=len(seen), h=len(owners))))
    weights = {}
    nw = [b for b in seen if b not in {_s(k) for k in (step.get("weights") or {})}]
    for k, v in (step.get("weights") or {}).items():
        weights[_s(k)] = _q(v, "weight " + _s(k))
    rows.append(_row("credit.weights", not nw, _first(nw) or
                     t("construction.credit.weights_detail", n=len(weights))))
    states = {_s(h): {_s(s): [_s(b) for b in bs] for s, bs in st.items()}
              for h, st in (step.get("states") or {}).items()}
    badst = []
    for h, st in states.items():
        for s, bs in st.items():
            if h not in owners or any(b not in owners[h] for b in bs) or len(set(bs)) != len(bs):
                badst.append("{}:{}".format(h, s))
    rows.append(_row("credit.states", not badst,
                     t("construction.credit.state_bad", which=_first(badst)) if badst else
                     t("construction.credit.states_detail", n=sum(len(v) for v in states.values()))))
    slots = step.get("slots")
    if slots is not None:
        covers = step.get("covers") or {}
        badcov = []
        for h, st in states.items():
            allowed = {_s(b): {_s(x) for x in xs} for b, xs in
                       ((slots.get(h) or {}).get("allowed") or {}).items()}
            for s, bs in st.items():
                cov = {_s(b): _s(x) for b, x in ((covers.get(h) or {}).get(s) or {}).items()}
                if (set(cov) != set(bs) or len(set(cov.values())) != len(cov)
                        or any(cov[b] not in allowed.get(b, set()) for b in cov)):
                    badcov.append("{}:{}".format(h, s))
        rows.append(_row("credit.covers", not badcov,
                         t("construction.credit.cover_bad", which=_first(badcov)) if badcov
                         else t("construction.credit.covers_detail")))
    cuts = step.get("cuts") or {}
    total_p, omitted, negp = Fraction(0), [], []
    value = Fraction(0)
    for c, raw in cuts.items():
        p = _q(raw.get("p"), "p({})".format(c))
        if p < 0:
            negp.append(_s(c))
        total_p += p
        st = {_s(h): _s(s) for h, s in (raw.get("states") or {}).items()}
        for h in owners:
            if h not in st or st[h] not in states.get(h, {}):
                omitted.append("{}@{}".format(h, c))
                continue
            value += p * sum((weights.get(b, Fraction(0)) for b in states[h][st[h]]), Fraction(0))
    rows.append(_row("credit.distribution", total_p == 1 and not negp,
                     t("construction.credit.p_sum", s=total_p) if total_p != 1 else
                     _first(negp) or t("construction.credit.p_detail", n=len(cuts))))
    rows.append(_row("credit.every_state", not omitted,
                     t("construction.credit.omitted", which=_first(omitted)) if omitted
                     else t("construction.credit.every_state_detail")))
    rel = _s(step.get("relation", ">="))
    target = _q(step.get("target", 0), "target")
    holds = {">=": value >= target, "<=": value <= target, "=": value == target,
             ">": value > target, "<": value < target}.get(rel)
    rows.append(_row("credit.sum", bool(holds),
                     t("construction.credit.sum_detail", v=value, rel=rel, target=target)))
    return rows, {"value": str(value), "target": str(target), "relation": rel}, "complete"


# --- hosting -----------------------------------------------------------------------

def check_hosting(step, ctx):
    from . import assignment as A

    rows = []
    try:
        items, allow, caps = A.normalise(step["items"], step["allowed"], step["capacities"])
        res = A.normalise_resources(items, step.get("resources") or {})
    except (A.NotAnAssignment, KeyError, TypeError) as e:
        rows.append(_row("hosting.readable", False, e))
        return rows, {}, "complete"
    gid = step.get("graph")
    if gid is not None:
        # TIED TO THE GRAPH: each base an edge of it, each allowed host joined
        # to both ends (host + base is a triangle), and the resources the
        # base's ends. Renaming a base and its owner together cannot then
        # slip away from the graph: the new name has to be an edge.
        G = ctx["graphs"].get(_s(gid))
        bases = {_s(k): [_s(x) for x in v] for k, v in (step.get("bases") or {}).items()}
        bad = []
        if G is None:
            bad.append(_s(gid))
        else:
            V, E = G
            for i in items:
                ends = bases.get(i)
                if not ends or len(ends) != 2 or _edge(*ends) not in E:
                    bad.append(i)
                    continue
                if any(_edge(h, ends[0]) not in E or _edge(h, ends[1]) not in E
                       for h in allow[i]):
                    bad.append("{}@{}".format(i, _first(allow[i])))
                elif sorted(res.get(i) or ends) != sorted(ends):
                    bad.append("{} (resources)".format(i))
                else:
                    res[i] = sorted(ends)
        rows.append(_row("hosting.graph", not bad, _first(bad) or
                         t("construction.hosting.graph_detail", g=gid, n=len(items))))
    got = {_s(k): _s(v) for k, v in (step.get("assignment") or {}).items()}
    probs = A.check_physical({"items": items, "allowed": allow, "capacities": caps,
                              "resources": res,
                              "physical": {"assignment": got, "size": len(got)}})
    rows.append(_row("hosting.physical", not probs, "; ".join(probs[:3]) or
                     t("construction.hosting.detail", n=len(got))))
    realized = None
    if gid is not None and not bad:
        # THE PIECES, NOT THE BOOKKEEPING. Per host, "no resource twice" is
        # what a host's own spokes need; in ONE graph two hosts can still
        # consume the same edge (ab on x and ab on y, under two names), and a
        # base on one host can be a spoke of another. So every placed base
        # u-v on host h is rebuilt as the edges {uv, hu, hv}, and each edge
        # of the graph may be used once in all of them -- and not at all if it
        # is already occupied (existing is not being free).
        occupied = {_edge(*e) for e in step.get("occupied") or []}
        src = step.get("occupied_from")
        if src is not None:
            prev = ctx["outputs"].get(_s(src)) or {}
            occupied |= {e for tr in prev.get("packing") or [] for e in _tri_edges(tuple(tr))}
        use = {}
        for i, h in sorted(got.items()):
            u, v = bases[i]
            for e in (_edge(u, v), _edge(h, u), _edge(h, v)):
                use.setdefault(e, []).append("{}@{}".format(i, h))
        twice = ["{}-{} ({})".format(e[0], e[1], ", ".join(w)) for e, w in sorted(use.items())
                 if len(w) > 1]
        taken = ["{}-{}".format(*e) for e in sorted(use) if e in occupied]
        realized = not twice and not taken
        rows.append(_row("hosting.edge_disjoint", realized,
                         t("construction.hosting.edge_twice", which=_first(twice)) if twice else
                         t("construction.hosting.edge_taken", which=_first(taken)) if taken else
                         t("construction.hosting.edge_disjoint_detail", n=len(got),
                           e=len(use), occ=len(occupied))))
    target = step.get("target")
    if target is not None:
        n = _nat(target, "target")
        rows.append(_row("hosting.target", len(got) >= n,
                         t("construction.hosting.target_detail", n=len(got), target=n)))
    out = {"placed": len(got), "items": list(items), "hosts": sorted(caps),
           "assignment_feasible": not probs,
           # None: no graph was given, so no realization could be rebuilt
           "edge_disjoint_realization_verified": realized,
           "target": None if target is None else _nat(target, "target")}
    if gid is not None and realized:
        out["packing"] = sorted([sorted([bases[i][0], bases[i][1], h])
                                 for i, h in got.items()])
    out["established"] = {
        "object": _s(gid) if gid is not None else None,
        "resource_model": ("edge-disjoint realization in the graph" if gid is not None
                           else "resources per host only; no realization rebuilt"),
        "verified_count": len(got),
        "dependencies": [_s(step["occupied_from"])] if step.get("occupied_from") else []}
    return rows, out, "complete"


# --- glue -----------------------------------------------------------------------------

def check_glue(step, ctx):
    rows = []
    blocks = step.get("blocks") or {}
    _distinct(list(blocks), "blocks")
    _distinct([p for raw in blocks.values() for p in raw.get("ports") or []], "ports")
    _distinct([i for raw in blocks.values() for i in raw.get("interiors") or []], "interiors")
    port_block, dup = {}, []
    for b, raw in blocks.items():
        for p in raw.get("ports") or []:
            if _s(p) in port_block:
                dup.append(_s(p))
            port_block[_s(p)] = _s(b)
    count = {p: 0 for p in port_block}
    badpair = []
    for pair in step.get("matching") or []:
        a, c = (_s(x) for x in pair)
        if a not in port_block or c not in port_block or port_block[a] == port_block[c]:
            badpair.append("{}-{}".format(a, c))
        for x in (a, c):
            if x in count:
                count[x] += 1
    for p in step.get("open") or []:
        if _s(p) in count:
            count[_s(p)] += 1
        else:
            badpair.append(_s(p))
    wrong = [p for p, k in count.items() if k != 1]
    rows.append(_row("glue.ports", not dup and not wrong and not badpair,
                     (t("construction.glue.port_count", which=_first(
                         "{}x{}".format(p, count[p]) for p in wrong)) if wrong
                      else _first(dup or badpair)) or
                     t("construction.glue.ports_detail", n=len(port_block),
                       m=len(step.get("matching") or []), o=len(step.get("open") or []))))
    owners = {_s(k): _s(v) for k, v in (step.get("owners") or {}).items()}
    where = {}
    for b, raw in blocks.items():
        for i in raw.get("interiors") or []:
            where.setdefault(_s(i), []).append(_s(b))
    two = [i for i, bs in where.items() if len(bs) > 1]
    none = [i for i in where if i not in owners]
    # THE OWNER IS THE BLOCK THAT DECLARES THE INTERIOR. Any known block
    # name used to pass, so two owners could be crossed; a change of owner
    # is a transport, to be declared as one, not a name that happens to exist.
    badown = ["{}->{}".format(i, o) for i, o in owners.items()
              if i not in where or o not in where[i]]
    rows.append(_row("glue.owners", not two and not none and not badown,
                     (t("construction.glue.two_owners", which=_first(two)) if two else
                      t("construction.glue.no_owner", which=_first(none)) if none else
                      t("construction.glue.wrong_owner", which=_first(badown)) if badown
                      else "") or t("construction.glue.owners_detail", n=len(where))))
    perforated = [n for n, c in (step.get("covers") or {}).items()
                  if c.get("closed") and (c.get("removed") or [])]
    rows.append(_row("glue.covers", not perforated,
                     t("construction.glue.perforated", which=_first(perforated)) if perforated
                     else t("construction.glue.covers_detail",
                            n=len(step.get("covers") or {}))))
    out = {"ports": len(port_block), "pairs": len(step.get("matching") or [])}
    val = step.get("value")
    if val is not None:
        src, qty = val.get("from"), val.get("quantity")
        if src is None or qty is None:
            rows.append(_row("glue.value", False, t("construction.glue.no_witness")))
        else:
            have = (ctx["outputs"].get(_s(src)) or {}).get(_s(qty))
            claim = _q(val.get("claim"), "value")
            ok = have is not None and _q(have, "value") == claim
            rows.append(_row("glue.value", ok, t("construction.glue.value_detail",
                                                 claim=claim, src=src, qty=qty, have=have)))
            out["value"] = str(claim)
    return rows, out, "complete"


# --- certificate ---------------------------------------------------------------------

def prepare_certificate(step, ctx):
    """Embed the certificate (and record its obligation's fingerprint): the
    construction is then checked from ITS OWN file, anywhere."""
    from . import obligation as O
    from . import store
    from .certificate import Certificate

    if step.get("embedded") is not None:
        return dict(step)
    path = _resolve(step["path"], ctx)
    cert = Certificate.from_dict(store.read_json(str(path)))
    out = dict(step, embedded=cert.to_dict(), digest=cert.digest())
    if step.get("digest") is not None and _s(step["digest"]) not in (cert.digest(), ):
        out["declared_digest"] = _s(step["digest"])
    ob = step.get("obligation")
    if ob is not None:
        from .spec import load_spec

        sp = load_spec(str(_resolve(ob, ctx)))
        got = O.same_obligation(cert, sp)
        # Only the SPEC's fingerprint is recorded: whether the certificate is
        # about it is recomputed by `verify` from the certificate itself.
        out["obligation"] = {"path": _s(ob), "differences": got["differences"][:4],
                             "fingerprint": (got.get("fingerprint") or {}).get("spec")}
    return out


def _resolve(name, ctx):
    """A relative path: beside the spec if it is there, else from the
    directory the command runs in (where `out/` usually is)."""
    import pathlib

    path = pathlib.Path(_s(name))
    if path.is_absolute():
        return path
    for base in ctx.get("bases") or []:
        if base is not None and (pathlib.Path(base) / path).exists():
            return pathlib.Path(base) / path
    return path


def _values_of(cert):
    p = cert.payload
    out = {"kind": cert.kind}
    if cert.kind in ("cegis", "synth_optimum", "synth_proved"):
        try:
            from .engines.cegis import implementation_of

            impl = implementation_of(cert) or {}
            # `{name: [sort, value]}` -- the value is what a backing compares
            out["implementation"] = {k: _s(v[1] if isinstance(v, (list, tuple)) else v)
                                     for k, v in impl.items()}
        except Exception:  # noqa: BLE001 -- a value this cannot read is just absent
            pass
    if cert.kind == "assignment":
        out["placed"] = int((p.get("physical") or {}).get("size", p.get("size", 0)) or 0)
    if cert.kind == "lp_dual":
        out["objective"] = p.get("objective")
    if cert.kind == "polynomial_nonneg":
        out["holds"] = p.get("holds")
    return out


def check_certificate(step, ctx):
    from . import obligation as O
    from .certificate import Certificate, verify

    rows = []
    try:
        cert = Certificate.from_dict(step["embedded"])
    except Exception as e:  # noqa: BLE001
        rows.append(_row("certificate.readable", False, e))
        return rows, {}, "complete"
    digest_ok = _s(step.get("digest")) == cert.digest() and step.get("declared_digest") is None
    rows.append(_row("certificate.digest", digest_ok,
                     t("construction.certificate.digest_detail", d=cert.digest()[:16])
                     if digest_ok else t("construction.certificate.digest_bad",
                                         want=_s(step.get("declared_digest") or step.get("digest"))[:16],
                                         got=cert.digest()[:16])))
    rep = verify(cert, ctx.get("limits"))
    rows.append(_row("certificate.verifies", rep.ok,
                     "{} ({})".format(cert.kind, rep.degree)))
    degree = "complete" if rep.ok and rep.degree == "complete" else (
        "with_solver" if rep.ok and rep.degree == "with_solver" else "relative")
    out = _values_of(cert)
    out["degree"] = rep.degree
    out["certificate_validity"] = "verified" if rep.ok else "invalid"
    ob = step.get("obligation")
    if ob is not None:
        # A BINDING IS COMPUTED, NOT READ. `same: true` with a null
        # fingerprint used to pass: a valid certificate of A, declared to be
        # about B, was accepted as B's. The certificate's own fingerprint is
        # recomputed here and must equal the obligation's, which must exist.
        if not isinstance(ob, dict):
            ob = {"path": ob}
        mine = O.fingerprint(cert)
        want = ob.get("fingerprint")
        if mine is None:
            # this kind keeps only part of its obligation (a core): the tie
            # cannot be recomputed, and is said so -- never taken as a match
            out["obligation_binding"] = "unsupported"
            out["relative_because"] = t("construction.certificate.binding_unsupported",
                                        kind=cert.kind, path=ob.get("path"))
            degree = "relative"
        else:
            bound = want is not None and mine == want
            out["obligation_binding"] = "verified" if bound else "differs"
            rows.append(_row("certificate.obligation", bound,
                             t("construction.certificate.obligation_detail", path=ob.get("path"),
                               fp=mine[:12]) if bound else
                             t("construction.certificate.no_fingerprint", path=ob.get("path"))
                             if want is None else
                             "; ".join(ob.get("differences") or []) or
                             t("construction.certificate.fingerprint_differs",
                               path=ob.get("path"), want=_s(want)[:12], got=mine[:12])))
    return rows, out, degree


# --- cegis -------------------------------------------------------------------------------

def check_cegis(step, ctx):
    rows = []
    src = _s(step.get("certificate"))
    prev = ctx["outputs"].get(src) or {}
    kind_ok = prev.get("kind") in ("cegis", "synth_optimum", "synth_proved")
    impl = prev.get("implementation") or {}
    rows.append(_row("cegis.source", kind_ok and bool(impl),
                     t("construction.cegis.source_detail", step=src, kind=prev.get("kind"),
                       impl=_first("{}={}".format(k, v) for k, v in impl.items()))))
    backed = step.get("backed_by") or {}
    declared_only = [_s(p) for p in step.get("declared_only") or []]
    required = [_s(p) for p in step.get("required_backing") or []]
    # EVERY PARAMETER IS ACCOUNTED FOR. One parameter backed used to cover
    # for another that was not (a = 1 backed, b = 100 not even mentioned).
    # Each is backed, or declared unbacked by name -- an algebraic parameter
    # needs no resource -- and a required one cannot be declared away.
    unbacked = [p for p in impl if p not in {_s(k) for k in backed} and p not in declared_only]
    clash = [p for p in required if p in declared_only or p not in {_s(k) for k in backed}]
    unknown = [p for p in declared_only + required if p not in impl]
    rows.append(_row("cegis.accounted", not unbacked and not clash and not unknown,
                     t("construction.cegis.unaccounted", which=_first(unbacked)) if unbacked else
                     t("construction.cegis.required_missing", which=_first(clash)) if clash else
                     _first(unknown) if unknown else
                     t("construction.cegis.accounted_detail", b=len(backed),
                       d=len(declared_only))))
    bad = []
    for param, b in backed.items():
        have = (ctx["outputs"].get(_s(b.get("step"))) or {}).get(_s(b.get("quantity")))
        rel = _s(b.get("relation", "<="))
        if _s(param) not in impl or have is None:
            bad.append(_s(param))
            continue
        v, h = _q(impl[_s(param)], param), _q(have, "quantity")
        if not {"<=": v <= h, ">=": v >= h, "=": v == h, "<": v < h, ">": v > h}.get(rel, False):
            bad.append("{}={} {} {}".format(param, v, rel, h))
    rows.append(_row("cegis.backed", not bad and bool(backed),
                     t("construction.cegis.unbacked") if not backed else
                     _first(bad) or t("construction.cegis.backed_detail", n=len(backed))))
    return rows, {"parameters": impl,
                  "backed_parameters": sorted(_s(k) for k in backed),
                  "unbacked_parameters": sorted(unbacked),
                  "declared_only_parameters": sorted(declared_only),
                  "established": {"object": src, "resource_model": "parameters against "
                                  "quantities other steps certified",
                                  "dependencies": sorted({_s(b.get("step"))
                                                          for b in backed.values()}),
                                  "unproved_bridges": sorted(declared_only)}}, "with_solver"


# --- charts --------------------------------------------------------------------------------

def _box_of(raw):
    out = {_s(n): (_q(lo, n), _q(hi, n)) for n, (lo, hi) in raw.items()}
    bad = [n for n, (lo, hi) in out.items() if hi < lo]
    if bad:
        raise NotAConstruction(t("construction.box_reversed", names=_first(bad)))
    return out


def _names(xs, what):
    out = tuple(_s(v) for v in xs)
    if len(set(out)) != len(out):
        raise NotAConstruction(t("construction.names_repeat", what=what))
    return out


def _selectors(chart, ring):
    from .polynomials import as_poly

    return {_s(n): as_poly(ring, g) for n, g in (chart.get("selectors") or {}).items()}


def _chart_holds(sel, box):
    from . import bernstein

    return all(bernstein.nonneg(g, box, 0)[0] for g in sel.values())


def prepare_charts(step, ctx):
    """The leaves: halve the box until one chart's selectors are all >= 0
    on each piece (Bernstein, at the polynomials' own degree)."""
    if step.get("leaves") is not None:
        return dict(step)
    from .budget import tick

    dom = _box_of(step["domain"])
    ring = tuple(sorted(dom))
    charts = {_s(k): _selectors(v, ring) for k, v in (step.get("charts") or {}).items()}
    depth = _nat(step.get("depth", 8), "depth")
    leaves, unresolved = [], []

    def go(box, d):
        tick(16)
        for name, sel in charts.items():
            if _chart_holds(sel, box):
                leaves.append({"box": {n: [str(a), str(b)] for n, (a, b) in box.items()},
                               "chart": name})
                return
        if d <= 0:
            unresolved.append({n: [str(a), str(b)] for n, (a, b) in box.items()})
            return
        n = max(ring, key=lambda v: (box[v][1] - box[v][0], v))
        lo, hi = box[n]
        mid = (lo + hi) / 2
        go(dict(box, **{n: (lo, mid)}), d - 1)
        go(dict(box, **{n: (mid, hi)}), d - 1)

    go(dom, depth)
    return dict(step, leaves=leaves, unresolved=unresolved)


def check_charts(step, ctx):
    from . import covering

    rows = []
    dom = _box_of(step["domain"])
    ring = tuple(sorted(dom))
    charts = {_s(k): v for k, v in (step.get("charts") or {}).items()}
    sel = {k: _selectors(v, ring) for k, v in charts.items()}
    leaves = step.get("leaves") or []
    boxes = [_box_of(lf["box"]) for lf in leaves]
    unresolved = step.get("unresolved") or []
    ok_tile, why = covering.tiles(dom, boxes) if boxes else (False, "no leaves")
    rows.append(_row("charts.tiling", ok_tile and not unresolved,
                     t("construction.charts.unresolved", n=len(unresolved)) if unresolved
                     else why or t("construction.charts.tiling_detail", n=len(boxes))))
    wrong = [i for i, (lf, b) in enumerate(zip(leaves, boxes))
             if _s(lf.get("chart")) not in sel or not _chart_holds(sel[_s(lf["chart"])], b)]
    rows.append(_row("charts.selectors", not wrong,
                     _first(wrong) or t("construction.charts.selectors_detail")))
    bad = [name for name, chart in charts.items() if not (chart.get("certificates") or [])]
    for name, chart in charts.items():
        mine = [b for lf, b in zip(leaves, boxes) if _s(lf.get("chart")) == name]
        sels = {tuple(sorted(g.terms.items())) for g in sel[name].values()}
        for sid in chart.get("certificates") or []:
            prev = ctx["outputs"].get(_s(sid)) or {}
            emb = ((ctx["steps"].get(_s(sid)) or {}).get("embedded") or {})
            p = emb.get("payload") or {}
            if prev.get("kind") != "polynomial_nonneg" or p.get("holds") is not True:
                bad.append("{}:{}".format(name, sid))
                continue
            if sorted(p.get("parameters") or []) != list(ring):
                bad.append("{}:{} (variables)".format(name, sid))
                continue
            cb = {n: (_q(lo, n), _q(hi, n)) for n, (lo, hi) in p["box"].items()
                  if hi is not None}
            if len(cb) != len(ring) or any(not (cb[n][0] <= b[n][0] and b[n][1] <= cb[n][1])
                                           for b in mine for n in ring):
                bad.append("{}:{} (box)".format(name, sid))
                continue
            from .polynomials import Poly

            vs = tuple(p["parameters"])
            for g in (p.get("region") or {}).values():
                gp = Poly.parse(vs, g)
                # the certificate's ring may list the variables in another order
                gg = Poly(ring, {tuple(e[vs.index(v)] for v in ring): c
                                 for e, c in gp.terms.items()})
                if tuple(sorted(gg.terms.items())) not in sels:
                    bad.append("{}:{} (region)".format(name, sid))
                    break
    rows.append(_row("charts.certificates", not bad,
                     _first(bad) or t("construction.charts.certificates_detail", n=len(charts))))
    return rows, {"leaves": len(leaves), "charts": len(charts)}, "complete"


# --- substitution ---------------------------------------------------------------------------

def _homog(p, images, den, d, ring):
    """`p(images / den) * den^d` as a polynomial over `ring` (d >= deg p)."""
    from .polynomials import Poly

    out = Poly(ring)
    for e, c in p.terms.items():
        term = Poly.const(ring, c)
        for v, k in zip(p.vars, e):
            if k:
                term = term * images[v] ** k
        term = term * den ** (d - sum(e))
        out = out + term
    return out


def _sub_parts(step):
    from .polynomials import as_poly

    old = step["old"]
    X = _names(old["variables"], "old.variables")
    Y = _names(step["new"]["variables"], "new.variables")
    N = {x: as_poly(Y, step["map"][x]) for x in X}
    D = as_poly(Y, step.get("denominator", "1"))
    U = {y: as_poly(X, step["inverse"][y]) for y in Y}
    E = as_poly(X, step.get("inverse_denominator", "1"))
    P = as_poly(X, step["obligation"])
    obox = _box_of(old["box"])
    conds = [(_s(n), as_poly(X, g)) for n, g in (old.get("conditions") or {}).items()]
    return X, Y, N, D, U, E, P, obox, conds


def _inclusions(step, ctx, X, Y, U, E, conds):
    """The polynomials over the OLD variables that must be >= 0 on the old
    domain for psi to land inside the certificate's domain."""
    from .polynomials import Poly

    emb = ((ctx["steps"].get(_s(step.get("certificate"))) or {}).get("embedded") or {})
    p = emb.get("payload") or {}
    vs = tuple(p.get("parameters") or [])
    out = []
    for y, (lo, hi) in (p.get("box") or {}).items():
        if lo is not None:
            out.append(("{} >= {}".format(y, lo), U[y] - E.scaled(_q(lo, y))))
        if hi is not None:
            out.append(("{} <= {}".format(y, hi), E.scaled(_q(hi, y)) - U[y]))
    for name, g in (p.get("region") or {}).items():
        gp = Poly.parse(vs, g)
        d = max(gp.degree, 0)
        d += d % 2          # an even power of E keeps the sign whatever E's
        out.append((name, _homog(gp, U, E, d, X)))
    return out


def prepare_substitution(step, ctx):
    from . import bernstein

    if step.get("inclusion_trees") is not None:
        return dict(step)
    X, Y, N, D, U, E, P, obox, conds = _sub_parts(step)
    terms = bernstein.region_terms(conds) if conds else []
    trees = []
    depth = _nat(step.get("depth", 6), "depth")
    for name, g in _inclusions(step, ctx, X, Y, U, E, conds):
        ok, tree = (bernstein.nonneg_region(g, obox, terms, depth) if terms
                    else bernstein.nonneg(g, obox, depth))
        trees.append({"name": name, "ok": bool(ok), "tree": tree})
    ok_e, etree = bernstein.positive(E, obox, depth)
    return dict(step, inclusion_trees=trees, inverse_denominator_tree=etree if ok_e else None)


def check_substitution(step, ctx):
    from . import bernstein
    from .polynomials import Poly

    rows = []
    X, Y, N, D, U, E, P, obox, conds = _sub_parts(step)
    sid = _s(step.get("certificate"))
    emb = ((ctx["steps"].get(sid) or {}).get("embedded") or {})
    p = emb.get("payload") or {}
    good_src = ((ctx["outputs"].get(sid) or {}).get("kind") == "polynomial_nonneg"
                and p.get("holds") is True and tuple(p.get("parameters") or []) == Y)
    rows.append(_row("substitution.source", good_src, t("construction.substitution.source_detail",
                                                         step=sid, vars=", ".join(Y))))
    if not good_src:
        return rows, {}, "complete"
    Q = Poly.parse(Y, p["poly"])
    k = _nat(step.get("power", P.degree), "power")
    pulled = _homog(P, N, D, max(k, P.degree), Y) if k >= P.degree else None
    rows.append(_row("substitution.pullback", pulled is not None and pulled == Q,
                     t("construction.substitution.pullback_detail", k=k)))
    nbox = {n: (_q(lo, n), _q(hi, n)) for n, (lo, hi) in p["box"].items() if hi is not None}
    closed = len(nbox) == len(Y)
    rows.append(_row("substitution.denominator", closed and bernstein.positive(D, nbox, 8)[0],
                     t("construction.substitution.denominator_detail", d=str(D))))
    ident = True
    for x in X:
        dd = max(N[x].degree, D.degree, 0)
        lhs = _homog(N[x], U, E, dd, X)
        rhs = Poly.var(X, x) * _homog(D, U, E, dd, X)
        ident = ident and lhs == rhs
    rows.append(_row("substitution.inverse", ident, t("construction.substitution.inverse_detail")))
    etree = step.get("inverse_denominator_tree")
    e_ok = bernstein.check_positive(E, obox, etree) if E.degree > 0 else (
        E.terms.get((0,) * len(X), Fraction(0)) > 0)
    rows.append(_row("substitution.inverse_denominator", bool(e_ok),
                     t("construction.substitution.denominator_detail", d=str(E))))
    terms = dict(bernstein.region_terms(conds)) if conds else None
    trees = {tr["name"]: tr for tr in step.get("inclusion_trees") or []}
    bad = []
    for name, g in _inclusions(step, ctx, X, Y, U, E, conds):
        tr = trees.get(name)
        if tr is None or not tr.get("ok") or not bernstein.check(g, obox, tr.get("tree"),
                                                                 terms=terms):
            bad.append(name)
    rows.append(_row("substitution.inclusion", not bad,
                     _first(bad) or t("construction.substitution.inclusion_detail",
                                      n=len(trees))))
    return rows, {"obligation": str(P), "holds_on": {n: [str(a), str(b)]
                                                     for n, (a, b) in obox.items()}}, "complete"


# --- the whole ----------------------------------------------------------------------------------

CHECKERS = {"lift": check_lift, "catalogue": check_catalogue, "credit": check_credit,
            "hosting": check_hosting, "glue": check_glue, "certificate": check_certificate,
            "cegis": check_cegis, "charts": check_charts, "substitution": check_substitution}
PREPARERS = {"certificate": prepare_certificate, "charts": prepare_charts,
             "substitution": prepare_substitution}


def normal_graphs(raw):
    _distinct(list(raw or {}), "graph names")
    return {_s(k): graph(v) for k, v in (raw or {}).items()}


def run(graphs_raw, steps, limits=None, base_dir=None, prepare=False):
    """Check every step in order. Returns `(steps_out, report)` where
    `report` is `[{"id", "contract", "ok", "degree", "rows", "outputs"}]`.
    `prepare=True` lets the producers fill in what they compute (embedded
    certificates, leaves, inclusion trees); `verify` runs with False and the
    steps exactly as the certificate carries them."""
    bases = base_dir if isinstance(base_dir, (list, tuple)) else [base_dir]
    try:
        graphs = normal_graphs(graphs_raw)
    except NotAConstruction as e:
        return list(steps), [{"id": "graphs", "contract": "graphs", "ok": False,
                              "degree": "relative", "rows": [(str(e), False, "")],
                              "outputs": {}}]
    ctx = {"graphs": graphs, "outputs": {}, "steps": {},
           "bases": list(bases), "limits": limits}
    out_steps, report, ids = [], [], set()
    for raw in steps:
        sid, contract = _s(raw.get("id")), _s(raw.get("contract"))
        if not raw.get("id") or sid in ids or contract not in CHECKERS:
            why = (t("construction.step_contract", c=contract, known=", ".join(CONTRACTS))
                   if contract not in CHECKERS else t("construction.step_id", id=sid))
            report.append({"id": sid, "contract": contract, "ok": False,
                           "degree": "relative", "rows": [(why, False, "")], "outputs": {}})
            out_steps.append(dict(raw))
            continue
        ids.add(sid)
        try:
            validate(raw)
            step = PREPARERS[contract](raw, ctx) if prepare and contract in PREPARERS \
                else dict(raw)
            ctx["steps"][sid] = step
            rows, outputs, degree = CHECKERS[contract](step, ctx)
        except NotAConstruction as e:
            step, rows, outputs, degree = dict(raw), [(str(e), False, "")], {}, "relative"
        except (KeyError, TypeError, ValueError, ZeroDivisionError, OSError) as e:
            step, rows, outputs, degree = dict(raw), [(t("construction.unreadable",
                                                         type=type(e).__name__,
                                                         why=str(e)[:160]), False, "")], {}, "relative"
        ok = all(r[1] for r in rows)
        if ok:
            ctx["outputs"][sid] = outputs
        report.append({"id": sid, "contract": contract, "ok": ok, "degree": degree,
                       "rows": rows, "outputs": outputs})
        out_steps.append(step)
    return out_steps, report


def degree_of(report) -> str:
    if any(r["degree"] == "relative" for r in report):
        return "relative"
    if any(r["degree"] == "with_solver" for r in report):
        return "with_solver"
    return "complete"
