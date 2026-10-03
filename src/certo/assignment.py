"""Items to receivers under capacities -- an assignment, and why no larger one.

Pages each go to one of the receivers they are allowed, every receiver takes
at most its capacity. How many can be placed at most? A max flow answers, and
it answers integrally. What makes it a CERTIFICATE is the other half, which is
Hall's condition counted: for any set `U` of receivers,

    every placed item either lands in U        (at most cap(U) of them)
    or is allowed somewhere outside U          (at most the items NOT confined to U)

so no assignment places more than `cap(U) + |items not confined to U|`. An
assignment that reaches that number for some `U` is maximum, and the pair --
the assignment and `U` -- is checked by counting. No solver, no matrix: a
model of the problem as an LP would certify an exact optimum of whatever
matrix was written, and the matrix is exactly what users got wrong by hand.
Here the data IS the problem.

`U = {}` says there are not enough items; `U` = every receiver says there is
not enough capacity; anything between is a bottleneck, and it is named.
"""
from __future__ import annotations

from collections import deque

from .i18n import t as _t


class NotAnAssignment(ValueError):
    """The data cannot be read as an assignment problem; says why."""


def _key(x) -> str:
    return str(x)


def normalise(items, allowed, capacities):
    """`(items, allowed, capacities)` with string keys, validated."""
    items = [_key(i) for i in items]
    if len(set(items)) != len(items):
        raise NotAnAssignment(_t("assign.items_repeat"))
    caps = {}
    for r, c in (capacities or {}).items():
        if not isinstance(c, int) or isinstance(c, bool) or c < 0:
            raise NotAnAssignment(_t("assign.bad_capacity", receiver=r, value=c))
        caps[_key(r)] = c
    amap = {_key(k): v for k, v in (allowed or {}).items()}
    allow = {}
    for i in items:
        rs = [_key(r) for r in amap.get(i, [])]
        unknown = [r for r in rs if r not in caps]
        if unknown:
            raise NotAnAssignment(_t("assign.unknown_receiver", item=i,
                                     receivers=", ".join(unknown[:4])))
        allow[i] = sorted(set(rs))
    extra = [k for k in (allowed or {}) if _key(k) not in set(items)]
    if extra:
        raise NotAnAssignment(_t("assign.unknown_item",
                                 items=", ".join(map(str, extra[:4]))))
    return items, allow, caps


def solve(items, allow, caps):
    """A maximum assignment `{item: receiver}` and its Hall set `U`.

    Augmenting paths on the bipartite graph with receiver capacities (a max
    flow with unit item edges); `U` is the receivers reachable from an
    unassigned item, or from the source side of the minimum cut, in the
    residual graph -- the standard reading, and the verifier does not rely
    on it: it recounts the bound.
    """
    assign = {}
    load = {r: 0 for r in caps}
    holders = {r: [] for r in caps}

    def augment(start):
        # BFS from an unassigned item over: item -> allowed receiver;
        # a receiver with room ends the path; a full one -> an item it holds.
        prev_r, prev_i = {}, {start: None}
        queue = deque([start])
        while queue:
            i = queue.popleft()
            for r in allow[i]:
                if r in prev_r:
                    continue
                prev_r[r] = i
                if load[r] < caps[r]:
                    # Walk back, flipping the path: each item moves to the
                    # receiver after it, freeing its old place for the item
                    # before it. Only the END receiver gains a load.
                    load[r] += 1
                    while True:
                        item = prev_r[r]
                        old = assign.get(item)
                        assign[item] = r
                        holders[r].append(item)
                        if old is None:
                            return True
                        holders[old].remove(item)
                        r = old
                for j in holders[r]:
                    if j not in prev_i:
                        prev_i[j] = r
                        queue.append(j)
        return False

    for i in items:
        if allow[i]:
            augment(i)

    # Hall set: receivers reachable in the residual graph from any item left
    # unassigned (through full receivers and the items they hold).
    seen_r, seen_i = set(), set()
    queue = deque(i for i in items if i not in assign)
    seen_i.update(queue)
    while queue:
        i = queue.popleft()
        for r in allow[i]:
            if r not in seen_r:
                seen_r.add(r)
                for j in holders[r]:
                    if j not in seen_i:
                        seen_i.add(j)
                        queue.append(j)
    return assign, sorted(seen_r)


def bound(items, allow, caps, U) -> dict:
    """`cap(U) + |items not confined to U|`, and its two parts."""
    U = set(U)
    confined = [i for i in items if set(allow[i]) <= U]
    return {"capacity": sum(caps[r] for r in U), "not_confined":
            len(items) - len(confined), "confined": len(confined),
            "value": sum(caps[r] for r in U) + len(items) - len(confined)}


def check(payload) -> dict:
    """Recount everything a certificate says. Returns `{ok, problems, size,
    bound}`; the verifier and the engine read the data the same way."""
    problems = []
    try:
        items, allow, caps = normalise(payload["items"], payload["allowed"],
                                       payload["capacities"])
    except (NotAnAssignment, KeyError, TypeError, AttributeError) as e:
        return {"ok": False, "problems": [str(e)], "legal": [str(e)],
                "hall": [], "size": 0, "bound": None}
    assign = {str(k): str(v) for k, v in (payload.get("assignment") or {}).items()}
    for i, r in assign.items():
        if i not in allow:
            problems.append(_t("assign.check.unknown_item", item=i))
        elif r not in allow[i]:
            problems.append(_t("assign.check.not_allowed", item=i, receiver=r))
    load = {}
    for r in assign.values():
        load[r] = load.get(r, 0) + 1
    over = sorted(r for r, n in load.items() if n > caps.get(r, 0))
    if over:
        problems.append(_t("assign.check.overload", receivers=", ".join(over[:4])))
    size = len(assign)
    if int(payload.get("size", size)) != size:
        problems.append(_t("assign.check.size", declared=payload.get("size"),
                           actual=size))
    hall = []
    U = [str(r) for r in (payload.get("hall") or {}).get("U", [])]
    if any(r not in caps for r in U):
        hall.append(_t("assign.check.unknown_receiver"))
        U = [r for r in U if r in caps]
    b = bound(items, allow, caps, U)
    declared = payload.get("hall") or {}
    for key in ("capacity", "not_confined", "value"):
        if declared.get(key) is not None and int(declared[key]) != b[key]:
            hall.append(_t("assign.check.declared", field=key,
                           declared=declared[key], actual=b[key]))
    if b["value"] != size:
        hall.append(_t("assign.check.not_tight", size=size, bound=b["value"]))
    return {"ok": not problems and not hall, "problems": problems + hall,
            "legal": problems, "hall": hall, "size": size, "bound": b}
