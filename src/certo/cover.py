"""An exact cover, checked by counting, and a clique partition as one case of it.

Somebody hands you a clique partition of a graph and says it has 47 parts.
Two things have to be true and neither is obvious by looking: every part
really is a clique, and every edge is covered EXACTLY once -- not zero times,
which would make it not a cover, and not twice, which would make the count a
lie.

Checking that is counting. No solver, no search, no trust in whatever produced
it, which is the whole reason it belongs in a certificate rather than in the
program that built it.

The general object is an EXACT COVER: a universe, and parts, and every element
of the universe in exactly one part. A clique partition of a graph is that,
with the universe being the edge set and each part being the edges of a
clique. So the machinery is written once, generally, and the graph case adds
one extra check -- that a part's edges really are all the edges among its
vertices, which is what makes it a clique rather than an arbitrary edge set.

WHAT THIS IS NOT is a search. Finding a minimum exact cover is NP-hard and
there are tools that do it; this certifies one you already have, and says how
large it is. For the other half -- that no smaller one exists -- the fractional
relaxation's exact dual is a lower bound, and `opt` produces it. When the two
meet, the number is proved, and that pairing is the same one `opt --gap` makes
for packings.

An `at_least` cover (every element covered one or more times) is allowed and
is a different claim, so it is recorded as a different one: the count is still
exact, and "exactly once" is simply not asserted.
"""
from __future__ import annotations

from collections import Counter

from .i18n import t as _t


class NotACover(ValueError):
    """Raised with what is wrong, because "invalid" is not actionable."""


def _key(x):
    """A hashable, order-insensitive id for a universe element.

    An edge given as `(3, 1)` and as `(1, 3)` is one edge. Anything else is
    taken as itself.
    """
    if isinstance(x, (tuple, list, set, frozenset)):
        return tuple(sorted(map(str, x)))
    return str(x)


def check(universe, parts, exact: bool = True) -> dict:
    """Does `parts` cover `universe`, and how many times is each element hit?

    Returns the whole picture rather than a bool: what was missed, what was
    doubled, and the counts. A cover that is wrong is usually wrong in a way
    worth seeing.
    """
    # The pair `clique_parts` returns, passed whole: two "parts", neither of
    # them a set of edges, and every edge reported missed. Refused by name.
    if (isinstance(parts, tuple) and len(parts) == 2
            and isinstance(parts[1], list) and parts[1]
            and all(isinstance(r, dict) and "vertices" in r for r in parts[1])):
        raise TypeError(_t("cover.pair_passed"))
    want = [_key(u) for u in universe]
    if len(set(want)) != len(want):
        dupes = [k for k, n in Counter(want).items() if n > 1]
        raise NotACover(_t("cover.universe_duplicate",
                           names=", ".join(map(str, dupes[:5]))))
    want_set = set(want)

    seen: Counter = Counter()
    foreign = []
    for i, part in enumerate(parts):
        for elem in part:
            k = _key(elem)
            if k not in want_set:
                foreign.append((i, k))
            seen[k] += 1

    missed = sorted(k for k in want_set if not seen[k])
    doubled = sorted(k for k in want_set if seen[k] > 1)
    return {
        "parts": len(parts),
        "universe": len(want_set),
        "covered": len(want_set) - len(missed),
        "missed": missed,
        "doubled": doubled,
        "foreign": foreign,
        "multiplicities": {k: seen[k] for k in sorted(want_set)},
        "ok": not missed and not foreign and (not doubled or not exact),
        "exact": exact,
    }


# ---------------------------------------------------------------------------
# the graph case
# ---------------------------------------------------------------------------


def _ordered(vertices) -> list:
    """The vertex set in ITS OWN order, with a fallback for mixed types.

    This used to be `sorted(set(vertices), key=str)` unconditionally, which
    sorts integer labels as text: `10` before `2`. So a clique on `{2, 10}`
    came out as the edge `(10, 2)` -- the larger vertex first -- and a caller
    who canonicalised numerically, as anybody would, was comparing against
    `(2, 10)` and finding a foreign edge.

    `_key` is order-insensitive, so certo's own comparisons survived it. What
    did not survive is the ORDER THAT TRAVELS: the certificate carried
    `(10, 2)`, and the same certificate carried the vertices in the caller's
    order, so one artefact held two orderings of one object.

    `key=str` was there for a reason -- labels of mixed types have no order
    between them and `sorted` raises. So the natural order is tried first and
    the text order is the fallback, which is the case that needs a rule rather
    than the case that has one.
    """
    vs = set(vertices)
    try:
        return sorted(vs)
    except TypeError:
        return sorted(vs, key=str)


def edges_of(vertices) -> list:
    """Every pair from a vertex set, as sorted tuples."""
    vs = _ordered(vertices)
    return [(vs[i], vs[j]) for i in range(len(vs)) for j in range(i + 1, len(vs))]


def clique_parts(edges, vertex_sets, max_size=None):
    """Turn vertex sets into cover parts, refusing any that is not a clique.

    Returns `(parts, report)`: the parts as edge lists, which is what `check`
    takes, and one `{"vertices", "edges"}` per part. Pass `parts` to `check`,
    not the pair -- a user did, and got "covered 0" for a correct partition.

    This is the check the general cover machinery cannot make: a part is a set
    of edges, and nothing about a set of edges says it came from a clique. A
    vertex set whose internal pairs are not all present in the graph would
    still cover edges, and the cover would verify, and the object would not be
    a clique partition.
    """
    present = {_key(e) for e in edges}
    parts, report = [], []
    for vs in vertex_sets:
        vs = list(vs)
        if len(set(map(str, vs))) != len(vs):
            raise NotACover(_t("cover.part_repeats", part=str(vs)))
        if len(vs) < 2:
            raise NotACover(_t("cover.part_small", part=str(vs)))
        if max_size is not None and len(vs) > max_size:
            raise NotACover(_t("cover.part_big", part=str(vs),
                               size=len(vs), cap=max_size))
        own = edges_of(vs)
        absent = [e for e in own if _key(e) not in present]
        if absent:
            raise NotACover(_t("cover.not_a_clique", part=str(vs),
                               missing=", ".join(map(str, absent[:4]))))
        parts.append(own)
        report.append({"vertices": [str(v) for v in vs], "edges": len(own)})
    return parts, report


# ---------------------------------------------------------------------------
# a repair of a partition somebody handed you
# ---------------------------------------------------------------------------


def check_repair(repair, universe, cliques=False):
    """Is `repair` an admissible change of the partition it names?

    `repair` is `{"before": {owner: part}, "withdraw": [owner, ...],
    "insert": {owner: part}, "frozen": [owner, ...], "new": [resource, ...],
    "balance": int or None}`, parts being vertex sets when `cliques`. The
    claim is about the CHANGE, not only its result: a final cover can be
    valid and the change still inadmissible -- a frozen owner replaced, or an
    edge taken from an owner that was not withdrawn just because the edge is
    there in the graph.

    Returns `{"ok", "problems": [(key, values)], "final": {owner: part},
    "order": [owner, ...]}`. `final` is the partition after the change, in
    a fixed order: the kept owners as `before` lists them, then the inserted.
    Called by `cover` and by `verify`, so the two cannot read a repair two
    ways.
    """
    before = dict(repair.get("before") or {})
    withdraw = [str(o) for o in repair.get("withdraw") or []]
    insert = dict(repair.get("insert") or {})
    frozen = [str(o) for o in repair.get("frozen") or []]
    new = list(repair.get("new") or [])
    balance = repair.get("balance")
    before = {str(k): v for k, v in before.items()}
    insert = {str(k): v for k, v in insert.items()}
    problems = []

    def resources(part):
        return [_key(e) for e in (edges_of(part) if cliques else part)]

    unknown = [o for o in withdraw if o not in before]
    if unknown:
        problems.append(("cover.repair.unknown_owner", {"owners": unknown}))
    twice = sorted(o for o, n in Counter(withdraw).items() if n > 1)
    if twice:
        problems.append(("cover.repair.withdrawn_twice", {"owners": twice}))
    missing_frozen = [o for o in frozen if o not in before]
    if missing_frozen:
        problems.append(("cover.repair.unknown_owner", {"owners": missing_frozen}))
    touched = [o for o in frozen if o in set(withdraw)]
    if touched:
        problems.append(("cover.repair.frozen_withdrawn", {"owners": touched}))
    kept = [o for o in before if o not in set(withdraw)]
    clash = [o for o in insert if o in set(kept)]
    if clash:
        problems.append(("cover.repair.owner_clash", {"owners": clash}))

    # The resource freed -- the withdrawn owners' and the declared new --
    # must be exactly what the inserted pieces cover. Exactly: a piece that
    # reaches an element of a KEPT owner takes it, whether or not the element
    # is in the graph.
    freed = Counter()
    for o in withdraw:
        if o in before:
            freed.update(resources(before[o]))
    freed.update(_key(e) for e in new)
    placed = Counter()
    for part in insert.values():
        placed.update(resources(part))
    owner_of = {}
    for o in kept:
        for r in resources(before[o]):
            owner_of.setdefault(r, o)
    taken = sorted(r for r in placed if (placed[r] > freed[r]) and r in owner_of)
    if taken:
        problems.append(("cover.repair.takes_other",
                         {"resources": taken,
                          "owners": sorted({owner_of[r] for r in taken})}))
    extra = sorted(r for r in placed if placed[r] > freed[r] and r not in owner_of)
    if extra:
        problems.append(("cover.repair.not_freed", {"resources": extra}))
    left = sorted(r for r in freed if freed[r] > placed[r])
    if left:
        problems.append(("cover.repair.left_uncovered", {"resources": left}))
    if balance is not None and int(balance) != len(insert) - len(set(withdraw)):
        problems.append(("cover.repair.balance",
                         {"declared": int(balance),
                          "actual": len(insert) - len(set(withdraw))}))

    # The universe the final cover is about: what `before` covered, and the
    # resource declared new. Not a larger graph the pieces happen to fit in.
    covered = set()
    for part in before.values():
        covered.update(resources(part))
    covered.update(_key(e) for e in new)
    if covered != {_key(u) for u in universe}:
        problems.append(("cover.repair.universe",
                         {"extra": sorted({_key(u) for u in universe} - covered)[:4],
                          "missing": sorted(covered - {_key(u) for u in universe})[:4]}))

    order = kept + [o for o in insert if o not in set(kept)]
    final = {o: (before[o] if o in before and o in set(kept) else insert[o])
             for o in order}
    return {"ok": not problems, "problems": problems, "final": final,
            "order": order}


def repair_text(problems) -> str:
    """The problems of a repair as one readable line."""
    out = []
    for key, values in problems:
        flat = {k: ", ".join(map(str, v[:4])) if isinstance(v, list) else v
                for k, v in values.items()}
        out.append(_t(key, **flat))
    return "; ".join(out)
