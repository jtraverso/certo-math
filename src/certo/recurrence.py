"""The minimum number of candidate parts, by a recurrence over masks -- and
the whole table as its certificate.

A cover certifies an UPPER bound: here is a partition into k parts. That
does not say k is the minimum, nor that every way was considered, and a user
was checking the lower bounds with Z3 and a second exact auditor. For a
universe small enough to index by bits there is a direct argument:

    f(0) = 0
    f(M) = min over candidates C that contain e = lowest(M)
               [ C inside M, for a partition ]   of   1 + f(M \\ C)

The lowest element of what is left has to be covered by SOME chosen part, so
branching on its candidates loses nothing; that is the whole proof of
optimality, and of exhaustiveness. The table of every state the recurrence
visits, each with its value and the candidate it chose, is checked entry by
entry: each value must be the minimum over its children's stored values,
and every child must be in the table. Nothing is searched by the verifier,
and nothing needs a solver.

Values are `None` where no partition exists (a lowest element no candidate
can take). The table can be large -- every subset the recurrence reaches --
so it is bounded (`max_states`) and the run's clock is read.
"""
from __future__ import annotations

import time

from .i18n import t as _t

MAX_STATES = 2_000_000


class TooLarge(RuntimeError):
    """The table outgrew its bound, or the clock ran out."""


def masks_of(universe, candidates):
    """`(index, masks)`: each element's bit, each candidate as a bit mask.
    A candidate naming something outside the universe is refused."""
    index = {_key(u): i for i, u in enumerate(universe)}
    masks = []
    for c in candidates:
        m = 0
        for e in c:
            k = _key(e)
            if k not in index:
                raise ValueError(_t("recurrence.foreign", element=str(e)))
            m |= 1 << index[k]
        masks.append(m)
    return index, masks


def _key(x):
    if isinstance(x, (list, tuple)):
        return tuple(sorted(_key(v) for v in x)) if all(
            not isinstance(v, (list, tuple)) for v in x) else tuple(_key(v) for v in x)
    return x


def by_lowest(n, masks):
    """For each element, the candidates containing it, in index order."""
    out = [[] for _ in range(n)]
    for j, m in enumerate(masks):
        for e in range(n):
            if m >> e & 1:
                out[e].append(j)
    return out


def options(M, masks, lowest, exact):
    """The transitions of state `M`: `[(candidate, child)]`."""
    e = (M & -M).bit_length() - 1
    out = []
    for j in lowest[e]:
        c = masks[j]
        if exact and c & ~M:
            continue
        out.append((j, M & ~c))
    return out


def solve(n, masks, exact=True, max_states=MAX_STATES, deadline=None):
    """The table `{mask: (value or None, choice or None)}` of every state
    reachable from the full mask."""
    lowest = by_lowest(n, masks)
    table = {0: (0, None)}
    full = (1 << n) - 1
    stack = [full]
    while stack:
        M = stack[-1]
        if M in table:
            stack.pop()
            continue
        if deadline is not None and time.monotonic() > deadline:
            raise TooLarge(_t("recurrence.clock"))
        opts = options(M, masks, lowest, exact)
        pending = [child for _j, child in opts if child not in table]
        if pending:
            stack.extend(pending)
            if len(table) + len(stack) > max_states:
                raise TooLarge(_t("recurrence.too_large", n=max_states))
            continue
        best, choice = None, None
        for j, child in opts:
            v = table[child][0]
            if v is None:
                continue
            if best is None or 1 + v < best:
                best, choice = 1 + v, j
        table[M] = (best, choice)
        stack.pop()
    return table


def reconstruct(table, masks, n):
    """The chosen candidates from the full mask, following the choices."""
    M, out = (1 << n) - 1, []
    while M:
        v, j = table[M]
        if v is None:
            return None
        out.append(j)
        M &= ~masks[j]
    return out


def check(n, masks, exact, table):
    """Every entry against the recurrence. `[(problem, mask)]`, empty when
    the table is right."""
    lowest = by_lowest(n, masks)
    full = (1 << n) - 1
    problems = []
    if full not in table:
        problems.append(("recurrence.no_target", full))
    if table.get(0, (None,))[0] != 0:
        problems.append(("recurrence.bad_base", 0))
    for M, (v, j) in table.items():
        if M == 0:
            continue
        if M & ~full:
            problems.append(("recurrence.outside", M))
            continue
        best = None
        for jj, child in options(M, masks, lowest, exact):
            if child not in table:
                problems.append(("recurrence.missing_child", M))
                best = "missing"
                break
            cv = table[child][0]
            if cv is not None and (best is None or 1 + cv < best):
                best = 1 + cv
        if best == "missing":
            continue
        if v != best:
            problems.append(("recurrence.not_minimum", M))
            continue
        if v is not None:
            if j is None or not (0 <= j < len(masks)) or \
                    (exact and masks[j] & ~M) or not (masks[j] & (M & -M)) or \
                    table.get(M & ~masks[j], (None,))[0] != v - 1:
                problems.append(("recurrence.bad_choice", M))
    return problems
