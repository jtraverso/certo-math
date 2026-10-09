"""A two-phase simplex in exact rationals, for when reconstruction runs out.

`exact.certify` reconstructs a rational primal and dual from a float solver
and checks them. That works, and there is a regime where it cannot: a
DEGENERATE optimum, where many dual solutions are optimal and the one CBC
happens to return need not round onto any of them.

0.6.0 answered that by deriving the dual from complementary slackness and
enumerating which tight rows carry the weight. Measured on a realistic exact
cover -- 98 rows, 49 of them tight, 7 active variables -- that is C(49, 7)
candidate bases, about 10^8. The approach is right for a handful of tight rows
and hopeless past it, and saying so is more useful than raising the cap.

So: solve the dual outright, in `Fraction`, with no floats anywhere.

    max c.x  s.t.  A x <= b, x >= 0        has dual
    min b.y  s.t.  A^T y >= c, y >= 0

The origin is infeasible for the dual whenever `c` has a positive entry, which
is almost always, so phase 1 finds a feasible point and phase 2 optimises from
it. BLAND'S RULE throughout -- always the smallest eligible index -- which is
slower than steepest-edge and cannot cycle. Termination matters more than
speed here: this runs only when the cheap route has already failed, and an
answer that never comes is worse than a slow one.

Nothing produced here is trusted for being produced here. `certify` puts the
result through the same `check_lp` as a rounded guess, and a bug in this file
shows up as a certificate that does not verify rather than as a wrong one that
does.
"""
from __future__ import annotations

from .rational import Q as Fraction, to_fraction

#: Pivots before giving up. Bland's rule cannot cycle, so hitting this means
#: the problem is genuinely large rather than that the method is stuck.
MAX_PIVOTS = 50_000

#: A program at least this WIDE -- columns per row, and columns -- is solved
#: as the primal, and its dual read off the slacks. Solving the dual outright
#: puts one tableau row per primal column: 4130 columns and 22 rows made a
#: 4130 x 8282 tableau of `Fraction`s, about 34 million entries updated on
#: every pivot, and a reconstruction ran for minutes. The primal tableau is
#: 22 x 4174. Narrow programs keep the dual route, so what they return --
#: which optimal dual, when there are several -- does not change.
WIDE_RATIO = 4
WIDE_FROM = 200


class SimplexLimit(RuntimeError):
    """The pivot budget ran out. Not an answer, and not a wrong answer."""


def _pivot(T, basis, row, col):
    """Standard tableau pivot, exactly. Only the pivot row's NON-ZERO
    positions change the other rows: on a wide sparse program most of a row
    is zero, and subtracting `f * 0` thousands of times was the cost."""
    piv = T[row][col]
    inv = Fraction(1) / piv
    prow = [v * inv for v in T[row]]
    T[row] = prow
    nz = [j for j, v in enumerate(prow) if v]
    for i in range(len(T)):
        if i != row and T[i][col]:
            f = T[i][col]
            r = T[i]
            for j in nz:
                r[j] -= f * prow[j]
    basis[row] = col


#: Degenerate pivots in a row before Dantzig's rule gives way to Bland's,
#: which cannot cycle.
DEGENERATE_STREAK = 50


def _solve(T, basis, n_cols, budget, deadline=None, prefer=None):
    """Pivot until no reduced cost is negative. Bland's rule -- or, with
    `prefer` (column indices, best first), those columns first and then
    Dantzig's most negative reduced cost, falling back to Bland's after a
    streak of degenerate pivots so that it still terminates."""
    import time

    m = len(T)
    bland = prefer is None
    streak = 0
    while True:
        if deadline is not None and time.monotonic() > deadline:
            raise SimplexLimit("deadline")
        obj = T[-1]
        if bland:
            col = next((j for j in range(n_cols) if obj[j] < 0), None)
        else:
            col = next((j for j in prefer if j < n_cols and obj[j] < 0), None)
            if col is None:
                neg = [(obj[j], j) for j in range(n_cols) if obj[j] < 0]
                col = min(neg)[1] if neg else None
        if col is None:
            return
        # Ratio test, smallest basis index on a tie: the other half of Bland.
        best, row = None, None
        for i in range(m - 1):
            if T[i][col] > 0:
                ratio = T[i][-1] / T[i][col]
                if best is None or ratio < best or (
                        ratio == best and basis[i] < basis[row]):
                    best, row = ratio, i
        if row is None:
            raise SimplexLimit("unbounded")
        budget[0] -= 1
        if budget[0] < 0:
            raise SimplexLimit("pivot budget")
        if not bland:
            streak = streak + 1 if best == 0 else 0
            if streak >= DEGENERATE_STREAK:
                bland = True
        _pivot(T, basis, row, col)


def _crash(A, b, c, x_hint, deadline):
    """The float solver's basis, entered exactly: `(T, basis)` primal
    feasible, or None.

    Start from the all-slack tableau, rhs as it is, and pivot each column the
    float primal uses into a row whose slack is TIGHT there -- Gaussian
    elimination rather than a ratio test, because the point is to reach that
    basis, not to stay feasible on the way. If the basis reached has a
    non-negative right-hand side it is a feasible vertex, and phase 2 starts
    from it; usually a handful of pivots from the optimum. Otherwise the
    caller runs the two phases from scratch.
    """
    import time

    m, n = len(A), len(c)
    total = n + m
    T = []
    for i in range(m):
        row = list(A[i]) + [Fraction(0)] * m
        row[n + i] = Fraction(1)
        T.append(row + [b[i]])
    basis = [n + i for i in range(m)]
    xs = [float(v or 0.0) for v in x_hint]
    slack = [float(b[i]) - sum(float(A[i][j]) * xs[j] for j in range(n) if xs[j])
             for i in range(m)]
    support = sorted((j for j in range(n) if xs[j] > 1e-9), key=lambda j: -xs[j])
    for j in support[:m]:
        if deadline is not None and time.monotonic() > deadline:
            raise SimplexLimit("deadline")
        rows = [i for i in range(m) if basis[i] >= n and T[i][j] != 0]
        if not rows:
            continue                       # dependent on the columns already in
        row = min(rows, key=lambda i: (abs(slack[basis[i] - n]), i))
        _pivot(T, basis, row, j)
    if any(t[-1] < 0 for t in T):
        return None
    return T, basis


def _primal_dual(A, b, c, deadline, hint=None, x_hint=None):
    """`max c.x` s.t. `A x <= b`, `x >= 0`, by the primal tableau; returns the
    optimal DUAL `y`, read as the reduced costs of the slack columns.

    A reduced cost does not change when a row is multiplied by -1, so the
    rows flipped to make the right-hand side non-negative need no
    correction. Two phases, Bland's rule, the same budget and deadline as the
    dual route; an unbounded primal is an infeasible dual and is raised as
    such.
    """
    m, n = len(A), len(c)
    total = n + m                                 # x, then slacks
    budget = [MAX_PIVOTS]
    crashed = _crash(A, b, c, x_hint, deadline) if x_hint is not None else None
    if crashed is not None:
        T, basis = crashed
        obj = [-Fraction(v) for v in c] + [Fraction(0)] * m + [Fraction(0)]
        for i, bi in enumerate(basis):
            if obj[bi]:
                f = obj[bi]
                obj = [o - f * v for o, v in zip(obj, T[i])]
        T.append(obj)
        _solve(T, basis, total, budget, deadline, prefer=list(hint or []))
        return [T[-1][n + i] for i in range(m)]

    T, basis, flipped = [], [], []
    for i in range(m):
        row = list(A[i]) + [Fraction(0)] * m
        row[n + i] = Fraction(1)
        r = b[i]
        if r < 0:
            row = [-v for v in row]
            r = -r
            flipped.append(i)
        T.append(row + [r])

    # Phase 1: an artificial for every flipped row (the others start basic
    # on their own slack).
    art = {i: total + k for k, i in enumerate(flipped)}
    width = total + len(flipped)
    for i, t in enumerate(T):
        extra = [Fraction(0)] * len(flipped)
        if i in art:
            extra[art[i] - total] = Fraction(1)
        T[i] = t[:-1] + extra + [t[-1]]
        basis.append(art.get(i, n + i))
    if flipped:
        cost = [Fraction(0)] * (width + 1)
        for i in flipped:
            for j in range(width + 1):
                cost[j] -= T[i][j]
        for a in art.values():
            cost[a] = Fraction(0)
        T.append(cost)
        _solve(T, basis, width, budget, deadline, prefer=list(hint or []))
        if T[-1][-1] != 0:
            raise SimplexLimit("the primal is infeasible")
        T.pop()
        for i in range(len(basis) - 1, -1, -1):
            if basis[i] < total:
                continue
            col = next((j for j in range(total) if T[i][j] != 0), None)
            if col is None:
                del T[i]
                del basis[i]
                continue
            _pivot(T, basis, i, col)
    for t in T:
        del t[total:width]

    # Phase 2: maximise c.x, written as reduced costs `-c` to be driven >= 0.
    obj = [-Fraction(v) for v in c] + [Fraction(0)] * m + [Fraction(0)]
    for i, bi in enumerate(basis):
        if obj[bi]:
            f = obj[bi]
            obj = [o - f * v for o, v in zip(obj, T[i])]
    T.append(obj)
    # The float solver's support enters first: on a degenerate program the
    # optimal basis is almost known, and Bland's rule alone took 6970 pivots
    # on 22 rows to find it again.
    _solve(T, basis, total, budget, deadline, prefer=list(hint or []))
    return [T[-1][n + i] for i in range(m)]


def minimise(A, b, c, deadline=None, hint=None, x_hint=None):
    """`min b.y` subject to `A^T y >= c`, `y >= 0`, exactly.

    Takes the PRIMAL data and solves that primal's dual, because that is the
    only thing this is ever used for and passing the transpose around at every
    call site invites getting it the wrong way round once.

    Returns the optimal `y` as a list of `Fraction`, or raises.
    """
    A = [[Fraction(v) for v in row] for row in A]
    b = [Fraction(v) for v in b]
    c = [Fraction(v) for v in c]
    m, n = len(A), len(c)                       # y has m entries, n rows
    if n >= WIDE_FROM and n >= WIDE_RATIO * max(m, 1):
        return [to_fraction(v) for v in _primal_dual(A, b, c, deadline, hint, x_hint)]

    # `A^T y >= c`  ->  `-A^T y + s = -c`, s >= 0, with an artificial where
    # the right-hand side is negative.
    rows, rhs = [], []
    for j in range(n):
        rows.append([-A[i][j] for i in range(m)])
        rhs.append(-c[j])

    total = m + n                                # y, then slacks
    T, basis, artificial = [], [], []
    for j in range(n):
        row = list(rows[j]) + [Fraction(0)] * n
        row[m + j] = Fraction(1)
        r = rhs[j]
        if r < 0:                                # flip so the rhs is >= 0
            row = [-v for v in row]
            r = -r
        T.append(row + [r])

    # Phase 1: one artificial per row, minimise their sum.
    for i in range(n):
        for k, t in enumerate(T):
            t.insert(total + i, Fraction(1) if k == i else Fraction(0))
        artificial.append(total + i)
        basis.append(total + i)
    width = total + n

    cost = [Fraction(0)] * width + [Fraction(0)]
    for i in range(n):
        for j in range(width + 1):
            cost[j] -= T[i][j]
    for a in artificial:
        cost[a] = Fraction(0)
    T.append(cost)

    budget = [MAX_PIVOTS]
    _solve(T, basis, width, budget, deadline)
    if -T[-1][-1] != 0:
        raise SimplexLimit("the dual is infeasible")

    # An artificial can END phase 1 still in the basis, at level zero, when
    # the rows are dependent -- which they routinely are here, because the
    # rows are one per monomial and monomials are not independent. Renaming
    # such a basic variable to a real one would state a false tableau: the
    # column it names is not the column the row was solved for. So drive it
    # out by a real pivot, and when the whole row is zero across the real
    # columns the row is redundant and is dropped.
    for i in range(len(basis) - 1, -1, -1):
        if basis[i] < total:
            continue
        col = next((j for j in range(total) if T[i][j] != 0), None)
        if col is None:
            del T[i]
            del basis[i]
            continue
        _pivot(T, basis, i, col)

    # Phase 2: drop the artificials, minimise b.y  ->  maximise -b.y.
    for t in T:
        del t[total:width]
    T.pop()
    obj = [Fraction(0)] * total + [Fraction(0)]
    for i in range(m):
        obj[i] = Fraction(b[i])
    for i, bi in enumerate(basis):
        if obj[bi]:
            f = obj[bi]
            for j in range(total + 1):
                obj[j] -= f * T[i][j]
    T.append(obj)
    _solve(T, basis, total, budget, deadline)

    y = [Fraction(0)] * m
    for i, bi in enumerate(basis):
        if bi < m:
            y[bi] = T[i][-1]
    return [to_fraction(v) for v in y]
