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

from fractions import Fraction

#: Pivots before giving up. Bland's rule cannot cycle, so hitting this means
#: the problem is genuinely large rather than that the method is stuck.
MAX_PIVOTS = 50_000


class SimplexLimit(RuntimeError):
    """The pivot budget ran out. Not an answer, and not a wrong answer."""


def _pivot(T, basis, row, col):
    """Standard tableau pivot, exactly."""
    piv = T[row][col]
    inv = Fraction(1) / piv
    T[row] = [v * inv for v in T[row]]
    for i in range(len(T)):
        if i != row and T[i][col]:
            f = T[i][col]
            T[i] = [a - f * b for a, b in zip(T[i], T[row])]
    basis[row] = col


def _solve(T, basis, n_cols, budget, deadline=None):
    """Phase 2: pivot until no reduced cost is negative. Bland's rule."""
    import time

    m = len(T)
    while True:
        if deadline is not None and time.monotonic() > deadline:
            raise SimplexLimit("deadline")
        col = next((j for j in range(n_cols) if T[-1][j] < 0), None)
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
        _pivot(T, basis, row, col)


def minimise(A, b, c, deadline=None):
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
    _solve(T, basis, total, budget)

    y = [Fraction(0)] * m
    for i, bi in enumerate(basis):
        if bi < m:
            y[bi] = T[i][-1]
    return y
