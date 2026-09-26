"""Integer matrices: rank, determinant, Hermite and Smith, with the
transforms that make every answer checkable by integer multiplication.

A determinant computed by floating point is a number somebody has to trust.
A determinant computed by exact elimination is a number somebody has to
RERUN. Neither is a certificate. What this module produces is:

    U . A = H          U unimodular, H in Hermite normal form
    U . A . V = S      U, V unimodular, S the Smith normal form

together with the INVERSES of the transforms. That turns every claim into
integer matrix multiplication, and integer matrix multiplication is something
a referee, a script, or Lean can redo without redoing the elimination:

    U . U_inv = I                 so det(U) = +1 or -1, and nothing else
    U . A = H                     so A and H have the same row lattice
    H echelon with r pivots       so rank(A) = r, because U is invertible
    det(A) = det(U) . prod h_ii   for a square A, because det(H) = prod h_ii

THE SIGN IS THE ONE INTERESTING PART. `U . U_inv = I` pins |det(U)| to 1 and
says nothing about which sign, and the sign of det(U) is the sign of det(A).
Recomputing det(U) over the integers would cost as much as the elimination we
are trying not to repeat. But det(U) is ALREADY KNOWN to be +1 or -1, and
those two are distinct modulo any odd prime -- so one determinant of U modulo
a word-sized prime, where no entry ever grows, settles it exactly. Not
probably: exactly, because there were only ever two candidates.

WHY HERMITE AND SMITH AND NOT AN INVERSE. `A^-1` answers one question about
one square matrix. The row lattice answers several, about any shape:

    rank                    how many pivots H has
    determinant             the product of H's diagonal, up to det(U)
    a minor                 the same question on a submatrix
    solvability of Ax = b   over the integers, not just the rationals
    the group Z^n / A Z^m   the invariant factors on S's diagonal

and the last one is the reason Smith is here at all. The torsion of a
quotient by a lattice is a finite computation with a finite certificate, and
it is the kind of fact a write-up states in one line and nobody checks.

WHAT IS NOT CLAIMED. That H is the ONLY Hermite form of A -- it is, by
uniqueness, but uniqueness is a theorem about the definition and not
something these checks establish; they establish that H IS in the form and
IS equivalent to A. Same for S. And nothing here says the matrix you wrote
down is the matrix your paper is about.
"""
from __future__ import annotations

from .i18n import t as _t

# A word-sized prime. Any odd prime settles a sign that is known to be
# +1 or -1; this one is large enough that the modular elimination below
# never needs more than machine-sized arithmetic to stay honest.
SIGN_PRIME = (1 << 31) - 1


class NotAnIntegerMatrix(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


# --- the matrix as data ----------------------------------------------------


def parse(rows, name="matrix") -> list:
    """A rectangular matrix of Python integers, or a refusal that says why."""
    if not rows:
        raise NotAnIntegerMatrix(_t("lattice.empty", name=name))
    out = []
    width = None
    for i, row in enumerate(rows):
        vals = []
        for v in row:
            # `int(2.5)` is 2 and raises nothing, so the check comes FIRST:
            # a matrix quietly rounded is a different matrix.
            if isinstance(v, bool) or not isinstance(v, int):
                num = getattr(v, "numerator", None)
                if num is None or getattr(v, "denominator", 0) != 1:
                    raise NotAnIntegerMatrix(
                        _t("lattice.not_integer", name=name, row=i))
                v = num
            vals.append(int(v))
        if width is None:
            width = len(vals)
        elif len(vals) != width:
            raise NotAnIntegerMatrix(_t("lattice.ragged", name=name, row=i,
                                        got=len(vals), want=width))
        out.append(vals)
    if not width:
        raise NotAnIntegerMatrix(_t("lattice.empty", name=name))
    return out


def shape(M) -> tuple:
    return len(M), len(M[0])


def identity(n) -> list:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def multiply(A, B) -> list:
    """Exact integer matrix product: the operation every check reduces to."""
    if len(A[0]) != len(B):
        raise NotAnIntegerMatrix(_t("lattice.shapes", a=shape(A), b=shape(B)))
    cols = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) for col in cols]
            for row in A]


def is_identity(M) -> bool:
    n, m = shape(M)
    return n == m and all(M[i][j] == (1 if i == j else 0)
                          for i in range(n) for j in range(m))


def det_mod(M, p=SIGN_PRIME) -> int:
    """The determinant modulo a prime, by elimination that cannot grow.

    Used for exactly one thing: a quantity already known to be +1 or -1, and
    for that this is not an estimate but a decision.
    """
    n, _ = shape(M)
    A = [[v % p for v in row] for row in M]
    det = 1
    for k in range(n):
        piv = next((i for i in range(k, n) if A[i][k]), None)
        if piv is None:
            return 0
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            det = (-det) % p
        det = (det * A[k][k]) % p
        inv = pow(A[k][k], p - 2, p)
        for i in range(k + 1, n):
            if A[i][k]:
                f = (A[i][k] * inv) % p
                A[i] = [(a - f * b) % p for a, b in zip(A[i], A[k])]
    return det % p


def unimodular_sign(U) -> int:
    """+1 or -1 for a matrix already known to be unimodular, else 0."""
    d = det_mod(U)
    if d == 1:
        return 1
    if d == SIGN_PRIME - 1:
        return -1
    return 0


# --- elimination that records what it did ----------------------------------


class _Row:
    """Row operations on M, mirrored into U and U_inv.

    The invariant, maintained by every method here:

        U . A = M        and        U . U_inv = I

    A left multiplication `M <- E.M` needs `U <- E.U`, and then `U_inv` must
    absorb `E^-1` on the RIGHT to keep the second identity -- which makes it
    a column operation. That asymmetry is the whole trick, and it is why the
    inverse comes out for free instead of being computed afterwards.
    """

    def __init__(self, M):
        self.M = [list(r) for r in M]
        n = len(M)
        self.U = identity(n)
        self.U_inv = identity(n)
        self.sign = 1              # det(U), tracked as it is built

    def swap(self, i, j):
        if i == j:
            return
        self.M[i], self.M[j] = self.M[j], self.M[i]
        self.U[i], self.U[j] = self.U[j], self.U[i]
        for row in self.U_inv:                    # columns i and j
            row[i], row[j] = row[j], row[i]
        self.sign = -self.sign

    def negate(self, i):
        self.M[i] = [-v for v in self.M[i]]
        self.U[i] = [-v for v in self.U[i]]
        for row in self.U_inv:
            row[i] = -row[i]
        self.sign = -self.sign

    def addmul(self, i, j, c):
        """row_i <- row_i + c . row_j. Determinant unchanged."""
        if not c or i == j:
            return
        self.M[i] = [a + c * b for a, b in zip(self.M[i], self.M[j])]
        self.U[i] = [a + c * b for a, b in zip(self.U[i], self.U[j])]
        for row in self.U_inv:                    # col_j -= c . col_i
            row[j] -= c * row[i]


class _Col:
    """The same, on columns: `M <- M.F`, `V <- V.F`, `V_inv <- F^-1 . V_inv`."""

    def __init__(self, n):
        self.V = identity(n)
        self.V_inv = identity(n)
        self.sign = 1

    def swap(self, M, i, j):
        if i == j:
            return
        for row in (M, self.V):
            for r in row:
                r[i], r[j] = r[j], r[i]
        self.V_inv[i], self.V_inv[j] = self.V_inv[j], self.V_inv[i]
        self.sign = -self.sign

    def negate(self, M, i):
        for rows in (M, self.V):
            for r in rows:
                r[i] = -r[i]
        self.V_inv[i] = [-v for v in self.V_inv[i]]
        self.sign = -self.sign

    def addmul(self, M, i, j, c):
        """col_i <- col_i + c . col_j."""
        if not c or i == j:
            return
        for rows in (M, self.V):
            for r in rows:
                r[i] += c * r[j]
        self.V_inv[j] = [a - c * b for a, b in
                         zip(self.V_inv[j], self.V_inv[i])]


# --- Hermite ---------------------------------------------------------------


def hermite(A) -> dict:
    """Row-style Hermite normal form, with U, U_inv and det(U).

    Column by column: clear the column below the pivot row by the Euclidean
    algorithm expressed as row operations, normalise the pivot positive, then
    reduce everything ABOVE it into [0, pivot). What comes out is echelon,
    with positive pivots and reduced entries above them -- which is the
    definition, and which is unique for a given row lattice.
    """
    st = _Row(A)
    n, m = shape(st.M)
    r = 0
    pivots = []

    for c in range(m):
        if r >= n:
            break
        # the Euclidean algorithm, as row operations
        while True:
            nz = [i for i in range(r, n) if st.M[i][c]]
            if not nz:
                break
            best = min(nz, key=lambda i: abs(st.M[i][c]))
            st.swap(r, best)
            rest = [i for i in range(r + 1, n) if st.M[i][c]]
            if not rest:
                break
            for i in rest:
                st.addmul(i, r, -(st.M[i][c] // st.M[r][c]))

        if r < n and st.M[r][c]:
            if st.M[r][c] < 0:
                st.negate(r)
            for i in range(r):
                q = st.M[i][c] // st.M[r][c]
                st.addmul(i, r, -q)
            pivots.append(c)
            r += 1

    return {"h": st.M, "u": st.U, "u_inv": st.U_inv, "det_u": st.sign,
            "rank": r, "pivots": pivots}


def is_hermite(H, pivots) -> bool:
    """The shape, as a check and not as a promise."""
    n, m = shape(H)
    # Each pivot a column index IN RANGE. Python reads -1 as the last column,
    # so [-1, 0] passed as "strictly increasing" and let a matrix that is not
    # triangular through -- and the determinant was then read off its
    # diagonal as 0 for a matrix whose determinant is -1.
    if any(not isinstance(c, int) or isinstance(c, bool) or not 0 <= c < m
           for c in pivots):
        return False
    if len(pivots) > min(n, m) or sorted(set(pivots)) != list(pivots):
        return False
    for r, c in enumerate(pivots):
        if H[r][c] <= 0:
            return False
        if any(H[r][j] for j in range(c)):
            return False
        if any(not (0 <= H[i][c] < H[r][c]) for i in range(r)):
            return False
    return all(not any(H[i]) for i in range(len(pivots), n))


# --- Smith -----------------------------------------------------------------


def smith(A) -> dict:
    """Smith normal form: U.A.V = S, diagonal, with s_i dividing s_{i+1}.

    Alternate row and column clearing at position t until the pivot is alone
    in its row and column, then make sure it divides everything left in the
    remaining block -- adding the offending row into the pivot row and
    starting that position over, which is what makes the divisibility chain
    come out rather than being imposed at the end.
    """
    st = _Row(A)
    n, m = shape(st.M)
    cols = _Col(m)
    M = st.M
    k = min(n, m)
    t = 0

    while t < k:
        piv = _find_pivot(M, t, n, m)
        if piv is None:
            break
        i0, j0 = piv
        # row transforms live in U, column transforms in V, and neither
        # leaks into the other -- which is why one swap needs two calls
        st.swap(t, i0)
        cols.swap(M, t, j0)

        while True:
            _clear_column(st, M, t, n)
            if _clear_row(cols, M, t, m):
                continue                      # the column may have refilled
            break

        bad = _not_divisible(M, t, n, m)
        if bad is not None:
            st.addmul(t, bad[0], 1)           # bring the offender into range
            continue                          # and redo this position

        if M[t][t] < 0:
            st.negate(t)
        t += 1

    _chain(st, cols, M, min(t, k))
    diag = [M[i][i] for i in range(k)]
    return {"s": M, "u": st.U, "u_inv": st.U_inv, "v": cols.V,
            "v_inv": cols.V_inv, "det_u": st.sign, "det_v": cols.sign,
            "invariants": [d for d in diag if d], "rank": sum(1 for d in diag
                                                              if d)}


def _find_pivot(M, t, n, m):
    """The smallest nonzero entry of the remaining block, by absolute value."""
    best = None
    for i in range(t, n):
        for j in range(t, m):
            if M[i][j] and (best is None or abs(M[i][j]) < abs(M[best[0]][best[1]])):
                best = (i, j)
    return best


def _clear_column(st, M, t, n):
    while True:
        rest = [i for i in range(t + 1, n) if M[i][t]]
        if not rest:
            return
        for i in rest:
            st.addmul(i, t, -(M[i][t] // M[t][t]))
        small = [i for i in range(t + 1, n) if M[i][t]]
        if small:
            st.swap(t, min(small, key=lambda i: abs(M[i][t])))


def _clear_row(cols, M, t, m) -> bool:
    """Returns whether anything moved, so the caller knows to re-clear."""
    moved = False
    while True:
        rest = [j for j in range(t + 1, m) if M[t][j]]
        if not rest:
            return moved
        moved = True
        for j in rest:
            cols.addmul(M, j, t, -(M[t][j] // M[t][t]))
        small = [j for j in range(t + 1, m) if M[t][j]]
        if small:
            cols.swap(M, t, min(small, key=lambda j: abs(M[t][j])))


def _not_divisible(M, t, n, m):
    d = M[t][t]
    if not d:
        return None
    for i in range(t + 1, n):
        for j in range(t + 1, m):
            if M[i][j] % d:
                return (i, j)
    return None


def _chain(st, cols, M, k):
    """Make the diagonal non-negative. Divisibility is already an invariant
    of the loop above; this only fixes signs."""
    for i in range(k):
        if M[i][i] < 0:
            st.negate(i)


def is_smith(S, invariants) -> bool:
    n, m = shape(S)
    for i in range(n):
        for j in range(m):
            if i != j and S[i][j]:
                return False
    diag = [S[i][i] for i in range(min(n, m))]
    if any(d < 0 for d in diag):
        return False
    nz = [d for d in diag if d]
    if nz != diag[:len(nz)] or nz != list(invariants):
        return False
    return all(b % a == 0 for a, b in zip(nz, nz[1:]))


# --- the answers -----------------------------------------------------------


def analyse(A, question="hermite") -> dict:
    """rank, det, hermite or smith -- one shape of evidence for all four."""
    n, m = shape(A)
    if question in ("det", "determinant") and n != m:
        raise NotAnIntegerMatrix(_t("lattice.not_square", n=n, m=m))

    if question == "smith":
        out = smith(A)
        out["question"] = "smith"
        diag = [out["s"][i][i] for i in range(min(n, m))]
        out["det"] = (out["det_u"] * out["det_v"] *
                      _product(diag)) if n == m else None
        return out

    out = hermite(A)
    out["question"] = question if question != "determinant" else "det"
    out["det"] = (out["det_u"] * _product([out["h"][i][i] for i in range(n)])
                  if n == m else None)
    return out


def _product(values) -> int:
    out = 1
    for v in values:
        out *= v
    return out
