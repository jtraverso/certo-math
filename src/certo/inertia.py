"""The inertia of a symmetric rational matrix, as a CONGRUENCE.

    S A S^T = D,    D diagonal,    S S_inv = I

Sylvester's law of inertia says congruent matrices have the same number of
positive, negative and zero eigenvalues, so the signs of D ARE the inertia of
A -- and checking that is two products of rational matrices and a look at a
diagonal, the same shape of evidence `matrix` already uses for Hermite and
Smith: a transform carried with its inverse, so the verifier multiplies and
never eliminates.

WHY NOT LDL^T AS IT STANDS. `sos` has an exact LDL^T, and it stops at the
first zero pivot whose column is not zero -- which is right there, because
such a matrix is not PSD and that is all `sos` needs to know. An inertia has
to go on. `[[0, 1], [1, 0]]` has inertia (1, 1, 0) and no usable pivot at all.
The remedy is congruence too: adding row and column `j` to row and column `k`
makes the new pivot `a_kk + 2 a_kj + a_jj`, which is `2 a_kj` when both
diagonal entries are zero -- non-zero exactly when there was something to
eliminate. Every step is an elementary congruence, applied to S, and its
inverse is applied to S_inv on the other side.

WHAT THE CERTIFICATE ALSO GIVES. PSD is `n_minus == 0`, positive definite is
`n_minus == n_zero == 0`, and rank is `n_plus + n_minus`. When PSD fails, the
row of S at a negative pivot is a vector `x` with `x^T A x < 0` -- one
quadratic form, checked on its own, the most direct refutation there is.

Entries are exact rationals: integers, `Fraction`, or strings like "3/7".
A float is refused rather than converted, because `0.1` is not 1/10 and a
matrix quietly rounded is a different matrix.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t as _t


class NotSymmetric(ValueError):
    """The input is not a symmetric rational matrix this can read."""


def _rational(x, where):
    if isinstance(x, bool):
        raise NotSymmetric(_t("inertia.not_rational", where=where, value=x))
    if isinstance(x, float):
        raise NotSymmetric(_t("inertia.float", where=where, value=x))
    try:
        return Fraction(x)
    except (TypeError, ValueError, ZeroDivisionError):
        raise NotSymmetric(_t("inertia.not_rational", where=where,
                              value=x)) from None


def parse(rows):
    """A square symmetric matrix of Fractions, or NotSymmetric."""
    try:
        M = [[_rational(v, "[{}][{}]".format(i, j)) for j, v in enumerate(r)]
             for i, r in enumerate(rows)]
    except TypeError:
        raise NotSymmetric(_t("inertia.not_square", n=0, m=0)) from None
    n = len(M)
    if n == 0 or any(len(r) != n for r in M):
        raise NotSymmetric(_t("inertia.not_square", n=n,
                              m=len(M[0]) if M else 0))
    for i in range(n):
        for j in range(i + 1, n):
            if M[i][j] != M[j][i]:
                raise NotSymmetric(_t("inertia.not_symmetric", i=i, j=j,
                                      a=str(M[i][j]), b=str(M[j][i])))
    return M


def congruence(A):
    """`(S, S_inv, D)` with `S A S^T = diag(D)`, all exact.

    O(n^3) Fraction operations. The row operations are the elementary
    congruences: swap two indices, or add a multiple of one row to another --
    each applied to both sides of `A`, to `S` on the left, and in inverse to
    `S_inv` on the right.
    """
    n = len(A)
    M = [list(r) for r in A]
    S = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    Sinv = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]

    def swap(a, b):
        M[a], M[b] = M[b], M[a]
        for r in M:
            r[a], r[b] = r[b], r[a]
        S[a], S[b] = S[b], S[a]
        for r in Sinv:                      # E^-1 = E, on the right
            r[a], r[b] = r[b], r[a]

    def add(dst, src, c):
        """row_dst += c row_src, and the same on columns."""
        if c == 0:
            return
        M[dst] = [x + c * y for x, y in zip(M[dst], M[src])]
        for r in M:
            r[dst] += c * r[src]
        S[dst] = [x + c * y for x, y in zip(S[dst], S[src])]
        for r in Sinv:                      # E^-1 = I - c e_dst e_src^T
            r[src] -= c * r[dst]

    for k in range(n):
        if M[k][k] == 0:
            j = next((i for i in range(k + 1, n) if M[i][i] != 0), None)
            if j is not None:
                swap(k, j)
            else:
                j = next((i for i in range(k + 1, n) if M[k][i] != 0), None)
                if j is None:
                    continue                # row and column k are zero
                add(k, j, Fraction(1))      # pivot becomes 2 a_kj != 0
        p = M[k][k]
        for i in range(k + 1, n):
            if M[i][k] != 0:
                add(i, k, -M[i][k] / p)
    D = [M[i][i] for i in range(n)]
    return S, Sinv, D


def _mul(X, Y):
    cols = list(zip(*Y))
    return [[sum((a * b for a, b in zip(row, col)), Fraction(0))
             for col in cols] for row in X]


def check(A, S, Sinv, D) -> dict:
    """Recompute everything the certificate says. Nothing is believed."""
    n = len(A)
    ident = all(v == (1 if i == j else 0)
                for i, r in enumerate(_mul(S, Sinv)) for j, v in enumerate(r))
    SAST = _mul(_mul(S, A), [list(c) for c in zip(*S)])
    diagonal = all(SAST[i][j] == (D[i] if i == j else 0)
                   for i in range(n) for j in range(n))
    return {"invertible": ident, "congruent": diagonal}


def counts(D) -> dict:
    plus = sum(1 for d in D if d > 0)
    minus = sum(1 for d in D if d < 0)
    return {"n_plus": plus, "n_minus": minus, "n_zero": len(D) - plus - minus}


def negative_direction(A, S, D):
    """A row of S at a negative pivot: `x^T A x < 0`, or None if PSD."""
    for k, d in enumerate(D):
        if d < 0:
            x = S[k]
            if quadratic(A, x) < 0:
                return x
    return None


def quadratic(A, x) -> Fraction:
    return sum((x[i] * A[i][j] * x[j] for i in range(len(A))
                for j in range(len(A))), Fraction(0))


def signature(rows) -> dict:
    """`{"n_plus", "n_minus", "n_zero"}`, EXACT and fast -- and not a
    certificate.

    For a loop over tens of thousands of matrices, where what is wanted is
    the three numbers. The matrix is scaled to integers (a positive scale
    changes no sign) and reduced by the same congruences as `congruence`, but
    fraction-free -- Bareiss's division, which is exact because every entry
    stays a minor -- and without carrying S. Nothing here is approximate; what
    it lacks is only the transform a verifier would multiply. When a number
    from this loop matters, ask `certo matrix` for that one and cite the
    certificate.
    """
    A = parse(rows)
    n = len(A)
    den = 1
    for r in A:
        for x in r:
            den = den * x.denominator // _gcd(den, x.denominator)
    M = [[int(x * den) for x in r] for r in A]
    size, zero, prev = n, 0, 1
    signs = []
    k = 0
    while k < size:
        if M[k][k] == 0:
            j = next((i for i in range(k + 1, size) if M[i][i] != 0), None)
            if j is not None:
                _iswap(M, k, j)
            else:
                j = next((i for i in range(k + 1, size) if M[k][i] != 0), None)
                if j is None:
                    # a zero row and column: one zero eigenvalue, set aside
                    size -= 1
                    zero += 1
                    _iswap(M, k, size)
                    continue
                _iadd(M, k, j)
        p = M[k][k]
        for i in range(k + 1, size):
            Mi = M[i]
            for j in range(k + 1, size):
                Mi[j] = (p * Mi[j] - M[i][k] * M[k][j]) // prev
        for i in range(k + 1, size):
            M[i][k] = M[k][i] = 0
        # the true pivot is p / prev, and prev is the previous pivot's minor
        signs.append((p > 0) == (prev > 0))
        prev = p
        k += 1
    plus = sum(signs)
    return {"n_plus": plus, "n_minus": len(signs) - plus, "n_zero": zero}


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def _iswap(M, a, b):
    M[a], M[b] = M[b], M[a]
    for r in M:
        r[a], r[b] = r[b], r[a]


def _iadd(M, dst, src):
    M[dst] = [x + y for x, y in zip(M[dst], M[src])]
    for r in M:
        r[dst] += r[src]


def inertia(rows) -> dict:
    """The whole answer for a matrix given as rows, for use in a loop.

    `{"n_plus", "n_minus", "n_zero", "S", "S_inv", "D", "psd", "pd",
    "rank", "witness"}` -- every field exact, and the triple (S, S_inv, D)
    already re-checked here before it is returned.
    """
    A = parse(rows)
    S, Sinv, D = congruence(A)
    ok = check(A, S, Sinv, D)
    if not all(ok.values()):         # arithmetic that disagrees with itself
        raise ArithmeticError("congruence failed its own check: {}".format(ok))
    c = counts(D)
    return dict(c, S=S, S_inv=Sinv, D=D, psd=c["n_minus"] == 0,
                pd=c["n_minus"] == 0 and c["n_zero"] == 0,
                rank=c["n_plus"] + c["n_minus"],
                witness=negative_direction(A, S, D), matrix=A)
