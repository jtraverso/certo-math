"""Sums of squares: a floating-point search, an exact certificate.

I argued twice in this project's own notes that SOS was not worth having
because an SDP is solved in floating point and an inexact certificate is not
citable. That objection was wrong, or rather it was aimed at the wrong half.
It is the same objection that would rule out `opt`, and `opt` answers it:
solve numerically, RECONSTRUCT rationals, and re-verify exactly. The floating
point is a search heuristic. The certificate is exact or it is not emitted.

So the pipeline is:

  1. Write `p = z^T G z` for the monomial vector z. That is a LINEAR condition
     on G, an affine subspace; `p` is a sum of squares iff some G in it is
     positive semidefinite.
  2. Find a numeric G. With Clarabel installed, an interior-point SDP solve
     that MAXIMISES the smallest eigenvalue of G. Without it, alternating
     projections -- onto the affine subspace, then onto the PSD cone by
     clipping eigenvalues, repeat -- which needs nothing but numpy.

     The difference is not only speed. Alternating projections land on the
     BOUNDARY of the PSD cone, with eigenvalues clipped to exactly zero, and
     rounding a boundary point to rationals breaks semidefiniteness. An
     interior point with its smallest eigenvalue pushed up leaves room to
     round. Measured on thirty random sums of squares, two to four variables
     and degree four to six: projections certified 6, Clarabel 26, mostly
     with denominator 1, and faster on every one. Neither certified Motzkin,
     which is non-negative and not a sum of squares -- the property that
     matters, because the search can only fail to find, never find wrongly.

     What the interior point does NOT fix: a polynomial that is a sum of
     squares only through SINGULAR Gram matrices has no interior to find, and
     its margin comes back zero. That is the case of every inequality with an
     equality case, and it is less bad than it sounds: the seven tight ones
     measured -- AM-GM in two, three and four variables, Lagrange, a sextic --
     all certify, because their Gram matrices are rational with small
     entries and rounding lands exactly on the face.

     What still fails is a sum of FEW squares with GENERIC coefficients.
     Facial reduction was built for it and measured, and it rescued none of
     the five: the minimal face containing every Gram matrix is spanned by
     the polynomial's algebraic common zeros, so it is not rational, and
     where rounding did produce a rational face it was the wrong one, with a
     negative margin. The rational certificate exists, on a lower-rank
     sub-face the interior point never exposes. Recovering it is rank
     reduction toward a rational Gram matrix, and it is open.
  3. Round G to rationals and project back onto the affine subspace EXACTLY,
     in `Fraction`. The rounding usually breaks positive semidefiniteness,
     which is why the next step is not optional.
  4. Exact LDL^T with symmetric pivoting. If every pivot is >= 0, the
     decomposition IS the sum of squares: `p = sum d_i (l_i . z)^2`.
  5. Expand it and compare with `p`, coefficient by coefficient.

Step 5 is the certificate. Steps 1-4 are how it was found, and a reader never
has to care. What travels is a list of rational coefficients and rational
linear forms, and checking it is multiplying polynomials.

Where it stops: an SOS decomposition proves `p >= 0` everywhere. The converse
fails from degree 4 in 3 variables (Motzkin), so "no SOS found" is never
"p takes a negative value" -- it is `unknown_solver`, like everything else
here that searched and came back empty.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations_with_replacement

from .i18n import t
from .polynomials import Poly


class NoBackend(RuntimeError):
    """numpy is not installed, so there is nothing to search with."""


def monomial_basis(nvars: int, half_degree: int) -> list:
    """Every monomial of degree <= d, as exponent tuples. The vector z."""
    out = [tuple([0] * nvars)]
    for deg in range(1, half_degree + 1):
        for combo in combinations_with_replacement(range(nvars), deg):
            e = [0] * nvars
            for i in combo:
                e[i] += 1
            out.append(tuple(e))
    return sorted(set(out), key=lambda e: (sum(e), e))


def _pairs(basis):
    """Which (i, j) contribute to each monomial of z z^T."""
    index = {}
    for i, a in enumerate(basis):
        for j, b in enumerate(basis):
            key = tuple(x + y for x, y in zip(a, b))
            index.setdefault(key, []).append((i, j))
    return index


# ---------------------------------------------------------------------------
# the numeric search
# ---------------------------------------------------------------------------


def search(p: Poly, basis, iterations=600, tol=1e-9):
    """Alternating projections onto {G : z^T G z = p} and the PSD cone.

    Not an SDP solver and not pretending to be one: no optimality, no duality,
    no certificate of infeasibility. It only has to land close enough that
    rounding survives, and for the sizes a write-up contains it does.
    """
    try:
        import numpy as np
    except ImportError:
        raise NoBackend(t("sos.no_numpy"))

    index = _pairs(basis)
    n = len(basis)
    target = {e: float(c) for e, c in p.terms.items()}

    def to_affine(G):
        """Spread each monomial's required coefficient over its cells."""
        H = G.copy()
        for mono, cells in index.items():
            want = target.get(mono, 0.0)
            got = sum(H[i, j] for i, j in cells)
            delta = (want - got) / len(cells)
            for i, j in cells:
                H[i, j] += delta
        return (H + H.T) / 2

    def to_psd(G):
        w, V = np.linalg.eigh((G + G.T) / 2)
        return (V * np.clip(w, 0.0, None)) @ V.T

    G = to_affine(np.zeros((n, n)))
    for _ in range(iterations):
        H = to_psd(G)
        G2 = to_affine(H)
        if np.max(np.abs(G2 - G)) < tol:
            G = G2
            break
        G = G2
    return to_psd(G)


def search_sdp(p: Poly, basis, time_limit_s=None):
    """Clarabel: maximise t subject to z^T G z = p, G - tI PSD, t <= 1.

    Returns the numeric G, or None when Clarabel is not installed. Nothing it
    returns is trusted: the exact rounding, projection and LDL^T below decide
    whether there is a certificate, exactly as they do for the other search.
    A mistake in THIS function can therefore cost certificates and cannot
    manufacture one, which is what made it safe to swap in.

    The cap `t <= 1` keeps the problem bounded and is not a claim: a margin of
    one is already far more than rounding needs.
    """
    try:
        import math

        import clarabel
        import numpy as np
        import scipy.sparse as sparse
    except ImportError:
        return None

    n = len(basis)
    # Upper triangle in COLUMN-MAJOR order -- (0,0),(0,1),(1,1),(0,2),... --
    # which is how Clarabel's PSDTriangleConeT reads its slice, with the
    # off-diagonal entries scaled by sqrt(2).
    tri = [(i, j) for j in range(n) for i in range(j + 1)]
    k_of = {ij: k for k, ij in enumerate(tri)}
    m = len(tri)
    t_col = m

    index = _pairs(basis)
    rows, cols, vals, rhs = [], [], [], []
    r = 0
    for mono in sorted(index):
        seen = {}
        for i, j in index[mono]:
            key = (i, j) if i <= j else (j, i)
            seen[key] = seen.get(key, 0) + 1        # an off-diagonal cell twice
        for key, count in seen.items():
            rows.append(r)
            cols.append(k_of[key])
            vals.append(float(count))
        rhs.append(float(p.terms.get(mono, 0)))
        r += 1
    n_eq = r

    # s = svec(G - tI) must be PSD; Clarabel writes that as A x + s = b.
    for k, (i, j) in enumerate(tri):
        rows.append(r + k)
        cols.append(k)
        vals.append(-(1.0 if i == j else math.sqrt(2.0)))
        if i == j:
            rows.append(r + k)
            cols.append(t_col)
            vals.append(1.0)
    r += m
    rows.append(r)
    cols.append(t_col)
    vals.append(1.0)                                 # 1 - t >= 0
    r += 1

    A = sparse.csc_matrix((vals, (rows, cols)), shape=(r, m + 1))
    b = np.array(rhs + [0.0] * m + [1.0])
    q = np.zeros(m + 1)
    q[t_col] = -1.0
    P = sparse.csc_matrix((m + 1, m + 1))
    cones = [clarabel.ZeroConeT(n_eq), clarabel.PSDTriangleConeT(n),
             clarabel.NonnegativeConeT(1)]
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    if time_limit_s is not None:
        # Clarabel's own clock. A solve that runs out returns no G, which is
        # "not found" -- never a certificate, since nothing below trusts G.
        settings.time_limit = float(time_limit_s)
    try:
        sol = clarabel.DefaultSolver(P, q, A, b, cones, settings).solve()
    except Exception:  # noqa: BLE001
        return None
    x = np.array(sol.x)
    if x.size != m + 1 or not np.all(np.isfinite(x)):
        return None
    G = np.zeros((n, n))
    for k, (i, j) in enumerate(tri):
        G[i, j] = G[j, i] = x[k]
    return G


def backends() -> list:
    """The searches available here, best first."""
    out = []
    try:
        import clarabel  # noqa: F401
        out.append("clarabel")
    except ImportError:
        pass
    try:
        import numpy  # noqa: F401
        out.append("projections")
    except ImportError:
        pass
    return out


# ---------------------------------------------------------------------------
# exact rounding and decomposition
# ---------------------------------------------------------------------------


def _round(G, denom: int):
    n = len(G)
    return [[Fraction(round(float(G[i][j]) * denom), denom) for j in range(n)]
            for i in range(n)]


def project_exact(M, basis, p: Poly):
    """Push a rounded matrix back onto `z^T G z = p`, in exact arithmetic.

    Rounding almost never lands on the affine subspace, and a Gram matrix that
    is off by 1e-9 does not represent `p` -- it represents something else. The
    correction is spread evenly over the cells of each monomial, which keeps
    the matrix symmetric and is the same move the numeric step makes.
    """
    index = _pairs(basis)
    out = [row[:] for row in M]
    for mono, cells in index.items():
        want = p.terms.get(mono, Fraction(0))
        got = sum(out[i][j] for i, j in cells)
        delta = Fraction(want - got, len(cells))
        for i, j in cells:
            out[i][j] += delta
    n = len(out)
    return [[(out[i][j] + out[j][i]) / 2 for j in range(n)] for i in range(n)]


def ldl(M):
    """Exact LDL^T with the rows in order. Returns (D, L) or None if not PSD.

    Bailing out on the first negative pivot rather than continuing is the
    point: the question is whether this matrix is a sum of squares, and one
    negative pivot answers it.
    """
    n = len(M)
    A = [row[:] for row in M]
    L = [[Fraction(1) if i == j else Fraction(0) for j in range(n)]
         for i in range(n)]
    D = [Fraction(0)] * n
    for k in range(n):
        D[k] = A[k][k]
        if D[k] < 0:
            return None
        if D[k] == 0:
            # A zero pivot is fine only if its whole column is zero; otherwise
            # the matrix is indefinite and no amount of pivoting saves it.
            if any(A[i][k] != 0 for i in range(k + 1, n)):
                return None
            continue
        for i in range(k + 1, n):
            L[i][k] = A[i][k] / D[k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] -= L[i][k] * D[k] * L[j][k]
    return D, L


def decomposition(D, L, basis, variables):
    """(coefficient, linear form) per square, dropping the zero pivots."""
    n = len(D)
    out = []
    for k in range(n):
        if D[k] == 0:
            continue
        form = Poly(variables)
        for i in range(k, n):
            if L[i][k]:
                form = form + Poly(variables, {basis[i]: L[i][k]})
        if form:
            out.append((D[k], form))
    return out


def expand(terms, variables) -> Poly:
    """sum d_i * q_i^2. The whole verification, in one line."""
    out = Poly(variables)
    for d, q in terms:
        out = out + (q * q).scaled(d)
    return out


DENOMS = (1, 2, 6, 12, 60, 360, 2520, 10**4, 10**6, 10**8)


def certify(p: Poly, half_degree=None, iterations=600, time_limit_s=None):
    """Find an exact SOS decomposition of `p`, or None.

    The denominator ladder is the same idea as `opt`'s rational
    reconstruction: try the simple denominators first, because a certificate
    with 1/2 in it is one a person can read and a certificate with
    1/99991 in it is one they will not check.
    """
    if p.degree % 2:
        return None, t("sos.odd_degree", d=p.degree)
    d = half_degree if half_degree is not None else max(p.degree // 2, 1)
    basis = monomial_basis(len(p.vars), d)

    available = backends()
    if not available:
        raise NoBackend(t("sos.no_numpy"))

    # BEST FIRST, AND THE OTHER ONE TOO. Clarabel found every certificate the
    # projections did on the measured sample and twenty more, but "every one
    # it found" is a sample, not a theorem. Trying both means installing
    # Clarabel can only ADD certificates -- it cannot lose one the old search
    # would have produced -- and the second attempt costs nothing when the
    # first succeeds.
    for name in available:
        G = (search_sdp(p, basis, time_limit_s) if name == "clarabel"
             else search(p, basis, iterations=iterations))
        if G is None:
            continue
        for denom in DENOMS:
            M = project_exact(_round(G, denom), basis, p)
            res = ldl(M)
            if res is None:
                continue
            terms = decomposition(res[0], res[1], basis, p.vars)
            if expand(terms, p.vars) == p:
                return (terms, basis, denom, name), ""
    return None, t("sos.no_rounding", n=len(DENOMS))


def serialize(terms) -> list:
    return [{"coef": str(d), "form": q.serialize()} for d, q in terms]


def parse(variables, data) -> list:
    return [(Fraction(x["coef"]), Poly.parse(variables, x["form"]))
            for x in data]
