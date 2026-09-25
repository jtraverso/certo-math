"""Aritmetica racional exacta.

Los solvers LP trabajan en punto flotante y no hay forma de evitarlo: CBC
devuelve 10.66666656003499 donde la respuesta es 32/3, con un error de 2.5e-7
que es su tolerancia por defecto. Con eso no se puede afirmar igualdad
primal-dual, ni citar una constante en un paper, ni exportar a Lean.

La salida no es un solver exacto, es esta:

    1. resolver en flotante (rapido, aproximado);
    2. RECONSTRUIR racionales a partir de la solucion flotante;
    3. VERIFICAR exactamente en Fraction, y aceptar solo si verifica.

El paso 3 es lo que hace que el paso 2 pueda ser una heuristica sin que eso
comprometa nada: una reconstruccion mala no verifica y se rechaza. El
certificado resultante no depende de confiar en CBC.
"""
from __future__ import annotations

from fractions import Fraction

# Denominadores que se prueban, de menor a mayor. Los primeros cubren lo que
# aparece de verdad en combinatoria (tercios, doceavos, 71/600...); los
# ultimos son la red de seguridad.
DENOM_LADDER = (1, 2, 3, 4, 6, 8, 12, 24, 60, 120, 360, 720,
                10**3, 10**4, 10**5, 10**6)


def to_fraction(v) -> Fraction:
    """Cualquier numero -> Fraction exacta. Los float se toman tal cual."""
    if isinstance(v, Fraction):
        return v
    if isinstance(v, int):
        return Fraction(v)
    if isinstance(v, str):
        return Fraction(v)
    return Fraction(v).limit_denominator(10**12)


def reconstruct(values, denom: int):
    """Redondea cada valor al racional mas cercano con denominador <= denom."""
    return [Fraction(v).limit_denominator(denom) for v in values]


def dot(u, v) -> Fraction:
    return sum((Fraction(a) * Fraction(b) for a, b in zip(u, v)), Fraction(0))


def serialize(x) -> str:
    """Fraction -> '32/3'. Exacto y legible; se relee con Fraction(s)."""
    f = to_fraction(x)
    return str(f.numerator) if f.denominator == 1 else "{}/{}".format(
        f.numerator, f.denominator)


def serialize_all(xs):
    return [serialize(x) for x in xs]


def parse_all(xs):
    return [Fraction(s) for s in xs]


# ---------------------------------------------------------------------------
# certificacion exacta de un LP:  max c.x  s.a.  A x <= b,  x >= 0
# ---------------------------------------------------------------------------


class Prepared:
    """`A`, `b`, `c` converted to Fractions ONCE, with `A` kept by its
    non-zeros in both directions.

    `check_lp` used to convert the whole matrix and multiply it densely on
    every call. On a 1048-column packing that was 21 seconds a call and 1097
    seconds of a run, for a matrix that is almost all zeros -- and `certify`
    calls it once per candidate. The arithmetic is the same arithmetic; what
    goes is multiplying by zero two million times.
    """

    __slots__ = ("rows", "cols", "b", "c")

    @classmethod
    def from_sparse(cls, rows, b, c):
        """From `{column: coefficient}` rows, never densified."""
        self = cls.__new__(cls)
        self.b = [to_fraction(v) for v in b]
        self.c = [to_fraction(v) for v in c]
        self.rows = [sorted((j, to_fraction(v)) for j, v in r.items() if v)
                     for r in rows]
        self.cols = [[] for _ in self.c]
        for i, r in enumerate(self.rows):
            for j, f in r:
                self.cols[j].append((i, f))
        return self

    def dense(self):
        """The dense matrix, for the one pass -- the exact simplex -- that
        needs it. Built only when that pass runs."""
        width = len(self.c)
        out = []
        for r in self.rows:
            row = [Fraction(0)] * width
            for j, f in r:
                row[j] = f
            out.append(row)
        return out

    def __init__(self, A, b, c):
        self.b = [to_fraction(v) for v in b]
        self.c = [to_fraction(v) for v in c]
        self.rows = []
        for row in A:
            r = []
            for j, v in enumerate(row):
                if not v:
                    continue          # a zero, of whatever type, costs nothing
                f = to_fraction(v)
                if f:
                    r.append((j, f))
            self.rows.append(r)
        self.cols = [[] for _ in self.c]
        for i, r in enumerate(self.rows):
            for j, f in r:
                self.cols[j].append((i, f))

    def row_dot(self, i, x) -> Fraction:
        return sum((f * x[j] for j, f in self.rows[i]), Fraction(0))

    def col_dot(self, j, y) -> Fraction:
        return sum((f * y[i] for i, f in self.cols[j]), Fraction(0))


def _sparse_dot(u, v) -> Fraction:
    return sum((a * b for a, b in zip(u, v) if a and b), Fraction(0))


def check_lp(A, b, c, x, y, tol_free: bool = True) -> dict:
    """Comprueba optimalidad en Fraction. Sin tolerancias, sin epsilon.

    Devuelve los cuatro veredictos por separado para poder decir QUE falla.
    Si los cuatro son ciertos, x e y son optimos y el objetivo es exacto:
    dualidad debil da c.x <= b.y siempre, y la igualdad cierra el sandwich.

    `A` may be a `Prepared` already, which is how `certify` calls it.
    """
    P = A if isinstance(A, Prepared) else Prepared(A, b, c)
    x = [to_fraction(v) for v in x]
    y = [to_fraction(v) for v in y]

    primal_nonneg = all(v >= 0 for v in x)
    primal_feasible = all(P.row_dot(i, x) <= P.b[i]
                          for i in range(len(P.rows)))
    dual_nonneg = all(v >= 0 for v in y)
    dual_feasible = all(P.col_dot(j, y) >= P.c[j] for j in range(len(P.c)))
    cx, by = _sparse_dot(P.c, x), _sparse_dot(P.b, y)
    strong = cx == by

    return {
        "primal_nonneg": primal_nonneg,
        "primal_feasible": primal_feasible,
        "dual_nonneg": dual_nonneg,
        "dual_feasible": dual_feasible,
        "strong_duality": strong,
        "objective": cx,
        "dual_bound": by,
        "ok": all((primal_nonneg, primal_feasible, dual_nonneg,
                   dual_feasible, strong)),
    }


def primal_from_dual(A, b, c, y):
    """The primal complementary slackness allows, given an exact optimal dual.

    The mirror of `dual_candidates`. For `max c.x` subject to `Ax <= b, x >= 0`
    at an optimal pair:

      * a row carrying weight (`y_i > 0`) is tight: `A_i . x = b_i`;
      * a variable whose reduced cost is positive (`sum_i A_ij y_i > c_j`)
        is off its bound: `x_j = 0`.

    This exists because the exact dual is reachable on instances where no
    ROUNDING of the float primal is feasible -- a vertex with a denominator
    past the ladder, which is what a real instance produces and a small
    example never does. Without it, `certify` had an exact dual in hand and
    nothing to pair it with, and fell back to floating point.

    Nothing here is trusted for where it came from: `check_lp` decides.
    """
    A = [[to_fraction(v) for v in row] for row in A]
    b = [to_fraction(v) for v in b]
    c = [to_fraction(v) for v in c]
    y = [to_fraction(v) for v in y]
    m, n = len(A), len(c)

    tight = [i for i in range(m) if y[i] > 0]
    free = [j for j in range(n)
            if sum((A[i][j] * y[i] for i in range(m)), Fraction(0)) == c[j]]
    if not free:
        # Every variable priced strictly above its cost: the origin is it.
        return [Fraction(0)] * n
    if not tight:
        return [Fraction(0)] * n

    sol = solve_exact([[A[i][j] for j in free] for i in tight],
                      [b[i] for i in tight])
    if sol is None:
        return None
    x = [Fraction(0)] * n
    for pos, j in enumerate(free):
        x[j] = sol[pos]
    return x


def solve_exact(rows, rhs):
    """Solve `M z = rhs` in Fraction, or None if it is singular.

    Gaussian elimination with partial pivoting on a non-zero entry -- with
    rationals there is no numerical reason to prefer a large pivot, only the
    need for a non-zero one. Returns one solution; an underdetermined system
    gets zeros in the free positions, which is what complementary slackness
    wants for a variable nothing pins down.
    """
    n = len(rows)
    if not n:
        return []
    m = len(rows[0])
    aug = [[Fraction(v) for v in row] + [Fraction(r)] for row, r in zip(rows, rhs)]

    where = [-1] * m          # which row ended up pivoting on each column
    r = 0
    for col in range(m):
        piv = next((i for i in range(r, n) if aug[i][col] != 0), None)
        if piv is None:
            continue
        aug[r], aug[piv] = aug[piv], aug[r]
        inv = Fraction(1) / aug[r][col]
        aug[r] = [v * inv for v in aug[r]]
        for i in range(n):
            if i != r and aug[i][col] != 0:
                f = aug[i][col]
                aug[i] = [a - f * b for a, b in zip(aug[i], aug[r])]
        where[col] = r
        r += 1
        if r == n:
            break

    # A row that reduced to `0 = c` with c non-zero means no solution at all.
    for i in range(n):
        if all(v == 0 for v in aug[i][:m]) and aug[i][m] != 0:
            return None
    return [aug[where[j]][m] if where[j] >= 0 else Fraction(0)
            for j in range(m)]


#: How many candidate bases to try before giving up. Degeneracy in practice
#: means a handful of tight rows; this is the guard against the case where it
#: does not, and hitting it is reported as "not certified", never as "wrong".
MAX_BASES = 400


def dual_candidates(A, b, c, x, cap=MAX_BASES):
    """Exact duals that complementary slackness allows, given an exact primal.

    For `max c.x` subject to `Ax <= b, x >= 0` at an optimal `x`:

      * a row with slack (`A_i . x < b_i`) has `y_i = 0`;
      * a variable off its bound (`x_j > 0`) has `sum_i A_ij y_i = c_j`.

    Those two do not always pin `y` down. On a DEGENERATE vertex -- more tight
    rows than active variables, which is exactly what symmetry produces -- the
    system is underdetermined, and the freedom left over IS the set of optimal
    duals CBC picks from arbitrarily. So this yields candidates: the full
    system first, then each choice of which tight rows carry the weight.

    None of them is trusted. `check_lp` decides, exactly, the same as it does
    for a rounded one. What changes is where candidates come from -- the
    structure of the problem instead of whatever a float solver landed on.
    """
    import itertools

    P = A if isinstance(A, Prepared) else Prepared(A, b, c)
    c = P.c
    x = [to_fraction(v) for v in x]
    m = len(P.rows)
    entry = [dict(r) for r in P.rows]

    tight = [i for i in range(m) if P.row_dot(i, x) == P.b[i]]
    active = [j for j in range(len(c)) if x[j] > 0]
    if not tight:
        # Nothing binds. The dual is zero, which is right when the optimum is
        # interior and rejected by check_lp when it is not.
        yield [Fraction(0)] * m
        return

    def solve_over(rows_used):
        eqs = [[entry[i].get(j, Fraction(0)) for i in rows_used]
               for j in active]
        rhs = [c[j] for j in active]
        sol = (solve_exact(eqs, rhs) if eqs
               else [Fraction(0)] * len(rows_used))
        if sol is None:
            return None
        y = [Fraction(0)] * m
        for pos, i in enumerate(rows_used):
            y[i] = sol[pos]
        return y

    seen = set()

    def offer(y):
        if y is None:
            return None
        key = tuple(y)
        if key in seen:
            return None
        seen.add(key)
        return y

    first = offer(solve_over(tight))
    if first is not None:
        yield first

    # The degenerate case: choose which tight rows carry non-zero weight. A
    # basis has as many rows as there are active variables.
    k = len(active)
    if 0 < k < len(tight):
        for n, rows_used in enumerate(itertools.combinations(tight, k)):
            if n >= cap:
                break
            y = offer(solve_over(list(rows_used)))
            if y is not None:
                yield y


def dual_from_primal(A, b, c, x):
    """The first dual complementary slackness allows, or None.

    Thin wrapper over `dual_candidates` for callers that want one answer.
    It is a CANDIDATE: feasibility is not checked here.
    """
    return next(iter(dual_candidates(A, b, c, x)), None)


def support_candidates(P, x_float, y_float, y_alts=(), tol=1e-7):
    """An exact pair from the SUPPORT of the float one, not from its digits.

    Rounding asks the float solver for the vertex's numbers; this asks it only
    which columns are positive and which rows bind -- a question it answers
    reliably long after its digits stop meaning anything. With the support
    fixed, the vertex is the solution of a square system, and so is the dual:

        A[tight, active] x[active] = b[tight]       (every other x_j = 0)
        A[:, active]^T y = c[active]  over the rows the dual weights

    Two eliminations, where the exact simplex behind it pivots hundreds of
    times over the whole tableau. It exists because a Bernstein dual's LP has
    vertices with denominators near 10^29: no rung of the ladder reaches them,
    no rounded primal is feasible, and the exact simplex was taking 97 of 101
    seconds of a small parametric run. Yields candidates; `check_lp` decides.
    """
    m, n = len(P.rows), len(P.c)
    entry = [dict(r) for r in P.rows]
    # Relative to the largest entry, never to 1: a vertex whose entries are
    # all near 10^-9 has a support, and a floor of 1 read it as the origin.
    scale = max([abs(float(v)) for v in x_float] + [0.0]) or 1.0
    active = [j for j in range(n) if float(x_float[j]) > tol * scale]
    slack = [float(P.b[i]) - sum(float(v) * float(x_float[j])
                                 for j, v in entry[i].items())
             for i in range(m)]
    tight = [i for i in range(m) if abs(slack[i]) <= tol * (1 + abs(float(P.b[i])))]
    xs = []
    if not active:
        xs.append([Fraction(0)] * n)
    elif tight:
        sol = solve_exact([[entry[i].get(j, Fraction(0)) for j in active]
                           for i in tight], [P.b[i] for i in tight])
        if sol is not None:
            x = [Fraction(0)] * n
            for pos, j in enumerate(active):
                x[j] = sol[pos]
            xs.append(x)
    for y_try in (y_float, *y_alts):
        ysc = max([abs(float(v)) for v in y_try] + [0.0]) or 1.0
        weighted = [i for i in range(m) if float(y_try[i]) > tol * ysc]
        for rows_used in (weighted, tight):
            if not rows_used:
                continue
            eqs = [[entry[i].get(j, Fraction(0)) for i in rows_used]
                   for j in active]
            sol = solve_exact(eqs, [P.c[j] for j in active]) if eqs                 else [Fraction(0)] * len(rows_used)
            if sol is None:
                continue
            y = [Fraction(0)] * m
            for pos, i in enumerate(rows_used):
                y[i] = sol[pos]
            for x in xs:
                yield x, y
            # the dual alone fixes a primal too, by complementary slackness
            if not xs:
                yield None, y


def certify(A, b, c, x_float, y_float, ladder=DENOM_LADDER, y_alts=()):
    """Reconstruct and verify. Returns (x, y, report, denom) or (None, ...).

    Three passes, cheapest first, and every one of them ends at the same
    `check_lp`: a candidate is never trusted for where it came from.

      1. BOTH AT ONE RUNG. The common case, and the one that gives the
         simplest denominators -- which is what anyone citing the constant in
         a paper wants.

      2. DERIVE THE DUAL. On a degenerate vertex -- which is what symmetry
         produces -- CBC returns an arbitrary one of many optimal duals, and
         rounding that particular one need not be dual-feasible at all.
         Complementary slackness determines the dual from the primal instead,
         and where it underdetermines it, the choices ARE the optimal duals.

    Pass 1 runs first so nothing that already worked changes, digests
    included.

    `y_alts` are further float duals to try at the SAME rung -- CBC does not
    fix the sign, so the caller hands in the negated and absolute versions.
    They belong here rather than in three separate calls: passes 2 and 3 do
    not read `y_float` at all, so calling three times repeated the expensive
    work and, now that the exact simplex is reachable, would have run it
    three times over.

    Not here, deliberately: reconstructing `x` and `y` at INDEPENDENT rungs.
    It looks like an obvious win and it is not one. `limit_denominator` is
    monotone in accuracy, so a rung high enough for the harder of the two is
    high enough for both, and pass 1 already climbs to it. Measured before
    writing it off, on primals needing 1/3, 1/7 and 2/7 against duals needing
    1/2 and 3/11: every pair was exact at one shared rung.
    """
    last = None
    P = A if isinstance(A, Prepared) else Prepared(A, b, c)
    if isinstance(A, Prepared):
        b, c = P.b, P.c
    dense = [None]

    def A_dense():
        if dense[0] is None:
            dense[0] = P.dense() if isinstance(A, Prepared) else A
        return dense[0]

    for denom in ladder:
        x = reconstruct(x_float, denom)
        for y_try in (y_float, *y_alts):
            y = reconstruct(y_try, denom)
            rep = check_lp(P, b, c, x, y)
            last = rep
            if rep["ok"]:
                return x, y, rep, denom

    # The primals worth pairing a dual against: feasibility is cheap and it
    # keeps the search below from running on a problem that is simply
    # infeasible.
    primals = []
    for dx in ladder:
        x = reconstruct(x_float, dx)
        if all(v >= 0 for v in x) and all(
                P.row_dot(i, x) <= P.b[i] for i in range(len(P.rows))):
            primals.append((dx, x))

    # 2. Stop asking CBC what the dual is, and work it out. On a degenerate
    # vertex there are several optimal duals and CBC returns an arbitrary one;
    # here they are enumerated, and the exact check picks.
    for dx, x in primals:
        for y in dual_candidates(P, b, c, x):
            rep = check_lp(P, b, c, x, y)
            if rep["ok"]:
                return x, y, rep, dx
            last = rep

    # 2b. Read which columns and rows are in play off the float solution, and
    # solve for the vertex and its dual exactly on that support.
    for x, y in support_candidates(P, x_float, y_float, y_alts):
        if x is None:
            x = primal_from_dual(A_dense(), b, c, y)
            if x is None:
                continue
        rep = check_lp(P, b, c, x, y)
        if rep["ok"]:
            denom = max((v.denominator for v in list(x) + list(y)), default=1)
            return x, y, rep, denom
        last = rep

    # 3. Solve the dual outright. Enumerating bases is right for a handful of
    # tight rows and hopeless past it -- a realistic exact cover reaches
    # C(49, 7), about 10^8 -- so past that the answer is an exact simplex
    # rather than a longer search. Still not trusted: `check_lp` decides.
    #
    # This pass used to sit INSIDE `for dx, x in primals`, which meant it
    # never ran when no rounded primal was feasible -- and that is exactly the
    # case it was written for. On a real instance whose optimal vertex has a
    # denominator past the ladder, `primals` is empty, the exact simplex was
    # skipped, and the whole function fell through to floating point with
    # whatever the float solver had said the dual was. The comment below --
    # "the dual does not depend on which primal" -- was already true and was
    # the argument for lifting the call out.
    from .simplex import SimplexLimit, minimise

    try:
        y = minimise(A_dense(), b, c)
    except (SimplexLimit, ZeroDivisionError):
        return None, None, last, None

    for dx, x in primals:
        rep = check_lp(P, b, c, x, y)
        if rep["ok"]:
            return x, y, rep, dx
        last = rep

    # No rounded primal fits this dual. Complementary slackness says which one
    # must, and it is exact -- so the answer no longer depends on a float
    # solution rounding onto a vertex.
    x = primal_from_dual(A_dense(), b, c, y)
    if x is not None:
        rep = check_lp(P, b, c, x, y)
        if rep["ok"]:
            denom = max((v.denominator for v in list(x) + list(y)), default=1)
            return x, y, rep, denom
        last = rep

    return None, None, last, None


def fmt(x, max_denom: int = 10**6) -> str:
    """Muestra un racional como fraccion si es legible, si no como decimal.

    Una razon exacta como 25/27 se lee mucho mejor asi que 0.9259...; pero un
    valor que venia de un float tiene denominador astronomico y ahi la
    fraccion no dice nada.
    """
    f = to_fraction(x)
    if f.denominator <= max_denom:
        return serialize(f)
    return "{:.6g}".format(float(f))


def stats(values):
    """min, max, media y suma, en Fraction. Devuelve None si no hay valores."""
    if not values:
        return None
    fs = [to_fraction(v) for v in values]
    total = sum(fs, Fraction(0))
    return {"count": len(fs), "min": min(fs), "max": max(fs),
            "mean": total / len(fs), "sum": total}
