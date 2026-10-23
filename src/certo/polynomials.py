"""Exact multivariate polynomials, and Buchberger with the cofactors kept.

The point of this module is one certificate: given `f` and generators
`g_1..g_k`, the polynomials `h_i` with

    f = h_1 g_1 + ... + h_k g_k

Finding those is a Groebner basis computation. CHECKING them is expanding a
product and comparing coefficients -- no solver, no algebra system, nothing to
trust. That is the same shape as a Farkas certificate, one level up from
linear arithmetic, and it is why this exists rather than a call to sympy:
sympy will happily tell you `f` is in the ideal, and then the only evidence is
that sympy said so.

The special case is the useful one. `1 = sum h_i g_i` means the system
`g_1 = ... = g_k = 0` has no common solution at all, and the `h_i` are the
whole proof of it. That is a refutation of a polynomial system with a witness
a referee can multiply out by hand.

Written over `Fraction`, so nothing here is approximate at any point. The cost
is speed, which is the right trade for objects small enough to appear in a
write-up; a budget stops the run and says so rather than grinding.
"""
from __future__ import annotations

import time
from fractions import Fraction
from itertools import combinations

from .i18n import t

#: A product with at least this many term pairs is multiplied by FLINT's
#: `fmpq_mpoly` when python-flint is installed. Below it, converting costs
#: more than it saves. Exact either way: the same rationals in, the same
#: rationals out -- a faster implementation of the same arithmetic, with the
#: Python loop kept as the fallback and `CERTO_NO_FLINT=1` to force it.
FLINT_FROM = 20_000

_FLINT = []          # [module or None], resolved once


def _flint():
    if not _FLINT:
        import os

        mod = None
        if not os.environ.get("CERTO_NO_FLINT"):
            try:
                import flint

                if hasattr(flint, "fmpq_mpoly_ctx"):
                    mod = flint
            except Exception:  # noqa: BLE001 -- absent or broken: the fallback
                mod = None
        _FLINT.append(mod)
    return _FLINT[0]


def flint_in_use() -> bool:
    """Whether large products go through FLINT in this process."""
    return _flint() is not None


def _flint_mul(a, b):
    """`a * b` through `fmpq_mpoly`, or None when FLINT is not there. The
    variables are renamed `v0, v1, ...` for the context: FLINT never sees a
    user's name, and the exponent tuples carry the meaning."""
    fl = _flint()
    if fl is None:
        return None
    ctx = fl.fmpq_mpoly_ctx.get(tuple("v{}".format(i) for i in range(len(a.vars))),
                                "lex")

    def to(p):
        return ctx.from_dict({e: fl.fmpq(int(c.numerator), int(c.denominator))
                              for e, c in p.terms.items()})

    prod = to(a) * to(b)
    return {tuple(int(x) for x in e): Fraction(int(c.p), int(c.q))
            for e, c in prod.to_dict().items()}


class Budget(RuntimeError):
    """Buchberger ran past its budget. Says so; does not guess."""


class TimeBudget(Budget):
    """The CLOCK ran out -- a different budget from the pairs or the terms,
    and said apart, so a caller knows whether more time or a smaller ideal
    is what would help."""


def _check_clock(deadline, every=[0]):
    """Raise TimeBudget once `time.monotonic()` passes `deadline`. Cheap
    enough to call inside the reduction loops: the clock is read one call in
    sixty-four."""
    if deadline is None:
        return
    every[0] += 1
    if every[0] % 64 == 0 and time.monotonic() > deadline:
        raise TimeBudget(t("poly.budget.time"))


class Poly:
    """A polynomial over Q, as {exponent tuple: coefficient}.

    The variable names live on the ring, not on the polynomial, so two
    polynomials can only be combined when they agree about what x means.
    """

    __slots__ = ("vars", "terms")

    def __init__(self, variables, terms=None):
        self.vars = tuple(variables)
        self.terms = {}
        for e, c in (terms or {}).items():
            c = Fraction(c)
            if c:
                self.terms[tuple(e)] = c

    @classmethod
    def _exact(cls, variables, terms):
        """From a dict already holding tuple keys and non-zero `Fraction`s --
        what the arithmetic below produces -- without normalising it again.
        Internal: re-running `Fraction()` over every coefficient of every
        intermediate sum was most of the time a large verification took."""
        out = cls.__new__(cls)
        out.vars = variables
        out.terms = terms
        return out

    # --- construction -----------------------------------------------------

    @classmethod
    def const(cls, variables, c):
        return cls(variables, {(0,) * len(variables): Fraction(c)})

    @classmethod
    def var(cls, variables, name):
        i = list(variables).index(name)
        e = [0] * len(variables)
        e[i] = 1
        return cls(variables, {tuple(e): Fraction(1)})

    @classmethod
    def from_z3(cls, expr, variables):
        """A z3 arithmetic term, through the same parser `farkas` uses. A
        sympy expression is read too, by `from_sympy`: the ring is known."""
        from .linarith import polynomial

        if type(expr).__module__.split(".")[0] == "sympy":
            return cls.from_sympy(expr, variables)
        poly = polynomial(expr)
        out = {}
        for mono, coef in poly.items():
            e = [0] * len(variables)
            for v in mono:
                e[list(variables).index(v)] += 1
            key = tuple(e)
            out[key] = out.get(key, Fraction(0)) + coef
        return cls(variables, out)

    @classmethod
    def from_sympy(cls, expr, variables):
        """A sympy expression or `sympy.Poly` over `variables`, by name. Only
        EXACT coefficients: a sympy Float is refused rather than read as the
        rational nearest it, and a symbol outside the ring is named."""
        import sympy

        names = [str(v) for v in variables]
        gens = sympy.symbols(names)
        if isinstance(expr, sympy.Poly):
            expr = expr.as_expr()
        expr = sympy.sympify(expr)
        extra = sorted(str(v) for v in expr.free_symbols if str(v) not in names)
        if extra:
            raise ValueError(t("poly.sympy_symbols", names=", ".join(extra),
                                ring=", ".join(names)))
        P = sympy.Poly(expr.subs({sympy.Symbol(n): g for n, g in zip(names, gens)}),
                       *gens)
        out = {}
        for mono, c in P.terms():
            if not c.is_Rational:
                raise ValueError(t("poly.sympy_inexact", coef=str(c)))
            out[tuple(mono)] = Fraction(int(c.p), int(c.q))
        return cls(tuple(variables), out)

    # --- arithmetic -------------------------------------------------------

    def __bool__(self):
        return bool(self.terms)

    def __eq__(self, other):
        return isinstance(other, Poly) and self.vars == other.vars \
            and self.terms == other.terms

    def __hash__(self):
        return hash((self.vars, tuple(sorted(self.terms.items()))))

    def _coerce(self, other):
        """`other` as a polynomial of THIS ring: a Poly over the same
        variables, or an exact number. A Poly over other variables is refused:
        its exponent tuples mean something else, and adding them position by
        position silently combined x with y."""
        if isinstance(other, Poly):
            if other.vars is not self.vars and other.vars != self.vars:
                raise ValueError(t("poly.ring_mismatch",
                                   got=", ".join(other.vars),
                                   want=", ".join(self.vars)))
            return other
        if isinstance(other, (int, Fraction)) and not isinstance(other, bool):
            return Poly.const(self.vars, other)
        return NotImplemented

    def __add__(self, other):
        other = self._coerce(other)
        if other is NotImplemented:
            return other
        out = dict(self.terms)
        for e, c in other.terms.items():
            out[e] = out.get(e, Fraction(0)) + c
            if not out[e]:
                del out[e]
        return Poly._exact(self.vars, out)

    __radd__ = __add__

    def __neg__(self):
        return self.scaled(-1)

    def __sub__(self, other):
        other = self._coerce(other)
        if other is NotImplemented:
            return other
        return self + other.scaled(-1)

    def __rsub__(self, other):
        other = self._coerce(other)
        if other is NotImplemented:
            return other
        return other + self.scaled(-1)

    def __pow__(self, k):
        """`p ** k` for an integer k >= 0, by repeated squaring."""
        if isinstance(k, bool) or not isinstance(k, int) or k < 0:
            raise ValueError(t("poly.pow_exponent", k=k))
        out, base = Poly.const(self.vars, 1), self
        while k:
            if k & 1:
                out = out * base
            k >>= 1
            if k:
                base = base * base
        return out

    def __mul__(self, other):
        other = self._coerce(other)
        if other is NotImplemented:
            return other
        if self.vars and len(self.terms) * len(other.terms) >= FLINT_FROM:
            fast = _flint_mul(self, other)
            if fast is not None:
                return Poly._exact(self.vars, {e: c for e, c in fast.items() if c})
        out = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in other.terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                out[e] = out.get(e, Fraction(0)) + c1 * c2
        return Poly._exact(self.vars, {e: c for e, c in out.items() if c})

    __rmul__ = __mul__

    def __truediv__(self, other):
        """Division by a NUMBER is multiplication by its exact inverse;
        `T*T/1` in a spec used to die with an unsupported-operand error.
        Division by a polynomial is not a polynomial and is refused by name."""
        if isinstance(other, Poly):
            raise TypeError(t("poly.divide_by_poly"))
        try:
            c = Fraction(other)
        except (TypeError, ValueError):
            return NotImplemented
        if c == 0:
            raise ZeroDivisionError(t("poly.divide_by_zero"))
        return self.scaled(1 / c)

    def scaled(self, c):
        c = Fraction(c)
        return Poly(self.vars, {} if not c
                    else {e: v * c for e, v in self.terms.items()})

    def term(self, exponent, coef):
        return Poly(self.vars, {exponent: coef})

    # --- order ------------------------------------------------------------

    @staticmethod
    def grevlex(e):
        """Graded reverse lexicographic: the usual default, and the fastest.

        Total degree first, then a reversed-lex tiebreak. Returned as a
        sortable key so the order lives in one place.
        """
        return (sum(e), tuple(-x for x in reversed(e)))

    def lead(self):
        """(exponent, coefficient) of the leading term. None when zero."""
        if not self.terms:
            return None
        e = max(self.terms, key=Poly.grevlex)
        return e, self.terms[e]

    @property
    def degree(self) -> int:
        return max((sum(e) for e in self.terms), default=-1)

    # --- reading and writing ----------------------------------------------

    def __str__(self):
        if not self.terms:
            return "0"
        parts = []
        for e in sorted(self.terms, key=Poly.grevlex, reverse=True):
            c = self.terms[e]
            mono = "*".join("{}^{}".format(v, p) if p > 1 else v
                            for v, p in zip(self.vars, e) if p)
            if not mono:
                parts.append(str(c))
            elif c == 1:
                parts.append(mono)
            elif c == -1:
                parts.append("-" + mono)
            else:
                parts.append("{}*{}".format(c, mono))
        out = parts[0]
        for p in parts[1:]:
            out += (" - " + p[1:]) if p.startswith("-") else (" + " + p)
        return out

    def serialize(self) -> dict:
        return {" ".join(map(str, e)): str(c) for e, c in self.terms.items()}

    @classmethod
    def parse(cls, variables, data) -> "Poly":
        """From `serialize`'s form. Every exponent must have one entry per
        variable: a ring with a variable dropped used to read the same
        exponents position by position, and the polynomial silently became
        another one."""
        variables = tuple(variables)
        terms = {}
        for k, v in data.items():
            # `split()`, not `split(" ")`: a ring with no variables writes its
            # constant under the key "", and `"".split(" ")` is `[""]` -- a
            # PeakSpec with no parameters could not be read back.
            e = tuple(int(x) for x in k.split())
            if len(e) != len(variables):
                raise ValueError(t("poly.exponent_length", got=len(e),
                                   want=len(variables)))
            terms[e] = Fraction(v)
        return cls(variables, terms)


# ---------------------------------------------------------------------------
# division, S-polynomials, Buchberger -- all with the cofactors kept
# ---------------------------------------------------------------------------


def _divides(a, b) -> bool:
    return all(x <= y for x, y in zip(a, b))


def _lcm(a, b):
    return tuple(max(x, y) for x, y in zip(a, b))


def divide(f: Poly, gs, track=None, deadline=None):
    """Multivariate division: f = sum q_i g_i + r.

    `track` carries, for each divisor, how that divisor is written in terms of
    the ORIGINAL generators. When it is given, the returned cofactors are in
    those terms too -- which is the whole point, since a Groebner basis is not
    what anyone stated the problem with.
    """
    n = len(gs)
    quots = [Poly(f.vars) for _ in range(n)]
    coeffs = [Poly(f.vars) for _ in range(len(track[0]) if track else 0)]
    rem = Poly(f.vars)
    cur = f

    while cur:
        # Inside the reduction, not only between pairs: one reduction of a
        # large S-polynomial was where a run spent minutes past its budget.
        _check_clock(deadline)
        le, lc = cur.lead()
        for i, g in enumerate(gs):
            ge, gc = g.lead()
            if _divides(ge, le):
                q = cur.term(tuple(a - b for a, b in zip(le, ge)), lc / gc)
                quots[i] = quots[i] + q
                cur = cur - q * g
                if track:
                    for j in range(len(coeffs)):
                        coeffs[j] = coeffs[j] + q * track[i][j]
                break
        else:
            piece = cur.term(le, lc)
            rem = rem + piece
            cur = cur - piece
    return quots, rem, coeffs


def spoly(f: Poly, g: Poly):
    """The S-polynomial, plus the two multipliers used to build it."""
    fe, fc = f.lead()
    ge, gc = g.lead()
    l = _lcm(fe, ge)
    mf = f.term(tuple(a - b for a, b in zip(l, fe)), Fraction(1) / fc)
    mg = g.term(tuple(a - b for a, b in zip(l, ge)), Fraction(1) / gc)
    return mf * f - mg * g, mf, mg


def groebner(gens, max_pairs=20_000, max_terms=20_000, deadline=None,
             progress=None, stats=None):
    """Buchberger, keeping each basis element written in the generators.

    The tracking is the reason this is not a call to a library. Knowing that
    `f` reduces to zero modulo some basis is not a certificate; knowing `f =
    sum h_i g_i` for the generators SOMEONE ACTUALLY WROTE is.

    Budgets rather than patience: Buchberger's worst case is doubly
    exponential, and a run that will not finish should say so.
    """
    variables = gens[0].vars
    basis = [g for g in gens if g]
    # track[i] = how basis[i] is built from the original generators
    track = []
    for i, g in enumerate(gens):
        if not g:
            continue
        row = [Poly(variables) for _ in gens]
        row[i] = Poly.const(variables, 1)
        track.append(row)

    pairs = list(combinations(range(len(basis)), 2))
    seen = 0
    t_start = time.monotonic()
    last = [t_start]

    def report(final=False):
        # At most once a second, and only sizes: no expression is printed.
        now = time.monotonic()
        if progress is None or (not final and now - last[0] < 1.0):
            return
        last[0] = now
        progress({"phase": "search", "pairs_done": seen,
                  "pairs_pending": len(pairs), "basis": len(basis),
                  "max_terms": max((len(b.terms) for b in basis), default=0),
                  "elapsed_s": round(now - t_start, 1), "final": final})

    while pairs:
        report()
        i, j = pairs.pop()
        seen += 1
        if seen > max_pairs:
            raise Budget(t("poly.budget.pairs", n=max_pairs))
        if deadline is not None and time.monotonic() > deadline:
            raise TimeBudget(t("poly.budget.time"))
        s, mf, mg = spoly(basis[i], basis[j])
        if not s:
            continue
        _, rem, coeffs = divide(s, basis, track, deadline)
        if not rem:
            continue
        if len(rem.terms) > max_terms:
            raise Budget(t("poly.budget.terms", n=max_terms))
        # rem = s - sum(...) and s = mf*g_i - mg*g_j, in generator terms:
        row = [mf * track[i][k] - mg * track[j][k] - coeffs[k]
               for k in range(len(gens))]
        basis.append(rem)
        track.append(row)
        pairs.extend((k, len(basis) - 1) for k in range(len(basis) - 1))
    report(final=True)
    if stats is not None:
        stats.update({"pairs": seen, "basis": len(basis),
                      "max_terms": max((len(b.terms) for b in basis), default=0)})
    return basis, track


# --- linear definitions, eliminated and put back --------------------------


def rational_function(expr, variables):
    """A z3 term as `(numerator, denominator)`, both polynomials.

    `N / D = 0` where `D != 0` is `N = 0` there, so clearing a denominator is
    exact -- ON THE SET WHERE IT DOES NOT VANISH, which is what the caller
    has to be told and what `IdealSpec(clear_denominators=True)` records.
    Users multiplied through by hand, by SymPy's `cancel`, and once by a
    denominator that could be zero. Nothing is cancelled here: a common
    factor stays in both, which is sound and only costs size. The
    denominator comes back monic (its leading coefficient folded into the
    numerator), and a constant one as 1."""
    import z3

    from .linarith import NotPolynomial, _literal_exponent

    V = tuple(variables)
    one = Poly.const(V, 1)

    def add(x, y):
        (n1, d1), (n2, d2) = x, y
        if d1 == d2:
            return n1 + n2, d1
        return n1 * d2 + n2 * d1, d1 * d2

    def rf(e):
        if z3.is_int_value(e):
            return Poly.const(V, e.as_long()), one
        if z3.is_rational_value(e):
            return Poly.const(V, Fraction(e.as_fraction())), one
        if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            if str(e) not in V:
                raise NotPolynomial(t("poly.unknown_variable", name=str(e)))
            return Poly.var(V, str(e)), one
        if z3.is_to_real(e):
            return rf(e.arg(0))
        if z3.is_add(e):
            out = (Poly(V), one)
            for c in e.children():
                out = add(out, rf(c))
            return out
        if z3.is_sub(e):
            a, b = e.children()
            nb, db = rf(b)
            return add(rf(a), (nb.scaled(-1), db))
        if z3.is_app_of(e, z3.Z3_OP_UMINUS):
            n, d = rf(e.arg(0))
            return n.scaled(-1), d
        if z3.is_mul(e):
            n, d = one, one
            for c in e.children():
                cn, cd = rf(c)
                n, d = n * cn, d * cd
            return n, d
        if z3.is_div(e):
            a, b = e.children()
            na, da = rf(a)
            nb, db = rf(b)
            if not nb:
                raise NotPolynomial("division by zero: {}".format(e))
            return na * db, da * nb
        if z3.is_app_of(e, z3.Z3_OP_POWER):
            base, exp = e.children()
            k = _literal_exponent(exp)
            if k is None:
                raise NotPolynomial("non-constant or negative exponent: {}".format(e))
            n, d = rf(base)
            return n ** k, d ** k
        raise NotPolynomial("not rational arithmetic: {}".format(e))

    n, d = rf(expr)
    lead = d.lead()
    if lead is not None and lead[1] != 1:
        n, d = n.scaled(1 / lead[1]), d.scaled(1 / lead[1])
    if d.degree <= 0:
        return n, one
    return n, d


def substitute(p: Poly, var: str, r: Poly) -> Poly:
    """`p` with `var` replaced by `r` (which must not contain `var`)."""
    vi = p.vars.index(var)
    out = Poly(p.vars)
    powers = {0: Poly.const(p.vars, 1)}
    for e, c in p.terms.items():
        d = e[vi]
        if d not in powers:
            powers[d] = r ** d
        rest = list(e)
        rest[vi] = 0
        out = out + Poly(p.vars, {tuple(rest): c}) * powers[d]
    return out


def quotient_by_substitution(p: Poly, var: str, r: Poly) -> Poly:
    """`q` with `p - p[var := r] = q * (var - r)`, exactly: for each term
    `a * var^d`, `var^d - r^d = (var - r) * sum_{i<d} var^i r^(d-1-i)`."""
    vi = p.vars.index(var)
    v = Poly.var(p.vars, var)
    q = Poly(p.vars)
    for e, c in p.terms.items():
        d = e[vi]
        if d == 0:
            continue
        rest = list(e)
        rest[vi] = 0
        a = Poly(p.vars, {tuple(rest): c})
        s = Poly(p.vars)
        for i in range(d):
            s = s + (v ** i) * (r ** (d - 1 - i))
        q = q + a * s
    return q


def linear_definition(g: Poly, skip=()):
    """`(var, c, r)` with `g = c * (var - r)`, `c` a non-zero RATIONAL and `r`
    free of `var` -- a definition that can be substituted without dividing by
    anything that might vanish -- or None. The first such variable in ring
    order, so the choice is deterministic."""
    for vi, var in enumerate(g.vars):
        if var in skip:
            continue
        with_v = {e: c for e, c in g.terms.items() if e[vi]}
        if len(with_v) != 1:
            continue
        (e, c), = with_v.items()
        if e[vi] != 1 or any(x for k, x in enumerate(e) if k != vi):
            continue
        rest = Poly(g.vars, {e2: c2 for e2, c2 in g.terms.items() if not e2[vi]})
        return var, c, rest.scaled(-1 / c)
    return None


def eliminate_linear(gs, target):
    """Substitute every linear definition among `gs`, one at a time.

    Returns `(steps, active, reduced_gs, reduced_target)`: `steps` is
    `[(k, var, c, r, gs_before, target_before, active_before)]`, enough to put
    the cofactors back (`lift`); `active` the indices of the equations left."""
    cur = list(gs)
    tgt = target
    active = list(range(len(gs)))
    steps = []
    while True:
        found = None
        for k in active:
            d = linear_definition(cur[k]) if cur[k] else None
            if d is not None:
                found = (k,) + d
                break
        if found is None:
            break
        k, var, c, r = found
        steps.append((k, var, c, r, list(cur), tgt, list(active)))
        active = [j for j in active if j != k]
        for j in active:
            cur[j] = substitute(cur[j], var, r)
        tgt = substitute(tgt, var, r)
    return steps, active, cur, tgt


def lift(steps, active, hs_active, n):
    """Cofactors of the reduced system (`hs_active[i]` for equation
    `active[i]`) back to all `n` original equations, through the steps in
    reverse: `f = sum h_j g_j + (q_f - sum h_j q_j) (v - r)` and
    `v - r = g_k / c`."""
    variables = None
    h = {}
    for j, hj in zip(active, hs_active):
        h[j] = hj
    for k, var, c, r, gs_before, tgt_before, active_before in reversed(steps):
        variables = tgt_before.vars
        qf = quotient_by_substitution(tgt_before, var, r)
        acc = qf
        for j in active_before:
            if j == k or j not in h:
                continue
            acc = acc - h[j] * quotient_by_substitution(gs_before[j], var, r)
        h[k] = acc.scaled(1 / c)
    zero = None
    out = []
    for j in range(n):
        if j in h:
            out.append(h[j])
        else:
            zero = zero or Poly(variables or hs_active[0].vars)
            out.append(zero)
    return out


def cofactors(f: Poly, gens, **budget):
    """`h_i` with `f = sum h_i g_i`, or None when f is not in the ideal.

    Returns (cofactors, in_ideal). The caller verifies by expanding; this
    function is a search and is allowed to be as clever as it likes.
    """
    basis, track = groebner(list(gens), **budget)
    if not basis:
        return None, not f
    _, rem, coeffs = divide(f, basis, track, budget.get("deadline"))
    if rem:
        return None, False
    return coeffs, True


def normal_form(f: Poly, gens, **budget) -> Poly:
    """`f` reduced modulo the ideal of `gens`: its remainder on division by
    a Groebner basis, zero exactly when `f` is in the ideal. What is LEFT of
    a claim that does not follow -- the factor a user dropped, usually."""
    basis, track = groebner(list(gens), **budget)
    if not basis:
        return f
    _, rem, _coeffs = divide(f, basis, track, budget.get("deadline"))
    return rem


def combination(hs, gs, variables=None) -> Poly:
    """sum h_i g_i. The check, in one line of arithmetic. With no equations
    it is the zero polynomial of `variables` -- an empty ideal, not an
    `IndexError`."""
    out = Poly(gs[0].vars if gs else tuple(variables or ()))
    for h, g in zip(hs, gs):
        out = out + h * g
    return out


# ---------------------------------------------------------------------------
# polynomials written as TEXT, for specs that are data
# ---------------------------------------------------------------------------
#
# A JSON spec cannot carry a z3 term, and `eval` is what this project decided
# not to run on a model's text. So: a small reader for exactly the arithmetic
# a polynomial needs -- numbers (exact, `1/3` and `0.25` alike), names, + - *,
# division by a NUMBER, `^` or `**` with a natural exponent, parentheses --
# and nothing else. A name outside the ring is refused by name.


def _tokens(text):
    import re

    pos, out = 0, []
    pat = re.compile(r"\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_][A-Za-z_0-9]*)|(\*\*|[-+*/^()]))")
    text = str(text)
    while pos < len(text):
        if text[pos:].strip() == "":
            break
        m = pat.match(text, pos)
        if not m or m.end() == pos:
            raise ValueError(t("poly.text_bad", text=text[:60], at=pos))
        out.append(("num", m.group(1)) if m.group(1) else
                   ("name", m.group(2)) if m.group(2) else ("op", m.group(3)))
        pos = m.end()
    return out


def parse_text(variables, text) -> "Poly":
    """`"x^2 - 2*x*y + 1/3"` over the ring `variables`, exactly."""
    ring = tuple(variables)
    toks = _tokens(text)
    i = [0]

    def peek():
        return toks[i[0]] if i[0] < len(toks) else (None, None)

    def take():
        tok = peek()
        i[0] += 1
        return tok

    def expr():
        out = term()
        while peek() in (("op", "+"), ("op", "-")):
            op = take()[1]
            rhs = term()
            out = out + rhs if op == "+" else out - rhs
        return out

    def term():
        out = factor()
        while peek() in (("op", "*"), ("op", "/")):
            op = take()[1]
            rhs = factor()
            if op == "*":
                out = out * rhs
            else:
                if any(any(e) for e in rhs.terms) or not rhs.terms:
                    raise ValueError(t("poly.text_division", text=str(text)[:60]))
                out = out / rhs.terms[(0,) * len(ring)]
        return out

    def factor():
        if peek() == ("op", "-"):
            take()
            return -factor()
        if peek() == ("op", "+"):
            take()
            return factor()
        base = atom()
        if peek() in (("op", "^"), ("op", "**")):
            take()
            kind, val = take()
            if kind != "num" or "." in val:
                raise ValueError(t("poly.text_exponent", text=str(text)[:60]))
            return base ** int(val)
        return base

    def atom():
        kind, val = take()
        if kind == "num":
            return Poly.const(ring, Fraction(val))
        if kind == "name":
            if val not in ring:
                raise ValueError(t("poly.text_name", name=val, ring=", ".join(ring)))
            return Poly.var(ring, val)
        if (kind, val) == ("op", "("):
            out = expr()
            if take() != ("op", ")"):
                raise ValueError(t("poly.text_bad", text=str(text)[:60], at=i[0]))
            return out
        raise ValueError(t("poly.text_bad", text=str(text)[:60], at=i[0]))

    out = expr()
    if i[0] != len(toks):
        raise ValueError(t("poly.text_bad", text=str(text)[:60], at=i[0]))
    return out


def as_poly(ring, x) -> "Poly":
    """A polynomial over `ring` from text, a z3 term, a number or a Poly of
    that ring."""
    ring = tuple(ring)
    if isinstance(x, Poly):
        if x.vars != ring:
            raise ValueError(t("poly.ring_mismatch", got=", ".join(x.vars),
                               want=", ".join(ring)))
        return x
    if isinstance(x, str):
        return parse_text(ring, x)
    if isinstance(x, (int, Fraction)) and not isinstance(x, bool):
        return Poly.const(ring, x)
    return Poly.from_z3(x, ring)


def compose_map(p: "Poly", images: dict, ring) -> "Poly":
    """`p(images)`: every variable of `p` replaced at once by a polynomial
    over the new `ring`."""
    ring = tuple(ring)
    out = Poly(ring)
    powers = {}
    for e, c in p.terms.items():
        term = Poly.const(ring, c)
        for v, k in zip(p.vars, e):
            if k:
                key = (v, k)
                if key not in powers:
                    powers[key] = images[v] ** k
                term = term * powers[key]
        out = out + term
    return out
