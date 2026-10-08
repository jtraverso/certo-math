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
        return ctx.from_dict({e: fl.fmpq(c.numerator, c.denominator)
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
        """A z3 arithmetic term, through the same parser `farkas` uses."""
        from .linarith import polynomial

        poly = polynomial(expr)
        out = {}
        for mono, coef in poly.items():
            e = [0] * len(variables)
            for v in mono:
                e[list(variables).index(v)] += 1
            key = tuple(e)
            out[key] = out.get(key, Fraction(0)) + coef
        return cls(variables, out)

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
