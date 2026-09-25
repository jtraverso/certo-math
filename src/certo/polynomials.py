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

from fractions import Fraction
from itertools import combinations

from .i18n import t


class Budget(RuntimeError):
    """Buchberger ran past its budget. Says so; does not guess."""


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

    def __add__(self, other):
        out = dict(self.terms)
        for e, c in other.terms.items():
            out[e] = out.get(e, Fraction(0)) + c
            if not out[e]:
                del out[e]
        return Poly._exact(self.vars, out)

    def __sub__(self, other):
        return self + other.scaled(-1)

    def __mul__(self, other):
        out = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in other.terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                out[e] = out.get(e, Fraction(0)) + c1 * c2
        return Poly._exact(self.vars, {e: c for e, c in out.items() if c})

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
        return cls(variables, {tuple(int(x) for x in k.split(" ")): Fraction(v)
                               for k, v in data.items()})


# ---------------------------------------------------------------------------
# division, S-polynomials, Buchberger -- all with the cofactors kept
# ---------------------------------------------------------------------------


def _divides(a, b) -> bool:
    return all(x <= y for x, y in zip(a, b))


def _lcm(a, b):
    return tuple(max(x, y) for x, y in zip(a, b))


def divide(f: Poly, gs, track=None):
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


def groebner(gens, max_pairs=20_000, max_terms=20_000):
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
    while pairs:
        i, j = pairs.pop()
        seen += 1
        if seen > max_pairs:
            raise Budget(t("poly.budget.pairs", n=max_pairs))
        s, mf, mg = spoly(basis[i], basis[j])
        if not s:
            continue
        _, rem, coeffs = divide(s, basis, track)
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
    return basis, track


def cofactors(f: Poly, gens, **budget):
    """`h_i` with `f = sum h_i g_i`, or None when f is not in the ideal.

    Returns (cofactors, in_ideal). The caller verifies by expanding; this
    function is a search and is allowed to be as clever as it likes.
    """
    basis, track = groebner(list(gens), **budget)
    if not basis:
        return None, not f
    _, rem, coeffs = divide(f, basis, track)
    if rem:
        return None, False
    return coeffs, True


def combination(hs, gs) -> Poly:
    """sum h_i g_i. The check, in one line of arithmetic."""
    out = Poly(gs[0].vars)
    for h, g in zip(hs, gs):
        out = out + h * g
    return out
