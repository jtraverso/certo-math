"""Boolean formulas to CNF, deterministically -- so a refutation can be
checked by unit propagation instead of by asking a solver again.

A `prove` over Boolean hypotheses -- incidences, Hall conditions with a
capacity -- produced an `unsat_core` certificate that verifies by re-solving
the core: right, and a solver in the trusted base. With `--drat` the core is
encoded here, refuted by the internal CDCL with a DRUP proof, and the
certificate carries the core and the proof. `verify` encodes the core AGAIN,
with this same function, and checks the proof against what it built. The
encoding is part of the trusted base, which is why it is small and
deterministic: same formulas, same clauses, same variable numbers.

What is encoded:

  * Boolean constants; `True`, `False`; `Not`, `And`, `Or`, `Implies`,
    `Xor`, `==` between Booleans, `If` with Boolean branches;
  * cardinality: `AtMost(..., k)`, `AtLeast(..., k)`, and a count compared to
    an integer -- `Sum(If(b, 1, 0), ...) <= k`, with `<`, `>=`, `>`, `==` --
    through a sequential counter whose outputs are DEFINED both ways, so a
    count can sit anywhere in a formula, negated or nested.

Anything else is refused by name: an integer that is not a count of
Booleans, a weighted sum, a real.
"""
from __future__ import annotations

import z3

from .cnf import CNF
from .i18n import t

#: The encoding's version: a verifier reads only what it knows how to build.
ENCODING = "certo-bool-1"


class NotPropositional(ValueError):
    """The formula has something this encoding does not take."""


class _Enc:
    def __init__(self):
        self.cnf = CNF()
        self.memo = {}
        self._true = None

    def true(self):
        if self._true is None:
            self._true = self.cnf.var("__true")
            self.cnf.add(self._true)
        return self._true

    def fresh(self, tag):
        return self.cnf.aux(tag)

    # -- Boolean structure --------------------------------------------------

    def lit(self, e):
        key = e.get_id()
        if key in self.memo:
            return self.memo[key]
        out = self._lit(e)
        self.memo[key] = out
        return out

    def _lit(self, e):
        if z3.is_true(e):
            return self.true()
        if z3.is_false(e):
            return -self.true()
        if not z3.is_bool(e):
            raise NotPropositional(t("boolenc.not_bool", expr=str(e)[:80]))
        if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            return self.cnf.var(str(e))
        k = e.decl().kind()
        args = [e.arg(i) for i in range(e.num_args())]
        if k == z3.Z3_OP_NOT:
            return -self.lit(args[0])
        if k in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            xs = [self.lit(a) for a in args]
            g = self.fresh("and" if k == z3.Z3_OP_AND else "or")
            if k == z3.Z3_OP_AND:
                for x in xs:
                    self.cnf.add(-g, x)
                self.cnf.add(g, *[-x for x in xs])
            else:
                for x in xs:
                    self.cnf.add(g, -x)
                self.cnf.add(-g, *xs)
            return g
        if k == z3.Z3_OP_IMPLIES:
            a, b = self.lit(args[0]), self.lit(args[1])
            g = self.fresh("imp")
            self.cnf.add(-g, -a, b)
            self.cnf.add(g, a)
            self.cnf.add(g, -b)
            return g
        if k in (z3.Z3_OP_IFF, z3.Z3_OP_XOR) or (
                k == z3.Z3_OP_EQ and z3.is_bool(args[0])):
            a, b = self.lit(args[0]), self.lit(args[1])
            g = self.fresh("iff")
            # g <-> (a <-> b)
            self.cnf.add(-g, -a, b)
            self.cnf.add(-g, a, -b)
            self.cnf.add(g, a, b)
            self.cnf.add(g, -a, -b)
            return -g if k == z3.Z3_OP_XOR else g
        if k == z3.Z3_OP_ITE and z3.is_bool(args[1]):
            c, a, b = (self.lit(x) for x in args)
            g = self.fresh("ite")
            self.cnf.add(-g, -c, a)
            self.cnf.add(-g, c, b)
            self.cnf.add(g, -c, -a)
            self.cnf.add(g, c, -b)
            return g
        if k in (z3.Z3_OP_PB_AT_MOST, z3.Z3_OP_PB_AT_LEAST):
            bound = int(e.decl().params()[0])
            xs = [self.lit(a) for a in args]
            ge = self.at_least(xs, bound + 1 if k == z3.Z3_OP_PB_AT_MOST else bound)
            return -ge if k == z3.Z3_OP_PB_AT_MOST else ge
        if k in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
            return self.compare(k, args[0], args[1])
        raise NotPropositional(t("boolenc.unsupported", expr=str(e)[:80]))

    # -- counts --------------------------------------------------------------

    def count(self, e):
        """`(literals, constant)` with `e = constant + #true(literals)`."""
        if z3.is_int_value(e):
            return [], e.as_long()
        k = e.decl().kind() if z3.is_app(e) else None
        if k == z3.Z3_OP_ADD:
            lits, const = [], 0
            for i in range(e.num_args()):
                l2, c2 = self.count(e.arg(i))
                lits += l2
                const += c2
            return lits, const
        if k == z3.Z3_OP_ITE:
            c, a, b = e.arg(0), e.arg(1), e.arg(2)
            if z3.is_int_value(a) and z3.is_int_value(b):
                va, vb = a.as_long(), b.as_long()
                if (va, vb) == (1, 0):
                    return [self.lit(c)], 0
                if (va, vb) == (0, 1):
                    return [-self.lit(c)], 0
        raise NotPropositional(t("boolenc.not_count", expr=str(e)[:80]))

    def compare(self, k, lhs, rhs):
        if z3.is_bool(lhs):
            raise NotPropositional(t("boolenc.unsupported", expr=str(lhs)[:80]))
        l1, c1 = self.count(lhs)
        l2, c2 = self.count(rhs)
        if l1 and l2:
            raise NotPropositional(t("boolenc.two_counts"))
        if l2:                       # constant OP count  ->  count OP' constant
            flip = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                    z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT,
                    z3.Z3_OP_EQ: z3.Z3_OP_EQ}
            return self.compare_count(flip[k], l2, c1 - c2)
        return self.compare_count(k, l1, c2 - c1)

    def compare_count(self, k, xs, bound):
        """`#true(xs) OP bound`."""
        if k == z3.Z3_OP_LE:
            return -self.at_least(xs, bound + 1)
        if k == z3.Z3_OP_LT:
            return -self.at_least(xs, bound)
        if k == z3.Z3_OP_GE:
            return self.at_least(xs, bound)
        if k == z3.Z3_OP_GT:
            return self.at_least(xs, bound + 1)
        a, b = self.at_least(xs, bound), self.at_least(xs, bound + 1)
        g = self.fresh("eq")
        self.cnf.add(-g, a)
        self.cnf.add(-g, -b)
        self.cnf.add(g, -a, b)
        return g

    def at_least(self, xs, k):
        """A literal equivalent to "at least k of xs": a sequential counter
        with s[i][j] <-> s[i-1][j] OR (x_i AND s[i-1][j-1]), both ways."""
        n = len(xs)
        if k <= 0:
            return self.true()
        if k > n:
            return -self.true()
        prev = {}                                  # j -> literal, for i-1
        for i, x in enumerate(xs, start=1):
            cur = {}
            for j in range(1, min(i, k) + 1):
                carry_prev = prev.get(j)           # None: false
                carry_low = self.true() if j == 1 else prev.get(j - 1)
                s = self.fresh("cnt")
                # s -> carry_prev OR (x AND carry_low)
                terms = []
                if carry_prev is not None:
                    terms.append(carry_prev)
                if carry_low is not None:
                    self.cnf.add(-s, *(terms + [x]))
                    self.cnf.add(-s, *(terms + [carry_low]))
                    # (x AND carry_low) -> s
                    self.cnf.add(s, -x, -carry_low)
                else:
                    self.cnf.add(-s, *terms) if terms else self.cnf.add(-s)
                if carry_prev is not None:
                    self.cnf.add(s, -carry_prev)
                cur[j] = s
            prev = cur
        return prev.get(k, -self.true())


def encode(formulas):
    """`CNF` asserting every formula. Deterministic: the same formulas give
    the same clauses and the same variable numbers."""
    enc = _Enc()
    for f in formulas:
        enc.cnf.add(enc.lit(f))
    return enc.cnf


def propositional(formulas) -> str | None:
    """None when every formula encodes; otherwise why not."""
    try:
        encode(formulas)
    except NotPropositional as e:
        return str(e)
    return None
