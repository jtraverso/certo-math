"""Templates: synthesise a FUNCTION, not only a constant.

`synth` finds values for its implementation variables. A template makes
those values the coefficients of a function -- a polynomial of a given
degree, or a combination of terms you choose -- so the search finds
`f(n) = 3 n^2 - n + 2` instead of a threshold, and `--prove-candidate`
proves the found function for every n, not only on the bounded domain.

    f = templates.polynomial("f", [n], degree=2, lo=-10, hi=10)
    SynthSpec(templates=[f], input_vars=[n],
              behavior=z3.And(n >= 0, n <= 20),
              correctness=f.expr >= n * (n - 1) / 2)

The coefficients join the implementation variables, their bounds join the
implementation's constraints, and the result names the function found.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from itertools import combinations_with_replacement

import z3


@dataclass
class Template:
    name: str
    expr: object                      # the function, over the coefficients
    vars: list                        # the coefficients: implementation vars
    constraints: list = field(default_factory=list)   # their bounds

    def instantiate(self, values: dict) -> str:
        """The function with the coefficients found, as text."""
        subs = []
        for v in self.vars:
            if str(v) in values:
                val = values[str(v)]
                val = val[1] if isinstance(val, (list, tuple)) else val
                subs.append((v, z3.RealVal(val) if z3.is_real(v) else z3.IntVal(val)))
        return " ".join(str(z3.simplify(z3.substitute(self.expr, *subs))).split())


def _coef(name, k, integer):
    return (z3.Int if integer else z3.Real)("{}_c{}".format(name, k))


def polynomial(name, variables, degree, lo=-10, hi=10, integer=True) -> Template:
    """`sum c_m * m` over every monomial `m` of total degree <= `degree` in
    `variables`, each coefficient in [lo, hi] (integers by default)."""
    variables = list(variables)
    monos = [z3.IntVal(1)]
    for d in range(1, degree + 1):
        for combo in combinations_with_replacement(variables, d):
            term = combo[0]
            for v in combo[1:]:
                term = term * v
            monos.append(term)
    return combination(name, monos, lo=lo, hi=hi, integer=integer)


def combination(name, terms, lo=-10, hi=10, integer=True) -> Template:
    """`sum c_i * terms[i]`: a linear combination of terms you choose --
    `[1, n, n * n, 2 ** n]` written as z3 terms -- with bounded coefficients."""
    cs = [_coef(name, k, integer) for k in range(len(terms))]
    expr = z3.Sum([c * t for c, t in zip(cs, terms)]) if cs else z3.IntVal(0)
    cons = []
    for c in cs:
        if lo is not None:
            cons.append(c >= lo)
        if hi is not None:
            cons.append(c <= hi)
    return Template(name=name, expr=expr, vars=cs, constraints=cons)
