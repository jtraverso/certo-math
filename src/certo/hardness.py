"""Why a question did not settle: the structure, not the budget.

A user's claim mixed a linear budget with floors and a quadratic in the size
of a reserve; z3 timed out, and certo said "raise --rlimit or --timeout-ms".
They kept the limits and split it in three -- a linear bound implying the
reserve's size, the forbidden cost reduced to a line, a one-variable
quadratic -- and every piece closed at once. What they needed from the tool
was the FIRST step: this is integer arithmetic with products AND floors,
which has no decision procedure, and here is where it comes from.

`report(formulas)` reads each named formula and says which theory it lives
in (linear or not, integer, real or both), whether it divides or takes
floors and remainders, its degree, and WHICH hypotheses bring each of those.
`hint(report)` turns that into something to do. Nothing here proves
anything; it is a reading of the question.
"""
from __future__ import annotations

import z3

from .i18n import t


def _walk(e, acc):
    """Degree of `e`, filling `acc` with what it contains."""
    if z3.is_int_value(e) or z3.is_rational_value(e) or z3.is_true(e) or z3.is_false(e):
        return 0
    if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        if z3.is_int(e):
            acc["int"] = True
        elif z3.is_real(e):
            acc["real"] = True
        return 1 if z3.is_arith(e) else 0
    k = e.decl().kind() if z3.is_app(e) else None
    kids = e.children()
    if k in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM):
        acc["div_mod"] = True
        degs = [_walk(c, acc) for c in kids]
        return max(degs or [0])
    if k == z3.Z3_OP_TO_INT:
        acc["floor"] = True
        return _walk(kids[0], acc)
    if k == z3.Z3_OP_IS_INT:
        acc["floor"] = True
        return _walk(kids[0], acc)
    if k == z3.Z3_OP_DIV:
        a, b = kids
        db = _walk(b, acc)
        if db > 0:
            acc["divides_by_variable"] = True
        return _walk(a, acc) + db
    if k == z3.Z3_OP_MUL:
        degs = [_walk(c, acc) for c in kids]
        if sum(1 for d in degs if d > 0) > 1 or any(d > 1 for d in degs):
            acc["products"] = acc.get("products", 0) + 1
        return sum(degs)
    if k == z3.Z3_OP_POWER:
        base, exp = kids
        db = _walk(base, acc)
        n = None
        if z3.is_int_value(exp):
            n = exp.as_long()
        elif z3.is_rational_value(exp) and exp.as_fraction().denominator == 1:
            n = exp.as_fraction().numerator
        if n is None or n < 0:
            acc["nonpolynomial"] = True
            return db
        if db > 0 and n > 1:
            acc["products"] = acc.get("products", 0) + 1
        return db * n
    if z3.is_quantifier(e):
        acc["quantifier"] = True
        return _walk(e.body(), acc)
    degs = [_walk(c, acc) for c in kids]
    return max(degs or [0])


def report(formulas: dict) -> dict:
    """`{"theory", "degree", "floors", "divides", "by_hypothesis": {...}}`
    for `{name: z3 formula}`."""
    by = {}
    total = {}
    deg = 0
    for name, f in formulas.items():
        acc = {}
        d = _walk(f, acc)
        acc["degree"] = d
        by[name] = acc
        deg = max(deg, d)
        for key, val in acc.items():
            if key != "degree" and val:
                total[key] = True
    nonlinear = deg > 1 or bool(total.get("products")) \
        or bool(total.get("divides_by_variable"))
    ints, reals = bool(total.get("int")), bool(total.get("real"))
    sort = "IRA" if ints and reals else ("IA" if ints else "RA")
    theory = ("N" if nonlinear else "L") + sort
    return {
        "theory": theory,
        "degree": deg,
        "floors": bool(total.get("floor") or total.get("div_mod")),
        "divides": bool(total.get("divides_by_variable")),
        "quantifiers": bool(total.get("quantifier")),
        "nonlinear_in": sorted(n for n, a in by.items()
                               if a["degree"] > 1 or a.get("products")
                               or a.get("divides_by_variable")),
        "floors_in": sorted(n for n, a in by.items()
                            if a.get("floor") or a.get("div_mod")),
        "by_hypothesis": by,
    }


def hint(rep: dict) -> str:
    """One sentence: what makes this hard, and the first thing to try. Never
    "raise the limits" -- that is the default advice it replaces."""
    names = lambda xs: ", ".join(xs[:4]) or "-"  # noqa: E731
    th = rep["theory"]
    if th.startswith("NIA") or th.startswith("NIRA"):
        if rep["floors"]:
            return t("hardness.nia_floors", theory=th, degree=rep["degree"],
                     nonlinear=names(rep["nonlinear_in"]),
                     floors=names(rep["floors_in"]))
        return t("hardness.nia", theory=th, degree=rep["degree"],
                 nonlinear=names(rep["nonlinear_in"]))
    if th.startswith("NRA"):
        return t("hardness.nra", degree=rep["degree"],
                 nonlinear=names(rep["nonlinear_in"]))
    if rep["floors"]:
        return t("hardness.floors", theory=th, floors=names(rep["floors_in"]))
    if rep["quantifiers"]:
        return t("hardness.quantifiers")
    return t("hardness.linear", theory=th)
