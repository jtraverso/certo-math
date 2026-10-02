"""A counterexample as mathematics: what each formula does at the point.

A refutation used to print `a = 2, b = 3`, and the reader recomputed the rest
by hand to see what to change in the proof. This evaluates every formula the
certificate asserts, exactly, at the point it carries:

    a > 0               2 > 0        holds, slack 2
    b <= 2*a            3 <= 4       holds, slack 1
    not(a*b <= a*a + 1) 6 <= 5       FAILS by 1

-- each side of each comparison as an exact number, whether it holds, by how
much, and which inequalities are ACTIVE (equality in a non-strict one): the
boundary the counterexample sits on, which is usually where the proof has to
change.

Computed from the certificate alone, at the time it is read, and never stored:
it cannot drift from what `verify` checks, and the schema does not move.
"""
from __future__ import annotations

from fractions import Fraction

_OPS = (("is_le", "<="), ("is_lt", "<"), ("is_ge", ">="), ("is_gt", ">"),
        ("is_eq", "=="), ("is_distinct", "!="))


def _number(v):
    """An exact number from a simplified z3 value, or its text."""
    import z3

    if z3.is_int_value(v):
        return Fraction(v.as_long())
    if z3.is_rational_value(v):
        return Fraction(v.numerator_as_long(), v.denominator_as_long())
    if z3.is_algebraic_value(v):
        return v.as_decimal(12)
    return str(v)


def _text(x):
    if isinstance(x, Fraction):
        return str(x.numerator) if x.denominator == 1 else str(x)
    return str(x)


def _holds(op, a, b):
    return {"<=": a <= b, "<": a < b, ">=": a >= b, ">": a > b,
            "==": a == b, "!=": a != b}[op]


def _row(f, subs, negated=False):
    import z3

    op = next((sym for name, sym in _OPS if getattr(z3, name)(f)), None)
    if op is None or f.num_args() != 2:
        val = z3.simplify(z3.substitute(f, *subs)) if subs else z3.simplify(f)
        ok = z3.is_true(val)
        return {"formula": ("not " if negated else "") + str(f),
                "holds": ok != negated}
    lhs = _number(z3.simplify(z3.substitute(f.arg(0), *subs)))
    rhs = _number(z3.simplify(z3.substitute(f.arg(1), *subs)))
    row = {"formula": str(f), "lhs": _text(lhs), "op": op, "rhs": _text(rhs)}
    if isinstance(lhs, Fraction) and isinstance(rhs, Fraction):
        inner = _holds(op, lhs, rhs)
        row["holds"] = inner != negated
        gap = abs(lhs - rhs)
        if negated:
            row["fails"] = True            # the claim, negated, holds: it fails
            row["by"] = _text(gap)
        elif inner:
            row["slack"] = _text(gap)
            row["active"] = gap == 0 and op in ("<=", ">=", "==")
        return row
    row["holds"] = None                    # an algebraic value: shown, not judged
    return row


def model_summary(cert) -> list | None:
    """One row per asserted formula (conjunctions split), evaluated exactly
    at the certificate's point -- or None for a certificate that carries no
    point."""
    if getattr(cert, "kind", None) != "model":
        return None
    import z3

    p = cert.payload
    try:
        formulas = list(z3.parse_smt2_string(p["smt2"]))
        consts = {}
        for f in formulas:
            for c in _consts(f):
                consts[str(c)] = c
        subs = []
        for name, (sort, val) in (p.get("assignment") or {}).items():
            c = consts.get(name)
            if c is None:
                continue
            if sort == "Bool":
                subs.append((c, z3.BoolVal(str(val).lower() == "true")))
            elif sort == "Int":
                subs.append((c, z3.IntVal(int(Fraction(val)))))
            else:
                subs.append((c, z3.RealVal(str(Fraction(val)))))
    except (KeyError, TypeError, ValueError, z3.Z3Exception):
        return None
    rows = []

    def add(f, negated=False):
        if not negated and z3.is_and(f):
            for g in f.children():
                add(g)
            return
        if not negated and z3.is_not(f):
            add(f.arg(0), negated=True)
            return
        rows.append(_row(f, subs, negated))

    for f in formulas:
        add(f)
    return rows


def _consts(f):
    from . import z3util

    return z3util.free_consts(f)


def _tag(r) -> str:
    from .i18n import t

    if r.get("fails"):
        return t("explain.fails", by=r["by"])
    if r.get("holds") is None:
        return t("explain.algebraic")
    if r.get("holds"):
        if r.get("active"):
            return t("explain.active")
        return (t("explain.holds", slack=r["slack"]) if "slack" in r
                else t("explain.holds_plain"))
    return t("explain.violated")


def _values(r) -> str:
    return "{} {} {}".format(r["lhs"], r["op"], r["rhs"]) if "op" in r else ""


def lines(rows) -> list:
    """The rows as aligned text, for the terminal."""
    if not rows:
        return []
    width = min(48, max(len(r["formula"]) for r in rows))
    out = []
    for r in rows:
        f = (r["formula"] if len(r["formula"]) <= width
             else r["formula"][:width - 1] + "~")
        out.append("{:<{w}}  {:<18} {}".format(f, _values(r), _tag(r), w=width))
    return out


def markdown(rows) -> str:
    """The rows as a Markdown table, to paste into a proof."""
    from .i18n import t

    out = ["| {} | {} | |".format(t("explain.formula"), t("explain.value")),
           "|---|---|---|"]
    for r in rows or []:
        out.append("| `{}` | {} | {} |".format(r["formula"], _values(r), _tag(r)))
    return "\n".join(out)
