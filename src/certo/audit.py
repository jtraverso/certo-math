"""Does each hypothesis earn its place? Drop it and go looking.

`core` answers the other half. It says WHICH hypotheses an unsat core needed
and drops the rest, which catches a theorem stated with slack. It cannot
catch the opposite mistake, and the opposite mistake is the expensive one:

    a theorem stated TOO STRONGLY, formalised, and only then found to have
    been about a smaller class than anybody wanted

So this drops each hypothesis in turn and hunts a counterexample to what
remains. Four answers per hypothesis, and they are genuinely different:

  NEEDED, with a witness. Without it the claim is false, and here is the
  assignment that breaks it. That witness is the useful artefact: it says not
  only that the hypothesis matters but HOW, which is what tells you whether
  you wrote the right one.

  REDUNDANT. The claim still follows without it, so the theorem is weaker than
  it looks and can be stated without it. `core` finds these too; they appear
  here because a per-hypothesis report that silently omitted them would read
  as "all needed".

  DOMAIN. Dropping it does not make the claim false -- it makes the claim
  MEANINGLESS, because it was holding up a well-definedness condition. See
  below; this one exists because reporting it as either of the other two
  would have been a lie in a different direction each time.

  UNKNOWN. The solver did not settle it inside the budget. Never folded into
  any of the other three -- "we did not find a counterexample" is not "there
  is none", and that distinction is the whole discipline here.

DIVISION IS TOTAL IN SMT, AND THAT IS A TRAP. `n/0` is not an error in Z3; it
is some fixed but unspecified value, supplied by an internal function the
solver is free to interpret however it likes. So dropping `d != 0` and asking
for a counterexample gets you one immediately: `d = 0`, with `div0` chosen to
make the goal false. The hypothesis then reads `needed`, which is true by
accident and false in substance -- it is needed for the statement to MEAN
something, not for it to be true.

So the divisors are collected up front and every search is GUARDED by them.
A hypothesis whose drop leaves a counterexample only outside the domain is
reported as DOMAIN, naming the obligation it was carrying, rather than as
`needed` with a witness that divides by zero.

The guards are also what the witnesses are checked against on the way back,
and Z3's internal `div0`/`mod0` are excluded from a witness entirely: they
are the solver's bookkeeping, never part of the problem, and a witness that
carried them could not be re-applied.

WHAT THIS IS FOR is the step before formalisation. Formalising a theorem whose
hypotheses were never tested is how a month goes into proving something that
is true of a smaller class than the paper claims, and the test is cheap: one
satisfiability query per hypothesis.

WHAT IT IS NOT is a proof that the hypothesis set is minimal. Dropping them ONE
at a time says nothing about dropping two -- a pair can be jointly redundant
with neither redundant alone. Said in the certificate, every time.
"""
from __future__ import annotations

from .i18n import t as _t


class NotAuditable(ValueError):
    """Raised with the reason, because a bare failure helps nobody."""


NEEDED, REDUNDANT, UNKNOWN = "needed", "redundant", "unknown"
#: A hypothesis holding up a well-definedness condition rather than a
#: mathematical one. Not `needed` -- the claim does not become false without
#: it -- and emphatically not `redundant`, because removing it does not give
#: a more general theorem, it gives a statement about `n/0`.
DOMAIN = "domain"

VERDICTS = (NEEDED, REDUNDANT, DOMAIN, UNKNOWN)

#: Z3 totalises division and modulo with these; they are the solver's
#: bookkeeping and never part of the problem, so they are not part of a
#: witness either.
INTERNAL = ("div0", "mod0", "rem0")


def divisors(*expressions) -> list:
    """Every divisor appearing anywhere in these formulas.

    A numeral divisor needs no obligation -- `n/3` is defined for every `n` --
    so only the ones that could vanish are collected, deduplicated by their
    printed form because two occurrences of the same expression are one
    obligation.
    """
    import z3

    kinds = {z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM}
    found, seen = [], set()

    def walk(e):
        if not z3.is_app(e):
            return
        if e.decl().kind() in kinds:
            den = e.arg(1)
            if not (z3.is_int_value(den) or z3.is_rational_value(den)):
                key = den.sexpr()
                if key not in seen:
                    seen.add(key)
                    found.append(den)
        for i in range(e.num_args()):
            walk(e.arg(i))

    for expr in expressions:
        if expr is not None:
            walk(expr)
    return found


def obligations_for(spec) -> list:
    """The domain obligations of a spec, as `(text, formula)` pairs."""
    import z3

    out = []
    for den in divisors(spec.goal, *[f for _n, f in spec.assumptions]):
        out.append((den.sexpr(), den != 0))
    return out


def _assignment(model) -> dict:
    """The witness, without the solver's own bookkeeping.

    Only arity-zero declarations of a sort that can be written back down:
    `div0` and `mod0` are functions Z3 invented to make division total, and a
    witness carrying them cannot be re-applied by anybody, including us.
    """
    known = {"Real", "Int", "Bool"}
    return {str(d): [d.range().name(), str(model[d])]
            for d in model.decls()
            if d.arity() == 0 and d.range().name() in known
            and str(d) not in INTERNAL}


def audit(spec, limits=None) -> dict:
    """One satisfiability query per hypothesis: what breaks without it."""
    import z3

    from .limits import Limits
    from .status import Status

    if spec.goal is None:
        raise NotAuditable(_t("audit.no_goal"))
    if not spec.assumptions:
        raise NotAuditable(_t("audit.no_hypotheses"))

    lim = limits or Limits()
    duties = obligations_for(spec)
    rows = []
    for dropped, _formula in spec.assumptions:
        keep = [(n, f) for n, f in spec.assumptions if n != dropped]
        s = z3.Solver()
        lim.apply_to(s)
        for _n, f in keep:
            s.add(f)
        # A counterexample to the claim, under everything EXCEPT this one --
        # and INSIDE the domain, because `n/0` is a value Z3 makes up and a
        # counterexample that uses it is about the solver, not the theorem.
        s.add(z3.Not(spec.goal))
        for _text, guard in duties:
            s.add(guard)
        got = s.check()

        if got == z3.sat:
            rows.append({"hypothesis": dropped, "verdict": NEEDED,
                         "witness": _assignment(s.model())})
        elif got == z3.unsat:
            lost = _lost_obligations(keep, duties, lim)
            if lost:
                rows.append({"hypothesis": dropped, "verdict": DOMAIN,
                             "witness": None, "obligations": lost})
            else:
                rows.append({"hypothesis": dropped, "verdict": REDUNDANT,
                             "witness": None})
        else:
            rows.append({"hypothesis": dropped, "verdict": UNKNOWN,
                         "witness": None,
                         "why": str(s.reason_unknown() or "")})
        _ = Status

    counts = {v: sum(1 for r in rows if r["verdict"] == v) for v in VERDICTS}
    return {"rows": rows, "counts": counts,
            "obligations": [text for text, _g in duties],
            "ok": counts[UNKNOWN] == 0,
            "redundant": [r["hypothesis"] for r in rows
                          if r["verdict"] == REDUNDANT],
            "domain": [r["hypothesis"] for r in rows
                       if r["verdict"] == DOMAIN]}


def _lost_obligations(keep, duties, lim) -> list:
    """Which well-definedness conditions the remaining hypotheses no longer
    force.

    This is what separates DOMAIN from REDUNDANT, and it is a question about
    the hypotheses rather than about the goal: if what is left still entails
    every divisor being non-zero, the dropped one really was carrying nothing
    and `redundant` is the honest answer.
    """
    import z3

    lost = []
    for text, guard in duties:
        s = z3.Solver()
        lim.apply_to(s)
        for _n, f in keep:
            s.add(f)
        s.add(z3.Not(guard))
        if s.check() != z3.unsat:       # the obligation is no longer forced
            lost.append(text)
    return lost


def declared_obligations(payload) -> dict:
    """Re-derive the domain obligations from the formulas that travelled.

    A certificate declaring FEWER divisors than its own formulas contain is a
    certificate whose searches ran unguarded, and every `needed` verdict in it
    could be a division by zero. So this is derived rather than read -- the
    same reason a branch-and-bound node rebuilds its own linear program.

    A certificate written before obligations existed declares none, and one
    that lists MORE than it needs has only searched a smaller region, which is
    sound and merely weaker -- so neither of those fails.
    """
    import z3

    formulas = [z3.And(*z3.parse_smt2_string(smt2))
                for smt2 in (payload.get("hypotheses_smt2") or {}).values()]
    goal = z3.And(*z3.parse_smt2_string(payload["goal_smt2"]))
    found = [d.sexpr() for d in divisors(goal, *formulas)]

    declared = payload.get("obligations")
    if declared is None:
        # Nothing was claimed, so nothing is contradicted. The rows are still
        # checked against the guards by `recheck`, which is where an unguarded
        # witness actually fails.
        return {"ok": True, "found": found, "missing": [], "declared": []}
    missing = [d for d in found if d not in set(declared)]
    return {"ok": not missing, "found": found, "missing": missing,
            "declared": list(declared)}


def recheck(payload, limits=None) -> dict:
    """Re-run every witness against the formulas it claims to break.

    The witness is the whole content of a NEEDED verdict, and checking one is
    evaluation rather than search: substitute the assignment, and the kept
    hypotheses must hold while the goal must not. A verdict with a witness
    that does not do that is a verdict about nothing.
    """
    import z3

    from .limits import Limits

    lim = limits or Limits()
    formulas = {}
    for name, smt2 in (payload.get("hypotheses_smt2") or {}).items():
        formulas[name] = z3.And(*z3.parse_smt2_string(smt2))
    goal = z3.And(*z3.parse_smt2_string(payload["goal_smt2"]))
    duties = divisors(goal, *formulas.values())

    bad, checked = [], 0
    for row in payload["rows"]:
        if row["verdict"] != NEEDED or not row.get("witness"):
            continue
        checked += 1
        subs = []
        for name, (sort, value) in row["witness"].items():
            try:
                var = {"Real": z3.Real, "Int": z3.Int,
                       "Bool": z3.Bool}[sort](name)
                lit = {"Real": z3.RealVal, "Int": z3.IntVal,
                       "Bool": lambda v: z3.BoolVal(v == "True")}[sort](value)
            except (KeyError, ValueError):
                bad.append(row["hypothesis"])
                break
            subs.append((var, lit))
        else:
            kept = [f for n, f in formulas.items()
                    if n != row["hypothesis"]]
            claim = z3.And(*kept) if kept else z3.BoolVal(True)
            s = z3.Solver()
            lim.apply_to(s)
            # The witness must satisfy what was KEPT, stay inside the domain,
            # and break the goal. Without the middle one a witness that
            # divides by zero re-checks happily, which is how the defect that
            # put this line here got past the first version.
            inside = [z3.substitute(d, *subs) != 0 for d in duties]
            s.add(z3.Not(z3.And(z3.substitute(claim, *subs),
                                *inside,
                                z3.Not(z3.substitute(goal, *subs)))))
            if s.check() != z3.unsat:
                bad.append(row["hypothesis"])

    # REDUNDANT and DOMAIN are POSITIVE claims -- the goal still follows
    # without the hypothesis -- and they were not re-checked at all: a
    # certificate could call a needed hypothesis redundant, and the reader
    # would drop it. Each is asked again, the way `audit` asked it.
    unproved = []
    guards = [(d.sexpr(), d != 0) for d in duties]
    for row in payload["rows"]:
        if row["verdict"] not in (REDUNDANT, DOMAIN):
            continue
        checked += 1
        keep = [(n, f) for n, f in formulas.items() if n != row["hypothesis"]]
        s = z3.Solver()
        lim.apply_to(s)
        for _n, f in keep:
            s.add(f)
        s.add(z3.Not(goal))
        for _text, guard in guards:
            s.add(guard)
        if s.check() != z3.unsat:
            unproved.append(row["hypothesis"])
            continue
        lost = _lost_obligations(keep, guards, lim)
        if (row["verdict"] == REDUNDANT) != (not lost) or (
                row["verdict"] == DOMAIN
                and sorted(row.get("obligations") or []) != sorted(lost)):
            unproved.append(row["hypothesis"])
    return {"checked": checked, "bad": sorted(set(bad)),
            "unproved": sorted(set(unproved))}
