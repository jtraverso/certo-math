"""SMT engine: prove, check, core.

Uses boolean assumptions (`check(p1, ..., pk)`) rather than assert_and_track,
so that deletion-based MUS does not have to rebuild the solver at every step.
"""
from __future__ import annotations

import time

import z3

from .. import linarith, z3util
from ..certificate import (core_matrix_certificate, model_certificate,
                           unsat_core_certificate)
from ..limits import Limits
from ..i18n import t
from ..status import (Result, Status, Verdict, classify_unknown,
                      readable_reason)

ENGINE = "z3:" + z3.get_version_string()


def _tracked(spec, negate_goal: bool):
    """Return (solver, {name: indicator}, formulas) ready for check()."""
    s = z3.Solver()
    items = list(spec.assumptions)
    if spec.goal is not None:
        items.append(("__goal__", z3.Not(spec.goal) if negate_goal else spec.goal))
    ind = {}
    for name, f in items:
        # FRESH, not named. `z3.Bool("__p_" + name)` was a name a spec could
        # use too: a claim over the Boolean `__p___goal__` WAS the goal's
        # indicator, the solver solved a different formula, and a free
        # proposition came back PROVED. A fresh constant cannot be spelled by
        # anyone, and the core is mapped back by identity, not by slicing a
        # name.
        p = z3.FreshBool("certo_ind")
        ind[name] = p
        s.add(z3.Implies(p, f))
    return s, ind, dict(items)


def _core_names(core, ind):
    """The hypothesis names of an unsat core, by indicator identity."""
    back = {p.get_id(): name for name, p in ind.items()}
    return {back[c.get_id()] for c in core if c.get_id() in back}


def _outcome(r, s):
    if r == z3.sat:
        return Status.SAT
    if r == z3.unsat:
        return Status.UNSAT
    return classify_unknown(s.reason_unknown())


def _model_cert(spec, formulas, model, used_names):
    exprs = [formulas[n] for n in used_names]
    consts = z3util.free_consts(*exprs)
    return model_certificate(z3util.smt2(*exprs), z3util.assignment(model, consts))


def _mus(s, ind, names, limits):
    """Deletion-based MUS: guaranteed minimal, not necessarily minimum."""
    core = list(names)
    for name in list(core):
        trial = [n for n in core if n != name]
        if s.check(*[ind[n] for n in trial]) == z3.unsat:
            core = trial
    return core



def _vacuous(s, ind, names, limits):
    """Are the hypotheses contradictory among themselves? And WHICH ones?

    `prove` succeeds when `hypotheses AND not goal` is unsatisfiable -- and if
    the hypotheses alone are already unsatisfiable, that happens for EVERY
    goal. The proof is valid and says nothing, which is the most embarrassing
    way to be wrong and the easiest to miss: the output looks like success.

    Returns the MINIMAL clashing subset rather than a bare `True`. The
    deletion-based MUS is right there and the answer to "which pair clashes"
    is what anyone asks next; telling them to go and run another command was
    an answer that made them do the work twice.

    One extra solver call to detect it, plus the MUS on a strictly smaller
    problem, and only on the successful path.
    """
    hyps = [n for n in names if n != "__goal__"]
    if not hyps:
        return None
    if s.check(*[ind[n] for n in hyps]) != z3.unsat:
        return None
    raw = {str(pp)[4:] for pp in s.unsat_core()}
    return _mus(s, ind, [n for n in hyps if n in raw] or hyps, limits)


# ---------------------------------------------------------------------------


def _farkas_for(formulas, names, limits):
    """Multipliers that close this core by arithmetic alone, if it is linear.

    Returns (rows, multipliers, sorts) or None. Never raises: a core that
    cannot be turned into rows is the ordinary case, not a failure, and a
    missing LP backend must not cost anyone a proof they already had.
    """
    from .. import z3util
    from ..engines import farkas as fk

    rows = []
    try:
        for n in names:
            poly, rel = linarith.as_row(formulas[n])
            if rel == "=":
                # An equality's multiplier is free in sign and the LP wants it
                # non-negative, so it goes in as two inequalities -- the same
                # split `rows_of` makes.
                rows.append((n, poly, "<="))
                rows.append((n + "_rev", {m: -c for m, c in poly.items()},
                             "<="))
            else:
                rows.append((n, poly, rel))
    except (linarith.NotPolynomial, KeyError, AttributeError):
        return None
    if not rows:
        return None

    try:
        lams, _const, _strict, _exact = fk._search(rows, limits)
    except Exception:
        # No LP backend, or the search blew up. The core is still a core.
        return None
    if lams is None:
        return None

    sorts = {}
    for c in z3util.free_consts(*[formulas[n] for n in names]):
        try:
            sorts[str(c)] = z3util.sort_name(c)
        except ValueError:
            pass
    return rows, lams, sorts


def _with_farkas(cert, formulas, names, limits):
    """Attach the multipliers to a core certificate, if they can be found.

    Optional payload fields and a flip of `solver_free`: both are additive,
    which is what the frozen schema permits. A reader that does not know about
    them verifies the core exactly as before.
    """
    from .. import exact

    found = _farkas_for(formulas, names, limits)
    if found is None:
        return cert
    rows, lams, sorts = found
    cert.payload["rows"] = linarith.serialize_rows(rows)
    cert.payload["multipliers"] = exact.serialize_all(lams)
    cert.payload["sorts"] = sorts
    cert.solver_free = True
    return cert


def _drat_of_core(smt2, names, dropped, lim, citations=None):
    """The core, encoded by `boolenc` and refuted by the internal CDCL with a
    DRUP proof checked here: `(certificate, None)`, or `(None, why not)`."""
    from .. import boolenc, cdcl, drup
    from ..certificate import propositional_refutation_certificate

    fs = list(z3.parse_smt2_string(smt2))
    try:
        cnf = boolenc.encode(fs)
    except boolenc.NotPropositional as e:
        return None, str(e)
    r = cdcl.solve(cnf.nvars, [c[:] for c in cnf.clauses],
                   max_conflicts=lim.conflict_budget,
                   timeout_s=max(1.0, lim.timeout_ms / 1000))
    if r.status != "unsat" or not r.proof:
        return None, t("engine.prove.drat_unsolved", detail=r.detail or r.status)
    rep = drup.check(cnf.clauses, r.proof, timeout_s=max(1.0, lim.timeout_ms / 1000))
    if not rep.ok or not rep.derived_empty:
        return None, t("engine.prove.drat_bad", detail=rep.detail)
    return propositional_refutation_certificate(
        smt2, names, dropped, list(r.proof), cnf.nvars, len(cnf.clauses),
        citations=citations), None


def prove(spec, limits: Limits | None = None, drat: bool = False) -> Result:
    """Negate the claim and look for unsat. unsat => proved. With `drat`, a
    Boolean core comes back refuted by a DRUP proof over its own encoding,
    checkable without a solver (`propositional_refutation`)."""
    lim = limits or Limits()
    t0 = time.perf_counter()
    s, ind, formulas = _tracked(spec, negate_goal=True)
    lim.apply_to(s)
    all_names = list(formulas)
    r = s.check(*[ind[n] for n in all_names])
    st = _outcome(r, s)
    ms = (time.perf_counter() - t0) * 1000

    if st is Status.UNSAT:
        raw = _core_names(s.unsat_core(), ind)
        core = _mus(s, ind, [n for n in all_names if n in raw] or all_names, lim)
        dropped = [n for n in all_names if n not in core]
        clash = _vacuous(s, ind, all_names, lim)
        vacuous = clash is not None
        cert = _with_farkas(
            unsat_core_certificate(
                z3util.smt2(*[formulas[n] for n in core]), core, dropped,
                vacuous=vacuous, clash=clash,
                citations=_cited(spec, core),
            ), formulas, core, lim)
        used = [n for n in core if n != "__goal__"]
        # When the proof is vacuous that IS the headline; "proved using 2 of
        # 2 hypotheses" underneath it would read as reassurance.
        detail = (t("engine.prove.vacuous_core", names=", ".join(clash))
                  if vacuous
                  else t("engine.prove.proved", used=len(used),
                         total=len(spec.assumptions)))
        meta = {"hypotheses_used": used, "hypotheses_dropped": dropped,
                "vacuous": vacuous, "clash": clash}
        if drat:
            alt, why = _drat_of_core(z3util.smt2(*[formulas[n] for n in core]),
                                     core, dropped, lim, _cited(spec, core))
            if alt is not None:
                alt.payload["vacuous"] = bool(vacuous)
                alt.payload["clash"] = clash or []
                cert = alt
                meta["drat"] = {"proof_lines": len(alt.payload["proof"]),
                                "clauses": alt.payload["nclauses"]}
            else:
                # Not refused: the proof is still proved, with the core the
                # old way, and the reason the DRAT route did not apply is said.
                meta["drat_refused"] = why
        regimes = regime_report(spec, lim)
        if regimes:
            meta["regime_report"] = regimes
        return Result(
            "prove", st, Verdict.PROVED, ENGINE, ms, cert, detail=detail,
            meta=meta,
        )

    if st is Status.SAT:
        cert = _model_cert(spec, formulas, s.model(), all_names)
        # The values ARE the answer. They were in the certificate and nowhere
        # on screen, so refuting a claim meant opening a JSON file to find out
        # what refuted it.
        meta = {"counterexample": {k: v[1] for k, v
                                   in cert.payload["assignment"].items()}}
        hints = refutation_hints(spec, s.model())
        best = best_constant(spec, lim)
        if best is not None:
            # The constant that WOULD hold, computed and certified, in place
            # of the hint that names the command for it.
            meta["best_constant"] = best
            hints = [h for h in hints if "certo range" not in h]
            hints.insert(0, t("engine.prove.best_constant", var=best["variable"],
                              bound=best["bound"], interval=best["interval"]))
        if hints:
            meta["hints"] = hints
        return Result(
            "prove", st, Verdict.REFUTED, ENGINE, ms, cert,
            detail=t("engine.prove.refuted"), meta=meta,
        )

    return Result(
        "prove", st, Verdict.INCONCLUSIVE, ENGINE, ms, None,
        detail=t("engine.inconclusive", status=st.value,
                 reason=readable_reason(s.reason_unknown())),
    )


def _cited(spec, core) -> dict:
    """The sources of the cited hypotheses the core USED."""
    cites = getattr(spec, "citations", None) or {}
    return {n: cites[n] for n in core if n in cites}


def best_constant(spec, lim):
    """When a refuted claim bounds ONE variable by a constant and the
    hypotheses are linear: the best constant the hypotheses do give, from
    `range` -- the interval, the bound on the claimed side, and its
    certificate (`variable_range`) as data. None when it does not apply."""
    goal = getattr(spec, "goal", None)
    if goal is None or not z3.is_app(goal) or goal.num_args() != 2:
        return None
    if not (z3.is_le(goal) or z3.is_lt(goal) or z3.is_ge(goal) or z3.is_gt(goal)):
        return None
    a, b = goal.arg(0), goal.arg(1)

    def number(e):
        return z3.is_int_value(e) or z3.is_rational_value(e)

    def variable(e):
        return z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED

    if variable(a) and number(b):
        var, upper = a, z3.is_le(goal) or z3.is_lt(goal)
    elif number(a) and variable(b):
        var, upper = b, z3.is_ge(goal) or z3.is_gt(goal)
    else:
        return None
    from . import algebra

    try:
        res = algebra.variable_range(spec, str(var), lim)
    except Exception:  # noqa: BLE001 -- a hint is never worth a failure
        return None
    if res.certificate is None or res.meta.get("empty"):
        return None
    bound = res.meta.get("upper" if upper else "lower")
    if bound is None:
        return None
    return {"variable": str(var), "side": "upper" if upper else "lower",
            "bound": bound, "interval": res.meta.get("interval"),
            "certificate": res.certificate.to_dict()}


def refutation_hints(spec, model) -> list:
    """What a counterexample suggests about the SPEC, said next to it.

    Two readings a user had to make alone. A value like `nu = -1/2` for a
    quantity that is a count: the variables were declared real, the claim was
    weaker than meant, and the counterexample may be spurious. And a claim
    that bounds a quantity by a constant, refuted: the constant was wrong, and
    `range` finds the best one -- which existed, and was found late.
    """
    hints = []
    frac = []
    for d in model.decls():
        if d.arity() != 0 or d.range() != z3.RealSort():
            continue
        v = model[d]
        if z3.is_rational_value(v):
            if v.denominator_as_long() != 1:
                frac.append("{} = {}".format(d.name(), v.as_fraction()))
        elif z3.is_algebraic_value(v):
            frac.append("{} = {}".format(d.name(), v.approx(6)))
    if frac:
        hints.append(t("engine.prove.hint.nonintegral",
                       values=", ".join(sorted(frac)[:4])))
    goal = getattr(spec, "goal", None)
    if goal is not None and z3.is_app(goal) and goal.num_args() == 2 and (
            z3.is_le(goal) or z3.is_lt(goal) or z3.is_ge(goal) or z3.is_gt(goal)):
        a, b = goal.arg(0), goal.arg(1)

        def number(e):
            return z3.is_int_value(e) or z3.is_rational_value(e) \
                or z3.is_algebraic_value(e)

        def variable(e):
            return z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED

        side = b if number(a) else a if number(b) else None
        if side is not None:
            if variable(side):
                hints.append(t("engine.prove.hint.range_var", var=str(side)))
            else:
                hints.append(t("engine.prove.hint.range_expr",
                               expr=str(side)[:60]))
    return hints


def _constant_goal(goal):
    """Is the claim a boolean literal? Then `check` is not asking what you think.

    `claim(False)` makes `hypotheses AND claim` unsatisfiable however
    satisfiable the hypotheses are, and `claim(True)` makes it exactly the
    hypotheses. Both are legal and neither answers the question the shape of
    the spec suggests, so both are named.
    """
    if goal is None:
        return None
    if z3.is_false(goal):
        return "false"
    return "true" if z3.is_true(goal) else None


def check(spec, limits: Limits | None = None,
          hypotheses_only: bool = False, integers: bool = False,
          regime: str | None = None) -> Result:
    """Plain satisfiability of hypotheses plus claim.

    With `hypotheses_only`, the claim is dropped and the question becomes "is
    this regime non-empty?" -- which is what people were reaching for when
    they wrote `claim(False)` and got told, correctly and uselessly, that
    `hypotheses AND False` has no model.
    """
    lim = limits or Limits()
    t0 = time.perf_counter()
    if hypotheses_only:
        return _hypotheses_only(spec, lim, t0, integers=integers, regime=regime)
    s, ind, formulas = _tracked(spec, negate_goal=False)
    lim.apply_to(s)
    all_names = list(formulas)
    constant = _constant_goal(spec.goal)
    r = s.check(*[ind[n] for n in all_names])
    st = _outcome(r, s)
    ms = (time.perf_counter() - t0) * 1000

    if st is Status.SAT:
        cert = _model_cert(spec, formulas, s.model(), all_names)
        meta = dict(_constant_meta(constant))
        meta["counterexample"] = {k: v[1] for k, v
                                  in cert.payload["assignment"].items()}
        return Result("check", st, Verdict.SATISFIABLE, ENGINE, ms, cert,
                      detail=t("engine.check.sat"), meta=meta)
    if st is Status.UNSAT:
        raw = _core_names(s.unsat_core(), ind)
        core = _mus(s, ind, [n for n in all_names if n in raw] or all_names, lim)
        cert = _with_farkas(
            unsat_core_certificate(
                z3util.smt2(*[formulas[n] for n in core]), core,
                [n for n in all_names if n not in core],
            ), formulas, core, lim)
        return Result("check", st, Verdict.UNSATISFIABLE, ENGINE, ms, cert,
                      detail=t("engine.check.unsat_constant")
                      if constant == "false" else t("engine.check.unsat"),
                      meta=_constant_meta(constant))
    return Result("check", st, Verdict.INCONCLUSIVE, ENGINE, ms, None,
                  detail=t("engine.inconclusive", status=st.value,
                           reason=readable_reason(s.reason_unknown())),
                  meta=_constant_meta(constant))


def _constant_meta(constant):
    return {} if constant is None else {"constant_goal": constant}


def as_integers(formulas, names=None):
    """REAL constants read as integers -- every one, or those in `names`: `x`
    becomes `ToReal(x)` with an integer `x` of the same name. The formulas
    keep their arithmetic; only the domain shrinks, which is the question a
    count asks."""
    reals = [c for c in z3util.free_consts(*formulas)
             if c.sort() == z3.RealSort()
             and (names in (None, True) or str(c) in names)]
    subs = [(c, z3.ToReal(z3.Int(str(c)))) for c in reals]
    if not subs:
        return list(formulas)
    return [z3.substitute(f, *subs) for f in formulas]


def regime_report(spec, lim) -> list:
    """For each declared regime: are the hypotheses inhabited THERE?

    `[{"regime", "integers", "status": inhabited|EMPTY|unknown, "witness"}]`.
    One satisfiability call each, under the same limits. An EMPTY regime is
    the finding that matters: the theorem is vacuous where it was meant.
    """
    out = []
    for name, expr, integers in getattr(spec, "regimes", None) or []:
        fs = [f for _n, f in spec.assumptions] + [expr]
        if integers:
            fs = as_integers(fs, integers)
        s = z3.Solver()
        lim.apply_to(s)
        s.add(*fs)
        r = s.check()
        row = {"regime": name, "integers": integers,
               "status": ("inhabited" if r == z3.sat
                          else "EMPTY" if r == z3.unsat else "unknown")}
        if r == z3.sat:
            m = s.model()
            row["witness"] = {str(d.name()): str(m[d]) for d in m.decls()
                              if d.arity() == 0}
        out.append(row)
    return out


def _hypotheses_only(spec, lim, t0, integers=False, regime=None) -> Result:
    """Is this regime non-empty? The question, asked directly.

    Satisfiable gives a MODEL: the parameter set exhibited rather than argued.
    Unsatisfiable gives the MINIMAL clash rather than the whole hypothesis
    set, because "which of these do I have to give up" is what anyone asks
    next.
    """
    import copy

    bare = copy.copy(spec)
    bare.goal = None
    # THE REGIMES JOIN THE QUESTION, by name: "is the regime that matters
    # non-empty" is the one this flag exists for, and a clash then names the
    # regime condition it involves.
    # ONE REGIME JOINS THE QUESTION, by name, when asked for: regimes are
    # alternatives (`l >= 6`, `l >= 7`), not one conjunction. A clash then
    # names the regime condition it involves. Every declared regime is also
    # reported on its own below.
    declared = {n: (e, i) for n, e, i in (getattr(spec, "regimes", None) or [])}
    bare.assumptions = list(spec.assumptions)
    if regime is not None:
        if regime not in declared:
            raise ValueError(t("engine.check.no_regime", name=regime,
                               known=", ".join(declared) or "-"))
        bare.assumptions.append(("regime:" + regime, declared[regime][0]))
        integers = integers or declared[regime][1]
    if integers:
        names_ = [n for n, _ in bare.assumptions]
        bare.assumptions = list(zip(names_, as_integers(
            [f for _, f in bare.assumptions], integers)))
    s, ind, formulas = _tracked(bare, negate_goal=False)
    lim.apply_to(s)
    names = [n for n in formulas if n != "__goal__"]
    if not names:
        ms = (time.perf_counter() - t0) * 1000
        return Result("check", Status.SAT, Verdict.SATISFIABLE, ENGINE, ms,
                      None, detail=t("engine.check.no_hypotheses"))

    r = s.check(*[ind[n] for n in names])
    st = _outcome(r, s)
    ms = (time.perf_counter() - t0) * 1000

    if st is Status.SAT:
        cert = _model_cert(bare, formulas, s.model(), names)
        return Result("check", st, Verdict.SATISFIABLE, ENGINE, ms, cert,
                      detail=t("engine.check.regime_nonempty", n=len(names))
                      + (" " + t("engine.check.over_integers") if integers else ""),
                      meta={"hypotheses_only": True, "integers": integers,
                            "regime_report": regime_report(spec, lim),
                            "counterexample": {
                                k: v[1] for k, v
                                in cert.payload["assignment"].items()}})
    if st is Status.UNSAT:
        raw = {str(pp)[4:] for pp in s.unsat_core()}
        clash = _mus(s, ind, [n for n in names if n in raw] or names, lim)
        cert = _with_farkas(
            unsat_core_certificate(
                z3util.smt2(*[formulas[n] for n in clash]), clash,
                [n for n in names if n not in clash],
                vacuous=True, clash=clash,
            ), formulas, clash, lim)
        return Result("check", st, Verdict.UNSATISFIABLE, ENGINE, ms, cert,
                      detail=t("engine.check.regime_empty",
                               names=", ".join(clash)),
                      meta={"hypotheses_only": True, "clash": clash})
    return Result("check", st, Verdict.INCONCLUSIVE, ENGINE, ms, None,
                  detail=t("engine.inconclusive", status=st.value,
                           reason=readable_reason(s.reason_unknown())),
                  meta={"hypotheses_only": True})


def audit(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    """Drop each hypothesis in turn and hunt a counterexample to what remains."""
    from ..audit import NotAuditable, audit as run
    from ..audit import DOMAIN, NEEDED, REDUNDANT, UNKNOWN
    from ..certificate import hypothesis_audit_certificate
    from .. import z3util

    t0 = time.perf_counter()
    try:
        out = run(spec, limits)
    except NotAuditable as e:
        return Result("audit", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE, 0.0, None, detail=str(e))

    ms = (time.perf_counter() - t0) * 1000
    cert = hypothesis_audit_certificate(
        rows=out["rows"], counts=out["counts"],
        goal_smt2=z3util.smt2(spec.goal),
        hypotheses_smt2={n: z3util.smt2(f) for n, f in spec.assumptions},
        obligations=out["obligations"],
        title=spec.title,
    ).stamp(spec_path or None)

    c = out["counts"]
    if out["redundant"] and c[DOMAIN]:
        detail = t("engine.audit.both", n=len(out["redundant"]),
                   names=", ".join(out["redundant"][:4]),
                   d=c[DOMAIN], dnames=", ".join(out["domain"][:4]),
                   needed=c[NEEDED])
    elif out["redundant"]:
        detail = t("engine.audit.redundant", n=len(out["redundant"]),
                   names=", ".join(out["redundant"][:4]),
                   needed=c[NEEDED])
    elif c[DOMAIN]:
        detail = t("engine.audit.domain", n=c[DOMAIN],
                   names=", ".join(out["domain"][:4]), needed=c[NEEDED])
    elif c[UNKNOWN]:
        detail = t("engine.audit.unknown", n=c[UNKNOWN], needed=c[NEEDED])
    else:
        detail = t("engine.audit.all_needed", n=c[NEEDED])
    return Result("audit", Status.SAT, Verdict.SATISFIABLE, ENGINE, ms, cert,
                  detail=detail,
                  meta={"needed": c[NEEDED], "redundant": c[REDUNDANT],
                        "domain": c[DOMAIN], "unknown": c[UNKNOWN],
                        "redundant_names": out["redundant"],
                        "domain_names": out["domain"],
                        "obligations": out["obligations"]})


def core(spec, limits: Limits | None = None) -> Result:
    """MUS: which hypotheses are actually needed. This is "simplify"."""
    res = prove(spec, limits)
    res.command = "core"
    if res.status is Status.UNSAT and res.certificate is not None:
        used = res.meta.get("hypotheses_used", [])
        drop = [n for n in res.meta.get("hypotheses_dropped", []) if n != "__goal__"]
        none = t("engine.core.none")
        res.detail = t("engine.core.summary",
                       used=", ".join(used) or none,
                       dropped=", ".join(drop) or none)
    return res


def core_matrix(spec, limits: Limits | None = None) -> Result:
    """Which hypotheses each goal actually needs, side by side.

    Running `core` once per goal already gives the columns; what the table
    adds is the comparison. A hypothesis needed by one goal and not another is
    exactly what decides how small a downstream interface can be, and it is
    invisible when the goals are looked at one at a time.
    """
    lim = limits or Limits()
    t0 = time.perf_counter()

    columns, subcerts, inconclusive = {}, {}, []
    for goal in spec.goal_names:
        res = prove(spec.single(goal), lim)
        if res.status is not Status.UNSAT:
            inconclusive.append((goal, res.status.value, res.detail))
            columns[goal] = None
            continue
        columns[goal] = set(res.meta.get("hypotheses_used", []))
        if res.certificate is not None:
            subcerts[goal] = res.certificate.to_dict()

    table = {h: {g: (None if columns[g] is None else h in columns[g])
                 for g in spec.goal_names}
             for h in spec.names}
    never = [h for h in spec.names
             if all(v is False for v in table[h].values())]

    ms = (time.perf_counter() - t0) * 1000
    cert = core_matrix_certificate(
        hypotheses=spec.names, goals=spec.goal_names, table=table,
        subcerts=subcerts, inconclusive=inconclusive)

    if all(columns[g] is None for g in spec.goal_names):
        return Result("core", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      ENGINE, ms, cert,
                      detail=t("engine.core.matrix_none", n=len(spec.goals)),
                      meta={"table": table, "inconclusive": inconclusive})

    return Result(
        "core", Status.UNSAT, Verdict.PROVED, ENGINE, ms, cert,
        detail=t("engine.core.matrix", goals=len(spec.goals),
                 hyps=len(spec.names),
                 unused=", ".join(never) or t("engine.core.none")),
        meta={"table": table, "never_used": never, "inconclusive": inconclusive},
    )
