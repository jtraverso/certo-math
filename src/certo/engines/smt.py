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


def prove(spec, limits: Limits | None = None) -> Result:
    """Negate the claim and look for unsat. unsat => proved."""
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
            ), formulas, core, lim)
        used = [n for n in core if n != "__goal__"]
        # When the proof is vacuous that IS the headline; "proved using 2 of
        # 2 hypotheses" underneath it would read as reassurance.
        detail = (t("engine.prove.vacuous_core", names=", ".join(clash))
                  if vacuous
                  else t("engine.prove.proved", used=len(used),
                         total=len(spec.assumptions)))
        return Result(
            "prove", st, Verdict.PROVED, ENGINE, ms, cert, detail=detail,
            meta={"hypotheses_used": used, "hypotheses_dropped": dropped,
                  "vacuous": vacuous, "clash": clash},
        )

    if st is Status.SAT:
        cert = _model_cert(spec, formulas, s.model(), all_names)
        # The values ARE the answer. They were in the certificate and nowhere
        # on screen, so refuting a claim meant opening a JSON file to find out
        # what refuted it.
        return Result(
            "prove", st, Verdict.REFUTED, ENGINE, ms, cert,
            detail=t("engine.prove.refuted"),
            meta={"counterexample": {k: v[1] for k, v
                                     in cert.payload["assignment"].items()}},
        )

    return Result(
        "prove", st, Verdict.INCONCLUSIVE, ENGINE, ms, None,
        detail=t("engine.inconclusive", status=st.value,
                 reason=readable_reason(s.reason_unknown())),
    )


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
          hypotheses_only: bool = False) -> Result:
    """Plain satisfiability of hypotheses plus claim.

    With `hypotheses_only`, the claim is dropped and the question becomes "is
    this regime non-empty?" -- which is what people were reaching for when
    they wrote `claim(False)` and got told, correctly and uselessly, that
    `hypotheses AND False` has no model.
    """
    lim = limits or Limits()
    t0 = time.perf_counter()
    if hypotheses_only:
        return _hypotheses_only(spec, lim, t0)
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


def _hypotheses_only(spec, lim, t0) -> Result:
    """Is this regime non-empty? The question, asked directly.

    Satisfiable gives a MODEL: the parameter set exhibited rather than argued.
    Unsatisfiable gives the MINIMAL clash rather than the whole hypothesis
    set, because "which of these do I have to give up" is what anyone asks
    next.
    """
    import copy

    bare = copy.copy(spec)
    bare.goal = None
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
                      detail=t("engine.check.regime_nonempty", n=len(names)),
                      meta={"hypotheses_only": True,
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
