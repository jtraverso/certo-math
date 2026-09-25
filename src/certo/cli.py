"""Command-line interface."""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

from . import __version__
from .certificate import Certificate
from .certificate import verify as verify_cert
from .i18n import available, set_lang, t
from .limits import Limits
from .status import Result, Status, Verdict

# Some consoles (Windows in particular) default to a legacy codepage that
# mangles accented output. Translations should not depend on that.
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):  # pragma: no cover
        pass

# The scope of a result matters as much as the result. A bare "PROVED"
# invites reading a bounded synthesis as a theorem, so commands whose scope
# is narrower than the word suggests get their own banner.
SCOPED = {
    ("synth", Verdict.PROVED), ("synth", Verdict.UNSATISFIABLE),
    ("prove", Verdict.PROVED), ("core", Verdict.PROVED),
    ("sweep", Verdict.PROVED), ("cases", Verdict.PROVED),
    ("bisect", Verdict.PROVED),
}
SCOPE_NOTE = {("synth", Verdict.PROVED), ("sweep", Verdict.PROVED)}


def banner(res: Result) -> str:
    # A sweep's banner depends on what it established about the PREDICATE, not
    # only on its verdict, so the engine picks the key.
    key = res.meta.get("banner_key")
    if key and (res.command, res.verdict) in SCOPED:
        return t(key)
    if (res.command, res.verdict) in SCOPED:
        return t("scope.{}.{}".format(res.command, res.verdict.value))
    return t("verdict." + res.verdict.value)


def scope_note(res: Result):
    if (res.command, res.verdict) in SCOPE_NOTE:
        return t("note.{}.{}".format(res.command, res.verdict.value))
    return None


# ---------------------------------------------------------------------------
# salida
# ---------------------------------------------------------------------------


_HIDDEN_META = ("trace", "errors", "describe", "counterexamples", "solution",
                "errors_detail", "inconclusive_detail", "implementation",
                "domain", "evaluations", "calibration", "table", "multipliers",
                "counterexample", "hint", "lemmas", "used", "unused", "bridges", "lo", "hi",
                "width", "ladder", "lo_float", "hi_float", "vacuous",
                "banner_key", "level", "orbits", "spot_checks",
                "by_orbit", "evaluated", "inferred", "cofactors", "squares",
                "achieved", "conditional", "discrete_gain", "selected",
                "skeleton_from", "nodes", "by_bound", "infeasible",
                "leaves", "closed", "integral_level", "tight",
                "mu", "nu", "gap", "leading", "case", "resultant", "floor", "bound", "missed", "doubled", "case",
                # both are already said in the detail line, and once loudly
                "constant_goal", "hypotheses_only", "clash")


def _item_id(entry) -> str:
    """An entry's id, reading the pre-rename `g6` field too."""
    return entry.get("id") or entry.get("g6") or "?"


def print_calibration(cal, worst_k=3):
    """Refuting says it is false; calibrating says how much, and where."""
    if not cal:
        return
    print("  " + t("cli.calibration", count=cal["count"], min=cal["min"],
                   max=cal["max"], mean=cal["mean"]))
    worst = cal["worst"][:worst_k]
    if worst:
        label = t("cli.label.lowest" if cal["worst_sense"] == "min"
                  else "cli.label.highest")
        print("  " + t("cli.calibration.worst", k=worst_k, label=label,
                       items=" | ".join("{} {}".format(_item_id(v), v["value"])
                                        for v in worst)))


def _as_json(res, args) -> dict:
    """The result as JSON, whole or summarised.

    `--cert-all --json` on a nested sweep puts megabytes on stdout: a range
    over three sizes and thirty-four graphs is already 94 KB, and every
    per-item certificate is in there. A reader piping that into `jq` to see a
    verdict has paid for a proof they did not ask to read.

    `--brief` replaces the certificate with what identifies it -- kind,
    digest, whether it is solver-free, and how big the thing it stands for is
    -- and changes nothing else. The certificate itself still goes to `--cert`
    if it was asked for, because a summary is for reading and the artefact is
    for keeping.
    """
    out = res.to_dict()
    if not getattr(args, "brief", False) or not out.get("certificate"):
        return out
    cert = res.certificate
    out["certificate"] = {
        "kind": cert.kind,
        "digest": cert.digest(),
        "solver_free": bool(cert.solver_free),
        "bytes": len(json.dumps(cert.to_dict(), ensure_ascii=False)),
        "summarised": True,
    }
    return out


def emit(res: Result, args) -> int:
    # Provenance: tie the certificate to the spec and version that made it.
    if res.certificate is not None:
        res.certificate.stamp(getattr(args, "spec", None))

    if getattr(args, "json", False):
        print(json.dumps(_as_json(res, args), indent=2, ensure_ascii=False))
    else:
        print("{}  [{}]".format(banner(res), res.status.value))
        if res.detail:
            print("  " + res.detail)

        impl = res.meta.get("implementation")
        if impl:
            print("  " + t("cli.synthesised_object"))
            for k, v in impl.items():
                print("    {} = {}".format(k, v))
        if res.meta.get("domain"):
            print("  " + t("cli.domain", domain=res.meta["domain"]))

        # A refutation without its values is half an answer: the point of a
        # counterexample is the counterexample.
        ce = res.meta.get("counterexample")
        if ce:
            print("  " + t("cli.counterexample" if res.verdict is Verdict.REFUTED
                           else "cli.witness"))
            for k, v in sorted(ce.items()):
                print("    {} = {}".format(k, v))

        for k, v in sorted(res.meta.items()):
            if k in _HIDDEN_META:
                continue
            print("  {}: {}".format(k, v))

        if res.meta.get("level") and res.meta["level"] != "certified":
            print("  !! " + t("cli.sweep.level." + res.meta["level"],
                              n=res.meta.get("predicate_uncertified", 0),
                              total=res.meta.get("evaluations", 0)))

        if res.meta.get("vacuous"):
            print("  !! " + t("cli.vacuous"))

        note = scope_note(res)
        if getattr(args, "prove_candidate", False):
            note = None   # the universal step follows immediately
        if note:
            print("  " + note)

        if res.certificate is not None:
            c = res.certificate
            tag = t("cli.cert.solver_free" if c.solver_free
                    else "cli.cert.needs_solver")
            print("  " + t("cli.certificate", kind=c.kind, tag=tag,
                           digest=c.digest()))
        else:
            print("  " + t("cli.certificate.none"))
        print("  " + t("cli.engine", engine=res.engine, ms=res.elapsed_ms))

    # Self-verification. A certificate that fails its own checker is a bug in
    # certo, never a result, and saying so here is the difference between
    # finding that out now and finding it out in somebody's audit.
    selfcheck = _self_check(res, args)

    out = getattr(args, "cert", None)
    if out and res.certificate is not None:
        Path(out).write_text(res.certificate.to_json(), encoding="utf-8")
        if not getattr(args, "json", False):
            print("  " + t("cli.cert.written", path=out))

    log = getattr(args, "log", None)
    if log:
        from . import ledger

        path = log if isinstance(log, str) and log != "-" else ledger.default_path()
        ledger.append(path, res, cert_path=out, spec_path=getattr(args, "spec", None),
                      note=getattr(args, "note", "") or "",
                      tags=getattr(args, "tag", None))
        if not getattr(args, "json", False):
            print("  " + t("cli.ledger.logged", path=path))

    # A question certo could not settle is the raw material of a coverage
    # map, and nothing was keeping it. Silent by design after the first time,
    # never fatal, and `CERTO_NO_COVERAGE=1` turns it off.
    from . import coverage

    if coverage.record(res, "cli") and not getattr(args, "json", False):
        _announce_coverage()

    if selfcheck is False:
        return 1
    return 0 if res.status.conclusive else 2


def _announce_coverage() -> None:
    """Say it once, the first time, and never again.

    A tool whose whole argument is that it does not claim more than it knows
    does not get to start writing files without mentioning it. A marker beside
    the log is how "the first time" survives between processes.
    """
    from . import coverage

    try:
        marker = coverage.default_path().with_suffix(".announced")
        if marker.exists():
            return
        marker.parent.mkdir(parents=True, exist_ok=True)
        marker.write_text("", encoding="utf-8")
        print("  " + t("cli.coverage.first",
                       path=str(coverage.default_path()),
                       off=coverage.ENV_OFF))
    except Exception:  # noqa: BLE001
        pass


def _self_check(res, args):
    """Run the real verifier over what we just produced. None = not run.

    Solver-free certificates are checked by default because the check is
    arithmetic; anything else is opt-in, since re-running a search on every
    invocation is a cost nobody asked for.
    """
    cert = res.certificate
    if cert is None:
        return None
    want = getattr(args, "self_check", None)
    if want is False:
        return None
    if want is None and not cert.solver_free:
        return None

    rep = verify_cert(cert, limits_from(args))
    res.meta["self_check"] = "ok" if rep.ok else "FAILED"
    if rep.ok:
        return True

    # Loud, and on stderr: this is certo failing, not the user's spec.
    print(t("cli.selfcheck.failed", kind=cert.kind), file=sys.stderr)
    for name, ok, detail in rep.checks:
        if not ok:
            print("    [XX] {}{}".format(
                name, "  ({})".format(detail) if detail else ""),
                file=sys.stderr)
    print(t("cli.selfcheck.report"), file=sys.stderr)

    # The one case where certo KNOWS the bug is its own. Write the report
    # without being asked -- locally, never sent -- and say where it is.
    from . import report as _report

    where = _report.capture_selfcheck(res, args)
    if where:
        print(t("cli.report.captured", path=where), file=sys.stderr)
    return False


def limits_from(args) -> Limits:
    return Limits(
        timeout_ms=args.timeout_ms,
        rlimit=args.rlimit,
        max_memory_mb=args.max_memory_mb,
        seed=args.seed,
        max_iterations=getattr(args, "max_iterations", 10_000),
        conflict_budget=getattr(args, "conflict_budget", 1_000_000),
        enumerate_timeout_s=getattr(args, "enumerate_timeout_s", 120),
        max_output_mb=getattr(args, "max_output_mb", 64),
    )


# ---------------------------------------------------------------------------
# comandos
# ---------------------------------------------------------------------------


#: The question people arrive with, and the command that answers it. Keyed on
#: the QUESTION because that is what somebody has when they are stuck: a
#: person who needs `order` is thinking "does this decay", not "order".
from .routing import BY_QUESTION  # noqa: E402  (the table moved)


def cmd_reduce(args):
    """One program, or a whole family -- the spec says which.

    `--parametric` does not switch a mode, it ASSERTS one: a user who came for
    the symbolic quotient and silently got the single-instance answer would
    have a weaker result than they think, which is the one failure mode worth
    a flag.
    """
    from .engines import algebra
    from .spec import ParametricSymmetrySpec, SymmetrySpec, load_spec

    spec = load_spec(args.spec)
    parametric = isinstance(spec, ParametricSymmetrySpec)
    if getattr(args, "parametric", False) and not parametric:
        print(t("cli.reduce.not_parametric", got=type(spec).__name__))
        return 3
    if not parametric and not isinstance(spec, SymmetrySpec):
        print(t("spec.wrong_type", got=type(spec).__name__,
                want="SymmetrySpec or ParametricSymmetrySpec"))
        return 3

    run = algebra.reduce_parametric if parametric else algebra.reduce_symmetry
    res = run(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        if parametric:
            print("  " + t("verify.paramsym.scope",
                           n=len(res.certificate.payload["points"])))
        else:
            print("  " + t("verify.symmetry.scope"))
    return rc


def cmd_solve(args):
    from .engines import algebra
    from .spec import LinearSystemSpec, load_spec

    spec = load_spec(args.spec, LinearSystemSpec)
    res = algebra.linear_system(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        if p["solution"]:
            print("  x = " + ", ".join(p["solution"][:8])
                  + (" ..." if len(p["solution"]) > 8 else ""))
        for k in p["kernel"][:3]:
            print("  " + t("cli.solve.kernel",
                           values=", ".join(k[:8])))
        if p.get("witness"):
            print("  " + t("cli.solve.witness",
                           values=", ".join(p["witness"][:8])))
        print("  " + t("verify.solve.scope"))
    return rc


def cmd_quotient(args):
    from .engines import algebra
    from .spec import EquitableQuotientSpec, load_spec

    spec = load_spec(args.spec, EquitableQuotientSpec)
    res = algebra.equitable_quotient(spec, limits_from(args),
                                     spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        print("  " + t("verify.quotient.scope"))
        print("  " + t("verify.quotient.integrality"))
    return rc


def cmd_cone(args):
    from .engines import algebra
    from .spec import ConeSpec, load_spec

    spec = load_spec(args.spec, ConeSpec)
    res = algebra.toric_cone(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        if p["height_functional"]:
            print("  u = " + ", ".join(p["height_functional"]))
        for name, d in sorted(p["discrepancies"].items()):
            print("  {:<12} height {:<8} discrepancy {}".format(
                name, p["heights"][name], d))
        for name, entry in sorted((p.get("subdivision") or {}).items()):
            print("  {:<12} height {:<8} discrepancy {}   (subdivision)".format(
                name, entry.get("height", "?"), entry.get("discrepancy", "?")))
        print("  " + t("verify.toric.lattice", where=p["multiplicity_in"]))
        print("  " + t("verify.toric.scope"))
    return rc


def cmd_profile(args):
    from .engines import algebra
    from .spec import ProfileSpec, load_spec

    spec = load_spec(args.spec, ProfileSpec)
    res = algebra.capacity_profile(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        print("  f({}) on [{}, {}]".format(p["parameter"], p["domain"]["lo"],
                                           p["domain"]["hi"]))
        for piece in p["piecewise"]:
            print("    [{:>5}, {:>5}]   f(t) = {}".format(
                piece["from"], piece["to"], piece["value"]))
        from fractions import Fraction

        for at, e in sorted((p.get("sources") or {}).items(),
                            key=lambda kv: Fraction(kv[0])):
            print("    t = {:<6} attained {:<8} load {}".format(
                at, e["value"], e["parameter_load"]))
        print("  " + t("verify.profile.scope"))
    elif not args.json and res.certificate is None and res.meta.get("failures"):
        for f in res.meta["failures"]:
            print("    !! " + json.dumps(f, ensure_ascii=False))
    return rc


def cmd_report(args):
    """Run a command again, decide whose bug it is, and write it all down.

    Sends nothing. What it prints is where the folder is and a link that opens
    a pre-filled issue with only non-sensitive fields in it; what goes into
    the issue is the person's decision, made after reading the folder.
    """
    from . import report

    argv = list(args.argv or [])
    if argv and argv[0] == "--":
        argv = argv[1:]
    info = report.build(argv=argv or None, cert_path=args.certificate,
                        wrong=args.wrong, with_coverage=args.coverage,
                        out=args.out)
    if args.json:
        print(json.dumps(info, indent=2, ensure_ascii=False))
        return 0

    tri = info["triage"]
    print(t("cli.report.header", category=tri["category"]))
    for e in tri["evidence"]:
        print("    - [{}] {}".format(e["category"], e["detail"]))
    print()
    print("  " + t("cli.report.folder", path=info["folder"]))
    print("  " + t("cli.report.archive", path=info["archive"]))
    if info["spec_included"]:
        print("  " + t("cli.report.spec_warning"))
    if info["coverage_included"]:
        print("  " + t("cli.report.coverage_included"))
    print()
    if tri["category"] == "soundness":
        print("  " + t("cli.report.private", link=info["link"]))
    else:
        print("  " + t("cli.report.file_it", link=info["link"]))
    print("  " + t("cli.report.nothing_sent"))
    return 0


def cmd_columns(args):
    from .engines import algebra
    from .spec import CliqueLPSpec, load_spec

    spec = load_spec(args.spec, CliqueLPSpec)
    res = algebra.clique_lp(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        for col in p["columns"][:args.top]:
            print("  {:<10} {}".format(col["x"], "{" + ", ".join(col["clique"]) + "}"))
        if len(p["columns"]) > args.top:
            print("  " + t("cli.solution.more", n=len(p["columns"]) - args.top))
        print("  " + t("cli.colgen.pricing", nodes=p["pricing"]["nodes"],
                       value=p["pricing"]["max_reduced"] or "-"))
    return rc


def cmd_semigroup(args):
    from .engines import algebra
    from .spec import SemigroupSpec, load_spec

    spec = load_spec(args.spec, SemigroupSpec)
    res = algebra.affine_semigroup(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        if p.get("grading"):
            print("  u = " + ", ".join(p["grading"])
                  + "   (" + t("verify.semigroup.grading") + ")")
        for name in p["order"]:
            deg = (p.get("degrees") or {}).get(name, "?")
            mark = "  redundant" if name in (p.get("redundant") or {}) else ""
            print("  {:<12} {:<18} degree {}{}".format(
                name, str(tuple(p["generators"][name])), deg, mark))
        for name, e in sorted((p.get("points") or {}).items()):
            print("  {:<12} {:<18} cone {:<6} group {:<6} semigroup {}".format(
                name, str(tuple(e["point"])), _say(e["in_cone"]),
                _say(e["in_group"]), _say(e["in_semigroup"])))
            if e.get("refutes_normality"):
                print("               " + t("cli.semigroup.witness", name=name))
        hb = p.get("hilbert")
        if hb is not None:
            print("  " + t("cli.semigroup.hilbert") + ": "
                  + _say(hb["is_minimal_generating_set"]))
            for name, e in sorted((hb.get("elements") or {}).items()):
                extra = ""
                if e.get("reduces_as"):
                    extra = "  = {} + {}".format(
                        p["order"][e["reduces_as"]["generator"]],
                        tuple(e["reduces_as"]["rest"]))
                print("    {:<12} {:<18} in S {:<10} irreducible {}{}".format(
                    name, str(tuple(e["element"])), _say(e.get("in_semigroup")),
                    _say(e.get("irreducible")), extra))
            if hb.get("unreachable_generators"):
                print("    " + t("cli.semigroup.unreachable",
                                 names=", ".join(hb["unreachable_generators"])))
        print("  " + t("verify.semigroup.scope"))
    return rc


def _say(v) -> str:
    """yes / no / unknown -- and unknown is never printed as no."""
    return t("cli.yes") if v is True else (
        t("cli.no") if v is False else t("cli.unknown"))


def cmd_range(args):
    from .engines import algebra
    from .spec import Spec, load_spec

    spec = load_spec(args.spec, Spec)
    res = algebra.variable_range(spec, args.var, limits_from(args),
                                 spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        for side, arrow in (("upper", "<="), ("lower", ">=")):
            end = p[side]
            if end["bound"] is None:
                continue
            print("  {} {} {}{}".format(
                p["variable"], arrow, end["bound"],
                "   (open: a strict row is binding)" if end["strict"] else ""))
            print("    " + ", ".join(
                "{} x {}".format(k, v)
                for k, v in sorted(end["multipliers"].items())))
        if p["empty"]:
            print("  " + t("engine.varrange.ask_check"))
    return rc


def cmd_cycle(args):
    from .engines import algebra
    from .spec import CycleSpec, load_spec

    spec = load_spec(args.spec, CycleSpec)
    res = algebra.dependency_cycle(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        for step in p["steps"]:
            print("  {:<10} {} {:<6}{:<10} -> {}".format(
                step["from"], step["rel"], step["fn"],
                "" if step["fn"] != "poly" else "^" + step["degree"],
                _cls(step["class"])))
        c = p["closes"]
        print("  closes: {} ({}) {} {} ({})".format(
            c["left"], _cls(c["left_class"]), c["rel"],
            c["right"], _cls(c["right_class"])))
    return rc


def _cls(d):
    return ("u^" + d["exponent"] if d["tier"] == "poly"
            else "{}(u)^{}".format(d["tier"], d["exponent"]))


def cmd_bind(args):
    from .engines import algebra
    from .spec import BindSpec, load_spec

    spec = load_spec(args.spec, BindSpec)
    res = algebra.lean_binding(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        p = res.certificate.payload
        print("  {} -> {}".format(p["certificate"], p["declaration"] or "-"))
        print("  discharges: {}".format(p["discharges"]))
        if p["spec"].get("stale"):
            print("  " + t("verify.bind.stale", path=p["spec"]["path"]))
    return rc


def cmd_matrix(args):
    from .engines import algebra
    from .spec import MatrixSpec, load_spec

    spec = load_spec(args.spec, MatrixSpec)
    res = algebra.integer_matrix(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        print("  " + t("verify.inertia.scope"
                       if res.certificate.kind == "symmetric_inertia"
                       else "verify.lattice.scope"))
    return rc


def cmd_audit(args):
    from .engines import smt
    from .spec import Spec, load_spec

    spec = load_spec(args.spec, Spec)
    res = smt.audit(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        for row in res.certificate.payload["rows"]:
            mark = {"needed": "[needed]", "redundant": "[REDUNDANT]",
                    "domain": "[DOMAIN]",
                    "unknown": "[unknown]"}[row["verdict"]]
            line = "  {:<12} {}".format(mark, row["hypothesis"])
            if row["verdict"] == "needed":
                w = row["witness"] or {}
                line += "   " + t("cli.audit.witness", values=", ".join(
                    "{}={}".format(k, v[1]) for k, v in sorted(w.items())[:5]))
            elif row["verdict"] == "domain":
                line += "   " + t("cli.audit.obligation", values=", ".join(
                    row.get("obligations") or []))
            print(line)
        duties = res.certificate.payload.get("obligations")
        if duties:
            print("  " + t("cli.audit.guarded", n=len(duties),
                           values=", ".join(duties[:5])))
        print("  " + t("verify.audit.not_minimal"))
    return rc


def cmd_ask(args):
    """One entry point: load the spec, and let its type pick the command.

    The friction was never the routing, it was having to know the routing. A
    spec already says what kind of question it is; this reads that and runs
    the command that answers it, printing WHICH one it chose so the answer
    stays traceable to a command somebody can run directly.
    """
    from .routing import runner_for
    from .spec import load_spec

    spec = load_spec(args.spec)
    command, fn = runner_for(spec)
    if command is None:
        print(t("cli.ask.unknown", got=type(spec).__name__))
        return 2
    if fn is None:
        print(t("cli.ask.needs_flags", command=command,
                got=type(spec).__name__))
        return 2
    if not args.json:
        print(t("cli.ask.routed", command=command, got=type(spec).__name__))
    # Not every engine takes a spec path; the ones that do use it to stamp
    # provenance, and passing it where it is not accepted would turn a routing
    # convenience into an error the user did not cause.
    import inspect

    from .routing import prepared

    ready = prepared(spec)
    if "spec_path" in inspect.signature(fn).parameters:
        res = fn(ready, limits_from(args), spec_path=args.spec)
    else:
        res = fn(ready, limits_from(args))
    return emit(res, args)


def cmd_commands(args):
    """Which command answers which question, in the terminal."""
    name = getattr(args, "name", None)
    if name:
        from .catalogue import rows

        row = next((r for r in rows() if r["command"] == name
                    or name in (r["aliases"] or [])), None)
        if row is None:
            print(t("cli.commands.no_such", name=name,
                    known=", ".join(sorted(r["command"] for r in rows()))[:200]),
                  file=sys.stderr)
            return 3
        if args.json:
            print(json.dumps(row, indent=2, ensure_ascii=False))
        else:
            for key in ("command", "aliases", "spec", "engine", "kind",
                        "tier"):
                value = row.get(key)
                print("  {:<12} {}".format(
                    key, ", ".join(value) if isinstance(value, list)
                    else ("-" if value is None else value)))
            if row.get("help"):
                print("  " + row["help"].strip().splitlines()[0])
        return 0

    if getattr(args, "table", False):
        # The one table the documents are checked against. A flag rather than
        # a command: the surface is the thing this project has to keep small,
        # and this is the same question asked for machines.
        from .catalogue import as_markdown, as_text, counts

        if args.json:
            from .catalogue import rows
            print(json.dumps({"counts": counts(), "rows": rows()}, indent=2,
                             ensure_ascii=False))
        elif args.markdown:
            from .i18n import DEFAULT_LANG
            print(as_markdown(getattr(args, "lang", None) or DEFAULT_LANG))
        else:
            print(as_text())
        return 0
    if args.json:
        print(json.dumps(
            [{"group": t(g), "rows": [{"question": t(q), "command": c}
                                      for q, c in rows]}
             for g, rows in BY_QUESTION], indent=2, ensure_ascii=False))
        return 0
    print(t("commands.header"))
    for group, rows in BY_QUESTION:
        print()
        print("  " + t(group))
        for question, command in rows:
            print("    {:<34} {}".format("certo " + command, t(question)))
    print()
    print("  " + t("commands.footer"))
    return 0


def cmd_prove(args):
    from .engines import smt
    from .spec import Spec, load_spec

    return emit(smt.prove(load_spec(args.spec, Spec), limits_from(args)), args)


def cmd_check(args):
    from .engines import smt
    from .spec import Spec, load_spec

    res = smt.check(load_spec(args.spec, Spec), limits_from(args),
                    hypotheses_only=args.hypotheses_only)
    rc = emit(res, args)
    # A constant claim makes `check` decide something other than what the
    # shape of the spec suggests, and the verdict alone cannot say so.
    if not args.json and res.meta.get("constant_goal"):
        print("  !! " + t("cli.check.constant." + res.meta["constant_goal"]))
    return rc


def cmd_core(args):
    from .engines import smt
    from .spec import MultiSpec, Spec, load_spec

    spec = load_spec(args.spec)
    if isinstance(spec, MultiSpec):
        res = smt.core_matrix(spec, limits_from(args))
        rc = emit(res, args)
        if not args.json:
            _print_matrix(res.meta.get("table"), spec.goal_names,
                          res.meta.get("never_used", []))
        return rc
    if not isinstance(spec, Spec):
        print("core needs a Spec or a MultiSpec; spec() returned "
              + type(spec).__name__, file=sys.stderr)
        return 1
    return emit(smt.core(spec, limits_from(args)), args)


def _print_matrix(table, goals, never):
    """The hypothesis-by-goal table. The comparison IS the result."""
    if not table:
        return
    cells = {True: "yes", False: "no", None: "?"}
    width = max([len(t("cli.matrix.header"))] + [len(h) for h in table])
    print("  {:<{w}}  {}".format(t("cli.matrix.header"), "  ".join(
        "{:>8}".format(g[:8]) for g in goals), w=width))
    for h, row in table.items():
        print("  {:<{w}}  {}".format(h, "  ".join(
            "{:>8}".format(cells[row[g]]) for g in goals), w=width))
    print("  " + t("cli.matrix.legend"))
    if never:
        print("  " + t("cli.matrix.never", names=", ".join(never)))


def cmd_farkas(args):
    from .engines import farkas
    from .spec import Spec, load_spec

    spec = load_spec(args.spec, Spec)
    res = farkas.farkas(spec, limits_from(args), nonlinear=args.nonlinear,
                        spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("multipliers"):
        print("  " + t("cli.farkas.multipliers"))
        for name, lam in res.meta["multipliers"].items():
            print("    {:<22} {}".format(name, lam))
        print("  " + t("cli.farkas.hint", hint=res.meta.get("hint", "")))
    return rc


def cmd_compose(args):
    from pathlib import Path

    from .engines import compose
    from .spec import ProofSpec, load_spec

    spec = load_spec(args.spec, ProofSpec)
    res = compose.compose(spec, limits_from(args), spec_path=args.spec,
                          base_dir=Path.cwd())
    rc = emit(res, args)
    if not args.json and res.meta.get("lemmas"):
        _print_lemmas(res)
    return rc


def _print_lemmas(res):
    """Which lemmas are linked, which are asserted, which are not needed.

    The distinction is the whole point: a linked lemma is checked against its
    own certificate, a bridge is a claim about what that certificate means.
    """
    bridges = set(res.meta.get("bridges", []))
    used = set(res.meta.get("used", []))
    print("  " + t("cli.compose.lemmas"))
    for name in res.meta["lemmas"]:
        mark = t("cli.compose.bridge") if name in bridges             else t("cli.compose.derived")
        print("    {:<24} {:<10} {}".format(
            name, mark, "*" if name in used else ""))
    if res.meta.get("unused"):
        print("  " + t("cli.compose.unused",
                       names=", ".join(res.meta["unused"])))


def cmd_bounds(args):
    from .engines import bounds
    from .spec import BoundSpec, load_spec

    spec = load_spec(args.spec, BoundSpec)
    if args.prec:
        spec.prec = args.prec
    if args.max_prec:
        spec.max_prec = args.max_prec
    res = bounds.bounds(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("lo"):
        print("  " + t("cli.bounds.enclosure", lo=res.meta["lo_float"],
                       hi=res.meta["hi_float"], width=res.meta["width"]))
        print("  " + t("cli.bounds.ladder",
                       ladder=", ".join(str(p) for p in res.meta["ladder"])))
    return rc


def _repair(args, doctor):
    """What an interrupted install left behind, and only then its removal.

    Preview is the default and `--apply` is a second decision, because what is
    being removed lives in site-packages: a wrong guess there breaks an
    environment rather than a file.
    """
    rep = doctor.repair(apply=args.apply)
    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 0 if not rep["failed"] else 1

    if rep["held_open"]:
        # The CAUSE, before the symptom: removing the leftovers while the
        # holder is running produces new ones on the next install.
        print("  !! " + t("cli.repair.held",
                          names=", ".join(rep["held_open"])))
    if not rep["leftovers"]:
        print("  " + t("cli.repair.clean"))
        return 0

    print("  " + t("cli.repair.found", n=len(rep["leftovers"])))
    for path in rep["leftovers"]:
        print("    " + path)
    if not rep["applied"]:
        print("  " + t("cli.repair.preview"))
        return 0
    if rep["removed"]:
        print("  " + t("cli.repair.removed", n=len(rep["removed"])))
    for bad in rep["failed"]:
        print("  [XX] " + t("cli.repair.failed", path=bad["path"],
                            why=bad["why"]))
    return 1 if rep["failed"] else 0


def cmd_doctor(args):
    """What this install can do, and what each gap actually costs."""
    from . import doctor

    if getattr(args, "repair", False):
        return _repair(args, doctor)

    rep = doctor.report()
    if args.json:
        rep["mcp"] = doctor.mcp_status()
        if args.register_mcp:
            rep["registration"] = doctor.register_mcp(getattr(args, "mcp_path", None))
        print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 0 if rep["ok"] else 3

    print("  " + t("doctor.header"))
    for r in rep["rows"]:
        mark = "[ok]" if r["ok"] else ("[XX]" if r["required"] else "[--]")
        print("  {:<12} {:<9} {}".format(r["key"], mark, r["what"]))
        # The detail on a FAILING row is the reason, and it was being dropped:
        # a probe that ran and came back with "no default toolchain" reported
        # exactly as one whose binary is not installed. A user told certo it
        # was wrong about their machine and they were right -- Lean was there,
        # with Mathlib built, and the one line that said why never printed.
        if r["detail"]:
            print("  {:<12} {:<9} {}".format("", "", r["detail"]))

    gaps = [r for r in rep["rows"] if not r["ok"] and not r["required"]]
    if gaps:
        print()
        print("  " + t("doctor.optional"))
        for r in gaps:
            print("    {:<12} {}".format(r["key"], r["without"]))

    if not rep["numerics"]:
        print()
        print("  !! " + t("doctor.numerics.none"))

    print()
    print("  " + t("doctor.mcp.header"))
    m = doctor.mcp_status()
    print("    " + t("doctor.mcp.workspace", path=m["workspace"]))
    if args.register_mcp:
        reg = doctor.register_mcp(getattr(args, "mcp_path", None))
        if not reg["written"]:
            print("    !! " + reg["detail"])
        elif reg["already"]:
            print("    " + t("doctor.mcp.already"))
        else:
            print("    " + t("doctor.mcp.registered", path=reg["path"],
                             servers=", ".join(reg["servers"])))
    elif not m["config_present"]:
        print("    " + t("doctor.mcp.not_registered"))
    print("    " + (t("doctor.mcp.starts") if m["starts"]
                    else t("doctor.mcp.fails", detail=m["detail"])))

    print()
    cov = rep.get("coverage") or {}
    print("  " + t("doctor.coverage.title"))
    from . import coverage as _cov

    if not cov.get("enabled", True):
        print("    " + t("doctor.coverage.off", off=_cov.ENV_OFF))
    elif cov.get("full"):
        print("    " + t("doctor.coverage.full", lines=cov.get("lines", 0),
                         path=cov.get("path", "")))
    elif cov.get("lines"):
        print("    " + t("doctor.coverage.some", lines=cov["lines"],
                         first=(cov.get("first") or "")[:10],
                         path=cov.get("path", "")))
    else:
        print("    " + t("doctor.coverage.none", path=cov.get("path", "")))

    print()
    print("  " + (t("doctor.all_required") if rep["ok"]
                  else t("doctor.required_missing", n=rep["missing_required"])))
    return 0 if rep["ok"] else 3


def cmd_induct(args):
    from .engines import induct
    from .spec import InductSpec, load_spec

    spec = load_spec(args.spec, InductSpec)
    res = induct.induct(spec, limits_from(args), spec_path=args.spec)
    return emit(res, args)


def _shrink_orbits(spec, sweep_res, args):
    """Minimise one representative per orbit. The end of the structural story.

    Running `shrink` by hand from each representative is the same work; what
    this removes is lining up three artefacts afterwards and hoping they came
    from the same run -- which is exactly what the certificate then records.
    """
    from .certificate import orbit_witnesses_certificate
    from .engines import shrink

    rows = sweep_res.meta.get("orbits") or []
    by_id = {spec.id_of(i): i for i in spec.enumerate()}
    witnesses = []
    for row in rows:
        start = by_id.get(row["representative"])
        if start is None:
            continue
        r = shrink.shrink_domain(spec, start, limits_from(args),
                                 spec_path=args.spec)
        witnesses.append({
            "representative": row["representative"],
            "size": row["size"],
            "minimal": r.meta.get("minimal", "?"),
            "steps": r.meta.get("steps", 0),
            "cert": r.certificate.to_dict() if r.certificate else None,
        })
    # Stamp the sweep certificate before embedding it: emit() will stamp the
    # wrapper, and an inner certificate with no spec path cannot be replayed.
    return orbit_witnesses_certificate(
        sweep_cert=sweep_res.certificate.stamp(args.spec).to_dict(),
        witnesses=witnesses,
        labelled=sweep_res.meta.get("labelled", 0),
        title=spec.title,
    ), witnesses


def _print_witnesses(witnesses):
    print("  " + t("cli.witness.header"))
    for w in witnesses:
        print("    " + t("cli.witness.row", rep=w["representative"],
                         size=w["size"], minimal=w["minimal"],
                         steps=w["steps"]))


def cmd_ideal(args):
    from .engines import algebra
    from .spec import IdealSpec, load_spec

    spec = load_spec(args.spec, IdealSpec)
    res = algebra.ideal(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("cofactors"):
        print("  " + t("cli.ideal.cofactors"))
        for i, h in res.meta["cofactors"].items():
            print("    g{} * ({})".format(i, h))
    return rc


def cmd_cover(args):
    from .engines import algebra
    from .spec import CoverSpec, load_spec

    spec = load_spec(args.spec, CoverSpec)
    res = algebra.cover(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if res.certificate is None:
        return rc

    if not args.optimize:
        if not args.json:
            print("  " + t("cli.cover.pair"))
        return rc

    try:
        bounds = algebra.cover_bounds(
            spec, limits_from(args), prove_optimal=args.prove_optimal,
            max_nodes=args.max_nodes, wall_ms=args.wall_timeout_ms)
    except ValueError as e:
        print("  !! " + str(e), file=sys.stderr)
        return 3

    yours = res.meta["parts"]
    if args.json:
        print(json.dumps({"parts": yours,
                          "relaxation": bounds.get("relaxation"),
                          "optimum": bounds.get("optimum"),
                          "stopped": bounds.get("stopped")},
                         indent=2, ensure_ascii=False))
        return rc

    # Three numbers, each with what it IS. The report that asked for this
    # showed a valid cover read as an optimal one and a fractional optimum
    # read as an integral cost; running them together is the fix only if the
    # labels travel with them.
    print()
    print("  " + t("cli.cover.bounds"))
    print("    " + t("cli.cover.yours", n=yours))
    if bounds.get("relaxation") is not None:
        print("    " + t("cli.cover.relaxed", value=bounds["relaxation"]))
    else:
        print("    " + t("cli.cover.relax_failed",
                         detail=bounds.get("relaxation_failed", "?")))
    if bounds.get("optimum") is not None:
        opt = bounds["optimum"]
        print("    " + t("cli.cover.optimum", value=opt))
        print("  " + t("cli.cover.is_optimal" if str(opt) == str(yours)
                       else "cli.cover.not_optimal", n=yours, value=opt))
    elif bounds.get("stopped"):
        print("    " + t("cli.cover.stopped",
                         detail=bounds["stopped_detail"]))
    elif not args.prove_optimal:
        print("  " + t("cli.cover.try_prove"))
    return rc


def cmd_entry(args):
    from .engines import algebra
    from .spec import EntrySpec, load_spec

    spec = load_spec(args.spec, EntrySpec)
    res = algebra.entry(spec, limits_from(args), spec_path=args.spec)
    return emit(res, args)


def cmd_moment(args):
    from .engines import algebra
    from .spec import MomentSpec, load_spec

    spec = load_spec(args.spec, MomentSpec)
    res = algebra.moment(spec, limits_from(args), spec_path=args.spec)
    return emit(res, args)


def cmd_ratio(args):
    from .engines import algebra
    from .spec import RatioSpec, load_spec

    spec = load_spec(args.spec, RatioSpec)
    res = algebra.ratio(spec, limits_from(args), spec_path=args.spec)
    return emit(res, args)


def cmd_family(args):
    from .engines import algebra
    from .spec import FamilySpec, load_spec

    spec = load_spec(args.spec, FamilySpec)
    res = algebra.family_max(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("value"):
        print("  " + t("verify.family_max.scope"))
    return rc


def cmd_exists(args):
    from .engines import algebra
    from .spec import CoverSpec, load_spec

    spec = load_spec(args.spec, CoverSpec)
    res = algebra.exists(spec, limits_from(args), spec_path=args.spec,
                         max_parts=args.max_parts)
    rc = emit(res, args)
    if not args.json and res.verdict.name == "PROVED":
        print("  " + t("cli.exists.scope"))
    return rc


def cmd_peak(args):
    from .engines import algebra
    from .spec import PeakSpec, load_spec

    spec = load_spec(args.spec, PeakSpec)
    res = algebra.peak(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("value"):
        print("  " + t("cli.peak.scope", floor=res.meta["floor"]))
    return rc


def cmd_parametric(args):
    from .engines import algebra
    from .spec import ParametricSpec, load_spec

    spec = load_spec(args.spec, ParametricSpec)
    res = algebra.parametric(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("bound"):
        print("  " + t("cli.param.scope", floor=res.meta["floor"]))
    return rc


def cmd_eliminate(args):
    from .engines import algebra
    from .spec import EliminateSpec, load_spec

    spec = load_spec(args.spec, EliminateSpec)
    if args.variable:
        spec.eliminate = args.variable
    res = algebra.eliminate(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.certificate is not None:
        # The identity is the certificate's whole content, so it is worth
        # showing rather than leaving in the JSON.
        print("  " + t("cli.eliminate.identity", var=spec.eliminate))
    return rc


def print_loads(cert):
    """The declared regions, what the design does to each, and what it cost."""
    loads = (cert.payload or {}).get("loads") if cert else None
    if not loads:
        return
    print("  " + t("cli.loads.header", n=len(loads)))
    for ld in loads:
        mark = t("cli.loads.binding") if ld["binding"] else t("cli.loads.slack",
                                                              slack=ld["slack"])
        print("    {:<16} {} {} {}   {}".format(
            ld["name"], ld["achieved"], ld["sense"], ld["bound"], mark))
        if ld.get("dual") and ld["dual"] != "0":
            print("    {:<16} {}".format(
                "", t("cli.loads.price", price=ld["dual"])))
        elif ld["binding"]:
            # Binding and priced at zero is a real and confusing state:
            # degeneracy. Saying so beats leaving a blank where a number was.
            print("    {:<16} {}".format("", t("cli.loads.degenerate")))


def cmd_sos(args):
    from .engines import algebra
    from .spec import SOSSpec, load_spec

    spec = load_spec(args.spec, SOSSpec)
    res = algebra.sos(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("squares"):
        print("  " + t("cli.sos.squares"))
        for line in res.meta["squares"]:
            print("    " + line)
    return rc


def cmd_number(args):
    from .engines import algebra
    from .spec import NumberSpec, load_spec

    if args.n is not None:
        spec = NumberSpec(n=args.n, question=args.question)
        path = ""
    else:
        spec = load_spec(args.spec, NumberSpec)
        path = args.spec
    res = algebra.number(spec, limits_from(args), spec_path=path)
    rc = emit(res, args)
    if not args.json and res.meta.get("nodes"):
        print("  " + t("cli.number.tree", n=res.meta["nodes"],
                       depth=res.meta["depth"]))
    return rc


def cmd_mixed(args):
    from .engines import mixed
    from .packing import PackingSpec
    from .spec import LPSpec, load_spec

    spec = load_spec(args.spec)
    if isinstance(spec, PackingSpec):
        # A packing whose items are whole-or-nothing IS a mixed design, and
        # making the user write the conversion would be busywork.
        # Every field carried: listing the ones to keep is how the loads
        # were dropped here, silently, so the design answered another packing.
        import dataclasses

        spec = dataclasses.replace(spec, integer=spec.integer or True).to_lp()
    elif not isinstance(spec, LPSpec):
        print("mixed needs an LPSpec or a PackingSpec; spec() returned "
              + type(spec).__name__, file=sys.stderr)
        return 1
    target = args.target if args.target is not None else spec.target
    freeze = None
    if args.freeze:
        # Their MILP, not ours. A real search may be HiGHS, Gurobi, something
        # bespoke or a person; making certo's solver reproduce it would put
        # certo's limits in front of a construction that already exists.
        data = json.loads(Path(args.freeze).read_text(encoding="utf-8"))
        freeze = data.get("assignment", data)
    if args.prove_optimal:
        from .engines import bb

        res = bb.prove_optimal(spec, limits_from(args), spec_path=args.spec,
                               max_nodes=args.max_nodes,
                               wall_ms=args.wall_timeout_ms)
    else:
        res = mixed.mixed(spec, limits_from(args), spec_path=args.spec,
                          target=target, freeze=freeze)
    rc = emit(res, args)
    if not args.json and res.meta.get("optimum"):
        print("  " + t("cli.bb.tree", n=res.meta["nodes"],
                       bound=res.meta["by_bound"],
                       inf=res.meta["infeasible"], leaf=res.meta["leaves"]))
    if not args.json and res.meta.get("achieved"):
        print("  " + t("cli.mixed.numbers",
                       achieved=res.meta["achieved"],
                       discrete=res.meta["discrete_gain"],
                       conditional=res.meta["conditional"],
                       bound=res.meta.get("bound") or "-"))
        sel = res.meta.get("selected") or []
        print("  " + t("cli.mixed.selected", n=len(sel),
                       names=", ".join(sel[:8]) or "-"))
        print("  " + t("cli.mixed.level." + res.meta["level"]))
        if res.meta.get("skeleton_from") == "external":
            print("  " + t("cli.mixed.external"))
    return rc


def cmd_order(args):
    from .engines import order
    from .spec import OrderSpec, load_spec

    spec = load_spec(args.spec, OrderSpec)
    if args.expect:
        spec.expect = args.expect
    res = order.order(spec, limits_from(args), spec_path=args.spec)
    rc = emit(res, args)
    if not args.json and res.meta.get("leading"):
        print("  " + t("cli.order.leading"))
        for row in res.meta["leading"]:
            print("    {}^{:<6} coefficient {}".format(
                res.certificate.payload["var"], row["exponent"],
                row["coefficient"]))
        if res.meta.get("cancelled"):
            print("  " + t("cli.order.cancelled", n=res.meta["cancelled"]))
    return rc


def cmd_synth(args):
    from .engines import cegis
    from .spec import SynthSpec, load_spec

    def on_round(r):
        print("  " + t("cli.round", round=r["round"],
                        impl={k: v[1] for k, v in r["implementation"].items()},
                        ce={k: v[1] for k, v in r["counterexample"].items()}),
              file=sys.stderr)

    spec = load_spec(args.spec, SynthSpec)
    lim = limits_from(args)
    res = cegis.synth(spec, lim, on_round if args.trace else None)
    if not args.prove_candidate or res.verdict is not Verdict.PROVED:
        return emit(res, args)

    # Paso 2: fijar el candidato y demostrar el enunciado GENERAL.
    from .certificate import synth_proved_certificate

    synth_cert = res.certificate
    rc = emit(res, args)
    print()
    try:
        uni = cegis.prove_candidate(spec, synth_cert.payload["implementation"], lim)
    except ValueError as e:
        print(t("cli.universal.unavailable"))
        print("  " + str(e))
        return rc

    if uni.verdict is Verdict.PROVED:
        print(t("cli.universal.pass", status=uni.status.value))
    elif uni.verdict is Verdict.REFUTED:
        print(t("cli.universal.fail", status=uni.status.value))
        print("  " + t("cli.universal.fail.detail"))
    else:
        print(t("cli.universal.unknown", status=uni.status.value))
    print("  " + uni.detail)

    combo = synth_proved_certificate(
        candidate=res.meta.get("implementation"),
        synth_cert=synth_cert.to_dict(),
        universal_cert=uni.certificate.to_dict() if uni.certificate else None,
    ).stamp(args.spec)
    if args.cert:
        Path(args.cert).write_text(combo.to_json(), encoding="utf-8")
        print("  " + t("cli.combined.written", path=args.cert))
    return rc if uni.verdict is Verdict.PROVED else 2


def _is_zero(v) -> bool:
    from fractions import Fraction

    try:
        return Fraction(str(v)) == 0
    except (ValueError, ZeroDivisionError):
        try:
            return abs(float(v)) < 1e-9
        except (TypeError, ValueError):
            return False


def cmd_opt(args):
    from .engines import lp
    from .packing import PackingSpec
    from .spec import LPSpec, load_spec

    spec = load_spec(args.spec)
    if isinstance(spec, PackingSpec):
        if getattr(args, "gap", False):
            return _opt_gap(args, spec)
        if args.by_type and spec.kinds:
            return _opt_by_type(args, spec)
        spec = spec.to_lp()
    elif not isinstance(spec, LPSpec):
        print("opt needs an LPSpec or a PackingSpec; spec() returned "
              + type(spec).__name__, file=sys.stderr)
        return 1

    direction = None
    if getattr(args, "dual_direction", None):
        direction = {}
        for part in args.dual_direction.split(","):
            name, _, w = part.partition("=")
            direction[name.strip()] = w.strip() or "1"
    res = lp.opt(spec, limits_from(args), use_exact=not args.no_exact,
                 target=args.target, dual_direction=direction)
    rc = emit(res, args)
    if not args.json:
        sol = res.meta.get("solution") or {}
        nz = [(k, v) for k, v in sol.items() if not _is_zero(v)]
        print("  " + t("cli.solution", total=len(sol), nonzero=len(nz)))
        for name, val in nz[:args.top]:
            print("    {} = {}".format(name, val))
        if len(nz) > args.top:
            print("    " + t("cli.solution.more", n=len(nz) - args.top))
        if res.meta.get("target") is not None:
            met = res.meta.get("meets_target")
            print("  " + t("cli.opt.target.met" if met else
                           "cli.opt.target.short",
                           value=res.meta["objective"],
                           target=res.meta["target"]))
        print_loads(res.certificate)
    return rc


def _opt_gap(args, packing):
    """nu against mu*, as one artefact rather than two runs to subtract."""
    from . import packing as pk

    cert, meta = pk.gap(packing, limits_from(args), target=args.target)
    if cert is None:
        return emit(meta, args)
    # A target that was not reached REFUTES only when the integer optimum is
    # global. Below that, `nu` is a point somebody found, and "we did not get
    # there" is not "it cannot be got to" -- which is the distinction the
    # whole tool is built around, and it does not stop at the engines.
    verdict = Verdict.SATISFIABLE
    if meta.get("reached") is False:
        verdict = (Verdict.REFUTED
                   if meta.get("integral_level") == "global_optimum"
                   else Verdict.INCONCLUSIVE)
    res = Result("opt", Status.SAT, verdict, "certo/gap", 0.0,
                 cert, detail=t("engine.opt.gap", mu=meta["mu"], nu=meta["nu"],
                                gap=meta["gap"]), meta=meta)
    rc = emit(res, args)
    if not args.json:
        print("  " + t("cli.opt.gap.tight", n=meta["tight"]))
        print("  " + t("cli.mixed.level."
                       + (meta["integral_level"] or "feasible")))
    return rc


def _opt_by_type(args, packing):
    """The mixed optimum and each type alone.

    Whether mixing buys anything is exactly the gap between the mixed optimum
    and the best single type, and that comparison is the usual question.
    """
    from .engines import lp

    rows = [("mixed", lp.opt(packing.to_lp(), limits_from(args),
                             use_exact=not args.no_exact))]
    for kind in packing.kinds:
        rows.append((kind, lp.opt(packing.restricted({kind}).to_lp(),
                                  limits_from(args),
                                  use_exact=not args.no_exact)))
    for label, r in rows:
        print("  {:<10} {:<14} {}".format(label, str(r.meta.get("objective")),
                                          r.detail[:56]))
    return emit(rows[0][1], args)


def cmd_enum(args):
    from .engines import graphsearch

    res = graphsearch.enum(args.n, args.filter, limits_from(args),
                           use_geng=not args.no_geng)
    if args.out and res.certificate is not None:
        Path(args.out).write_text(
            "\n".join(res.certificate.payload["graph6"]) + "\n", encoding="utf-8"
        )
        print(t("cli.graph6.written", path=args.out))
    return emit(res, args)


def cmd_sweep(args):
    from .engines import domain, graphsearch
    from .spec import DomainSpec, SweepSpec, load_spec

    mode = "all" if args.cert_all else ("none" if args.cert_none else "failures")
    spec = load_spec(args.spec)
    if args.n_range:
        return _sweep_range(args, spec, mode)
    if isinstance(spec, DomainSpec):
        res = domain.sweep_domain(spec, limits_from(args), cert_mode=mode,
                                  by_orbit=getattr(args, "by_orbit", False))
    elif isinstance(spec, SweepSpec):
        res = graphsearch.sweep(spec, limits_from(args),
                                use_geng=not args.no_geng, cert_mode=mode,
                                by_orbit=getattr(args, "by_orbit", False))
    else:
        print("sweep needs a SweepSpec (graphs) or a DomainSpec (any finite "
              "domain); spec() returned " + type(spec).__name__, file=sys.stderr)
        return 1
    # --witnesses replaces the sweep certificate with one that carries the
    # sweep, the orbits AND a minimal witness per orbit -- the whole
    # structural story as one artefact rather than three files to line up.
    witnesses = None
    if getattr(args, "witnesses", False):
        if res.verdict is not Verdict.REFUTED or not res.meta.get("orbits"):
            print("  " + t("cli.witness.needs_orbits"), file=sys.stderr)
        elif not isinstance(spec, DomainSpec) or spec.reduce is None:
            print("  " + t("cli.witness.needs_reduce"), file=sys.stderr)
        else:
            res.certificate, witnesses = _shrink_orbits(spec, res, args)

    rc = emit(res, args)
    if args.json:
        return rc

    print_calibration(res.meta.get("calibration"), args.worst)

    if res.verdict is Verdict.REFUTED:
        # With a symmetry declared, the orbits ARE the answer: printing a
        # thousand relabelled copies underneath them would bury it again.
        if res.meta.get("by_orbit") and not res.meta.get("inferred"):
            print("  " + t("cli.orbits.nothing_inferred"))
        elif res.meta.get("by_orbit"):
            print("  !! " + t("cli.orbits.by_orbit",
                              evaluated=res.meta["evaluated"],
                              inferred=res.meta["inferred"],
                              n=res.meta["spot_checks"]))
        if res.meta.get("orbits"):
            print("  " + t("cli.orbits.summary",
                           labelled=res.meta["labelled"],
                           orbits=res.meta["orbit_count"]))
            print("  " + t("cli.orbits.header"))
            for row in res.meta["orbits"][:10]:
                print("    " + t("cli.orbits.row", rep=row["representative"],
                                 size=row["size"],
                                 members=", ".join(row["members"][:3])))
        else:
            print("  " + t("cli.counterexamples.graph" if res.meta.get("graphs")
                           else "cli.counterexamples"))
            for c in res.meta.get("counterexamples", [])[:10]:
                print("    " + c)
        for d in res.meta.get("describe", []):
            print("    -> " + str(d))
        if witnesses:
            _print_witnesses(witnesses)

    # The uncertified count is reported once, by the level line in `emit`,
    # which also says which of the three levels this run reached. This second
    # message said less, said "graphs" on a domain of tuples, and made readers
    # skim both.
    for label, key in ((t("cli.sweep.errors"), "errors_detail"),
                       (t("cli.sweep.inconclusive"), "inconclusive_detail")):
        for e in res.meta.get(key, [])[:3]:
            print("  {}: {} -> {}".format(label, _item_id(e), e["detail"][:70]))
    return rc


def cmd_cases(args):
    from .cnf import CNF, CNFSpec
    from .engines import sat
    from .spec import load_spec

    p = Path(args.spec)
    if p.suffix.lower() in (".cnf", ".dimacs"):
        obj = CNF.from_dimacs(p.read_text(encoding="utf-8"))
    else:
        obj = load_spec(args.spec)
    spec = obj if isinstance(obj, CNFSpec) else CNFSpec(cnf=obj, title=obj.title)

    backend = args.solver
    if args.solver_binary:
        backend = "binary:" + args.solver_binary
    res = sat.cases(spec, limits_from(args), backend=backend,
                    check_proof=not args.no_check)

    if args.proof and res.certificate is not None and res.certificate.kind == "drat":
        Path(args.proof).write_text(
            "\n".join(res.certificate.payload["proof"]) + "\n", encoding="utf-8")
        print(t("cli.proof.written", path=args.proof))

    rc = emit(res, args)
    if not args.json:
        # A formula encoded by Tseitin is refuted in its NEGATION, so the
        # verdict reads backwards unless what it means is printed beside it.
        # And its auxiliary variables are an artefact of the encoding, so the
        # witness is reported in the variables somebody wrote.
        meaning = (spec.meta or {}).get("means")
        if meaning:
            print("  " + meaning)
            extra = (spec.meta or {}).get("auxiliaries")
            if extra:
                print("  " + t("cli.prop.auxiliaries", n=extra,
                               atoms=len(spec.meta.get("atoms") or [])))
        pc = res.meta.get("proof_check", {})
        for checker, rep in pc.items():
            print("  " + t("cli.checker", name=checker,
                            verdict="OK" if rep.get("ok") else "FAIL",
                            detail=rep.get("detail", "")))
        w = res.meta.get("witness")
        atoms = (spec.meta or {}).get("atoms")
        if w and atoms:
            w = {k: v for k, v in w.items() if k in set(atoms)}
        if w:
            true_ = [k for k, v in sorted(w.items()) if v]
            print("  " + t("cli.witness", n=len(true_),
                            names=", ".join(true_[:20])
                            + (" ..." if len(true_) > 20 else "")))
    return rc


def cmd_shrink(args):
    from .cnf import CNF, CNFSpec
    from .engines import domain, graphsearch, shrink
    from .graphs import Graph
    from .spec import DomainSpec, SweepSpec, load_spec

    obj = load_spec(args.spec)

    if isinstance(obj, (CNF, CNFSpec)):
        spec = obj if isinstance(obj, CNFSpec) else CNFSpec(cnf=obj, title=obj.title)
        return emit(shrink.shrink_cnf(spec, limits_from(args)), args)

    if isinstance(obj, DomainSpec):
        items = {obj.id_of(i): i for i in obj.enumerate()}
        if args.item:
            start = items.get(args.item)
            if start is None:
                print("no item with id " + args.item, file=sys.stderr)
                return 1
        else:
            sw = domain.sweep_domain(obj, limits_from(args))
            ces = sw.meta.get("counterexamples", [])
            if not ces:
                print(t("cli.no_counterexample", n=sw.meta.get("examined")),
                      file=sys.stderr)
                return 2
            start = items[ces[0]]
            if not args.json:
                print(t("cli.starting_from", g6=ces[0]))
        return emit(shrink.shrink_domain(obj, start, limits_from(args),
                                         spec_path=args.spec,
                                         use_objective=args.objective), args)

    if not isinstance(obj, SweepSpec):
        print("shrink needs a SweepSpec (graphs), a DomainSpec (any finite "
              "domain) or a CNFSpec (MUS); spec() returned "
              + type(obj).__name__, file=sys.stderr)
        return 1

    if args.from_cert:
        start = Graph.from_graph6(
            _worst_from_cert(args.from_cert, getattr(obj, "worst", "min")))
    elif args.graph:
        start = Graph.from_graph6(args.graph)
    else:
        sw = graphsearch.sweep(obj, limits_from(args), use_geng=not args.no_geng)
        ces = sw.meta.get("counterexamples", [])
        if not ces:
            print(t("cli.no_counterexample", n=sw.meta.get("examined")),
                  file=sys.stderr)
            return 2
        start = Graph.from_graph6(ces[0])
        if not args.json:
            print(t("cli.starting_from", g6=start.to_graph6()))

    res = shrink.shrink_graph(obj, start, limits_from(args), spec_path=args.spec,
                              keep_filters=not args.no_keep_filters,
                              use_objective=args.objective)
    rc = emit(res, args)
    if not args.json and res.meta.get("trace"):
        print("  " + t("cli.reductions"))
        for st in res.meta["trace"][:12]:
            print("    {:>2}. {:<16} {} -> {}".format(
                st["step"], st["op"], st["from"], st["to"]))
        if len(res.meta["trace"]) > 12:
            print("    " + t("cli.reductions.more",
                              n=len(res.meta["trace"]) - 12))
    return rc


def cmd_bisect(args):
    from .engines import bisect
    from .spec import BisectSpec, load_spec

    def on_probe(e):
        print("  " + t("cli.probe", t=e["t"], status=e["status"]),
              file=sys.stderr)

    spec = load_spec(args.spec, BisectSpec)
    res = bisect.bisect(spec, limits_from(args), on_probe if args.trace else None)
    return emit(res, args)


def _sweep_range(args, spec, mode):
    from .engines import graphsearch
    from .spec import SweepSpec

    if not isinstance(spec, SweepSpec):
        print("--n-range only applies to a SweepSpec", file=sys.stderr)
        return 1
    try:
        lo, hi = (int(x) for x in args.n_range.split(".."))
    except ValueError:
        print(t("cli.range.bad"), file=sys.stderr)
        return 1

    def on_size(row):
        if not args.json:
            print(t("cli.range.row", n=row["n"], verdict=row["verdict"],
                    detail=row["detail"][:70]))
            if row.get("vacuous"):
                print("      !! " + t("cli.range.vacuous"))

    res = graphsearch.sweep_range(spec, lo, hi, limits_from(args),
                                  stop_on_first=args.stop_on_first,
                                  cert_mode=mode,
                                  use_geng=not args.no_geng, on_size=on_size,
                                  spec_path=getattr(args, "spec", "") or "")
    return emit(res, args)


def _worst_from_cert(path, obj_sense="min") -> str:
    """Start from the WORST counterexample of a sweep, not the first one.

    Re-running the sweep to find a starting point doubles the cost when the
    predicate is expensive, and the first counterexample is rarely the
    interesting one. If the sweep collected a value, the worst is picked by it.
    """
    from fractions import Fraction

    data = json.loads(_resolve_read(path))
    p = data.get("payload", {})
    # sweep and domain_sweep share the entry shape on purpose, so the same
    # "start from the worst one" works for graphs and for anything else.
    failures = [_item_id(e) for e in p.get("entries", [])]
    if not failures:
        raise ValueError("that certificate carries no counterexample: " + str(path))
    values = {_item_id(v): Fraction(v["value"]) for v in p.get("values", [])
              if _item_id(v) in failures}
    if not values:
        return failures[0]
    pick = (min if obj_sense == "min" else max)(values, key=values.get)
    return pick


def _resolve_read(path) -> str:
    return Path(path).read_text(encoding="utf-8")


def cmd_ledger(args):
    from . import ledger

    path = args.file or ledger.default_path()

    if args.action == "list":
        rows = ledger.read(path)
        if not rows:
            print(t("cli.ledger.empty", path=path))
            return 2
        for e in rows[-args.limit:]:
            if e.get("_corrupt"):
                print("  ?? corrupt line {}".format(e["_line"]))
                continue
            c = e.get("certificate") or {}
            print("  {}  {:<8} {:<14} {:<12} {}".format(
                e["ts"][:19], e["command"], e["verdict"],
                c.get("kind", "-"), (e.get("note") or e["detail"])[:44]))
        print(t("cli.ledger.count", n=len(rows), path=path))
        return 0

    rep = ledger.verify_all(path, limits_from(args))
    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 0 if rep["counts"]["failed"] == 0 else 1
    for r in rep["rows"]:
        mark = {"ok": "ok", "failed": "XX", "missing": "??",
                "changed": "!!", "no_cert": "--", "corrupt": "??"}[r["state"]]
        print("  [{}] {}  {:<8} {}".format(mark, r["ts"][:19],
                                           r.get("command", "-"),
                                           r["detail"][:60]))
    c = rep["counts"]
    print(t("cli.ledger.summary", total=rep["total"], **c))
    bad = c["failed"] + c["tampered"] + c["corrupt"]
    return 0 if bad == 0 else 1


def _tamper(cert, args) -> int:
    """Forge this certificate one field at a time and report what was caught.

    A REPORT, not a verdict. An uncaught field means either that it carries no
    claim -- and does not belong in a payload that claims to be checkable --
    or that it carries one and nothing is checking it. Only a reader can tell
    those apart, so this prints both columns and exits zero either way. The
    one thing it refuses is probing a certificate that does not verify, where
    every mutation would be "caught" by the failure already there.
    """
    from . import tamper

    out = tamper.probe(cert, limits_from(args),
                       excuse=not getattr(args, "tamper_all", False))
    if args.json:
        print(json.dumps(out, indent=2, ensure_ascii=False))
        return 0 if out["original_ok"] else 1

    if not out["original_ok"]:
        print(t("cli.tamper.original_fails", detail=out.get("detail", "")),
              file=sys.stderr)
        return 1

    print(t("cli.tamper.header", kind=out["kind"]))
    print("  " + t("cli.tamper.caught", n=len(out["caught"])))
    for f in out["caught"]:
        print("    ok  " + f)
    if out["uncaught"]:
        print("  " + t("cli.tamper.uncaught", n=len(out["uncaught"])))
        for f in out["uncaught"]:
            print("    !!  " + f)
        print("  " + t("cli.tamper.means"))
    if out["unshaped"]:
        print("  " + t("cli.tamper.unshaped",
                       names=", ".join(out["unshaped"][:6])))
    if out["excused"]:
        print("  " + t("cli.tamper.excused", n=len(out["excused"])))
    return 0


def cmd_verify(args):
    data = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    cert = Certificate.from_dict(data)

    # Tying the certificate to a file you are LOOKING at is a different check
    # from verifying it, and the failure it catches is specific: verifying an
    # old certificate correctly while believing it describes the spec on your
    # screen. `status` reports staleness across a directory; this refuses.
    if args.spec:
        import hashlib

        want = (cert.provenance or {}).get("spec_sha256")
        got = hashlib.sha256(Path(args.spec).read_bytes()).hexdigest()
        if not want:
            print(t("cli.verify.no_provenance", path=args.spec),
                  file=sys.stderr)
            return 3
        if want != got:
            print(t("cli.verify.spec_differs", path=args.spec,
                    was=(cert.provenance or {}).get("spec_path") or "?",
                    want=want[:16], got=got[:16]), file=sys.stderr)
            return 1
        if not args.json:
            print("  " + t("cli.verify.spec_matches", path=args.spec))

    if getattr(args, "tamper", False):
        return _tamper(cert, args)

    rep = verify_cert(cert, limits_from(args))
    if args.json:
        print(json.dumps(rep.to_dict(), indent=2, ensure_ascii=False))
    else:
        print(t("cli.verify.header",
                state=t("cli.verify.valid" if rep.ok else "cli.verify.invalid"),
                kind=rep.kind,
                how=t(rep.method_key or ("cli.verify.solver_free"
                                         if rep.solver_free
                                         else "cli.verify.with_solver"))))
        for name, ok, detail in rep.checks:
            print("  [{}] {}{}".format("ok" if ok else "XX", name,
                                       "  ({})".format(detail) if detail else ""))
        for w in rep.warnings:
            print("  " + t("cli.warning", text=w))
        if rep.detail:
            # The detail describes what the certificate SAYS about itself.
            # After a failure, a bare trailing summary reads as an
            # endorsement of the thing the checks above just refuted.
            print("  " + (rep.detail if rep.ok
                          else t("cli.verify.despite", detail=rep.detail)))
    return 0 if rep.ok else 1


# Errors, warnings and notes get a mark rather than a colour: this output is
# read as often by a model through `--json` and by a person through a pipe as
# it is on a terminal that has colours at all.
LINT_MARK = {"error": "XX", "warn": "!!", "note": "--"}


def cmd_lint(args):
    """What is wrong with this spec, before the compute is spent on it."""
    from . import lint as linter

    rep = linter.lint(args.spec, limits_from(args))
    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    else:
        print(t("cli.lint.header", kind=rep["kind"] or "?",
                command=rep["command"] or "?"))
        for f in rep["findings"]:
            if f["level"] == "note" and args.quiet:
                continue
            print("  [{}] {}".format(LINT_MARK[f["level"]], f["text"]))
        if not rep["errors"] and not rep["warnings"]:
            print("  " + t("cli.lint.clean"))
        print("  " + t("cli.lint.summary", errors=rep["errors"],
                       warnings=rep["warnings"], notes=rep["notes"]))
    if rep["errors"]:
        return 1
    return 2 if rep["warnings"] else 0


def cmd_repro(args):
    """Everything a referee needs, in one directory."""
    from . import repro

    m = repro.bundle(args.where, args.out, limits_from(args),
                     include_ledger=not args.no_ledger)
    if args.json:
        print(json.dumps(m, indent=2, ensure_ascii=False))
        return 1 if m["refused"] else 0

    print(t("cli.repro.done", n=len(m["certificates"]), path=args.out))
    print("  " + t("cli.repro.free", free=m["solver_free"],
                   total=len(m["certificates"])))
    if m["specs"]:
        print("  " + t("cli.repro.specs", n=len(m["specs"])))
    if m["specs_not_included"]:
        print("  !! " + t("cli.repro.untied", n=len(m["specs_not_included"])))
        for u in m["specs_not_included"][:4]:
            print("       {}  ({})".format(u["spec"], u["why"]))
    if m["refused"]:
        print("  !! " + t("cli.repro.refused", n=len(m["refused"])))
        for r in m["refused"][:4]:
            print("       {}: {}".format(r["file"], "; ".join(r["why"][:1])))
    print("  " + t("cli.repro.next", path=args.out))
    # A bundle that had to leave something out is not a clean result.
    return 1 if m["refused"] else 0


def _print_hollow_lean(rep):
    """Lean files that state nothing, named with their line.

    `status` read certificates and never opened a `.lean`, so a
    `theorem X : True` sat in a project untouched while the report said
    everything was fine. It compiles, carries no `sorry`, and passes an axiom
    audit -- which is exactly why it has to be looked for by name.
    """
    rows = rep.get("hollow_lean") or []
    if not rows:
        return
    print(t("cli.status.lean_hollow", n=len(rows)))
    for row in rows[:8]:
        print("  {}:{}  {}".format(row["rel"], row["line"], row["name"]))
    if len(rows) > 8:
        print(t("cli.status.lean_more", n=len(rows) - 8))


def _manifest(args, status_report):
    """The set, its order, and the number that pins it.

    A count is not a guarantee: two runs over 71 cells with one duplicate also
    count 72. So what goes out is the canonical order, the duplicates of both
    kinds, and -- when `--expect` says what was meant -- what is missing.
    """
    try:
        expect = None
        if getattr(args, "expect", None):
            expect = [line.strip() for line
                      in Path(args.expect).read_text(encoding="utf-8").splitlines()
                      if line.strip()]
        rep = status_report.manifest(args.where, expect=expect)
    except FileNotFoundError:
        print(t("cli.status.nowhere", path=args.where), file=sys.stderr)
        return 3

    if args.manifest != "-":
        Path(args.manifest).write_text(
            json.dumps(rep, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.json or args.manifest == "-":
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    else:
        print("  " + t("cli.manifest.head", count=rep["count"],
                       files=rep["files"], order=rep["order"]))
        print("  " + t("cli.manifest.fingerprint",
                       value=rep["fingerprint"]))
        if rep.get("edges"):
            print("  " + t("cli.manifest.edges", n=len(rep["edges"])))
            for e in rep["edges"][:8]:
                print("    {} {} -> {} {}".format(
                    e["from_kind"], e["from"][:8], e["to_kind"], e["to"][:8]))
        for key, msg in (("duplicate_files", "cli.manifest.same_file"),
                         ("duplicate_subjects", "cli.manifest.same_subject")):
            if rep[key]:
                print("  !! " + t(msg, n=len(rep[key])))
        if "missing" in rep:
            if rep["complete"]:
                print("  " + t("cli.manifest.complete", n=rep["expected"]))
            else:
                for name in rep["missing"][:8]:
                    print("  [XX] " + t("cli.manifest.missing", name=name))
                for name in rep["unexpected"][:8]:
                    print("  [??] " + t("cli.manifest.unexpected", name=name))
        if args.manifest != "-":
            print("  " + t("cli.cert.written", path=args.manifest))
    # A manifest asked to check a declared set and finding it incomplete is a
    # failure; one that only describes what is there is not.
    return 1 if rep.get("missing") or rep.get("unexpected") else 0


def cmd_status(args):
    """Where the proof stands, read off the certificates themselves."""
    from . import status_report

    if getattr(args, "manifest", None):
        return _manifest(args, status_report)

    try:
        rep = status_report.scan(args.where, verify_all=args.verify,
                                 limits=limits_from(args))
    except FileNotFoundError:
        print(t("cli.status.nowhere", path=args.where), file=sys.stderr)
        return 3

    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 1 if rep["broken"] else 0

    if not rep["certificates"]:
        print(t("cli.status.empty", path=rep["root"], skipped=rep["skipped"]))
        # A directory with no certificates and a hollow theorem in it is the
        # WORST case, not the empty one: nothing was established and the file
        # that says so passes every gate. Reporting "nothing here" and exiting
        # zero is how it stayed unnoticed.
        _print_hollow_lean(rep)
        return 1 if rep.get("hollow_lean") else 0

    _print_hollow_lean(rep)
    print(t("cli.status.header", n=rep["certificates"], path=rep["root"]))
    print("  " + "   ".join("{} {}".format(k, v)
                            for k, v in rep["kinds"].items()))

    _rows(t("cli.status.results", n=len(rep["results"])), rep["results"],
          lambda n: ["  {:<16} {:<30} {}".format(
              n["kind"], _tail(n["rel"], 30), n["headline"]).rstrip()])

    # Owed comes first among the problems: a bridge is the thing a reader is
    # most likely to have forgotten, precisely because everything around it
    # verified.
    _rows(t("cli.status.owed", n=len(rep["owed"])), rep["owed"],
          lambda o: ["  {}: {}".format(o["rel"], o["name"])]
                    + (['      "{}"'.format(o["why"])] if o["why"] else []))
    _rows(t("cli.status.hollow", n=len(rep["hollow"])), rep["hollow"],
          lambda h: ["  {}: {}".format(h["rel"], h["text"])])
    _rows(t("cli.status.stale", n=len(rep["stale"])), rep["stale"],
          lambda x: ["  {}: {}".format(
              x["rel"],
              t("cli.status.stale." + x["why"], spec=x["spec"] or "?"))])
    _rows(t("cli.status.broken", n=len(rep["broken"])), rep["broken"],
          lambda b: ["  {}: {}".format(b["rel"], b["detail"])])

    if not args.verify:
        print()
        print("  " + t("cli.status.unverified"))
    return 1 if rep["broken"] else 0


def _tail(path, width):
    """The end of a path, which is the part that identifies it."""
    s = str(path)
    return s if len(s) <= width else "..." + s[-(width - 3):]


def _rows(title, items, render):
    """A titled section, or nothing at all when there is nothing to say."""
    if not items:
        return
    print()
    print("  " + title)
    for item in items:
        for line in render(item):
            print(line)


def cmd_export(args):
    if args.lean:
        return _export_lean(args)

    from .cnf import CNF, CNFSpec
    from .spec import Spec, SynthSpec, load_spec
    from . import z3util
    import z3

    obj = load_spec(args.spec)
    if isinstance(obj, (CNF, CNFSpec)):
        print((obj.cnf if isinstance(obj, CNFSpec) else obj).to_dimacs(), end="")
    elif isinstance(obj, Spec):
        parts = list(obj.formulas)
        if obj.goal is not None:
            parts.append(z3.Not(obj.goal) if args.negate_goal else obj.goal)
        print(z3util.smt2(*parts))
    elif isinstance(obj, SynthSpec):
        impl, behav, corr = obj.normalized()
        print("; ---- impl_constraints ----")
        print(z3util.smt2(impl))
        print("; ---- behavior ----")
        print(z3util.smt2(behav))
        print("; ---- correctness ----")
        print(z3util.smt2(corr))
    else:
        print("export does not support " + type(obj).__name__, file=sys.stderr)
        return 1
    return 0


# ---------------------------------------------------------------------------


def _export_lean(args):
    """Lean 4 from a certificate: data for a graph, proof steps for the rest.

    Which exporter runs is decided by the certificate's KIND, because that is
    what determines how much can honestly be emitted. A Farkas certificate
    becomes a runnable `linarith` example; a `compose` proof becomes a
    skeleton with `sorry` on exactly the bridges; a sweep becomes a list Lean
    can `decide` over. A graph counterexample is still data, because data is
    all it is.
    """
    from . import lean, leanexport
    from .graphs import Graph

    if args.graph:
        text = lean.graphs_to_lean([Graph.from_graph6(args.graph)],
                                   "graph6 " + args.graph)
        return _write_lean(text, args, [])

    path = Path(args.spec)
    data = json.loads(path.read_text(encoding="utf-8"))
    kind = data.get("kind")
    source = "{} (certificate {})".format(
        args.spec, Certificate.from_dict(data).digest())
    data["digest"] = Certificate.from_dict(data).digest()

    exporter = leanexport.EXPORTERS.get(kind)
    if exporter is not None:
        try:
            text = exporter(data, source)
        except leanexport.NotExportable as e:
            # certo declining to write is a RESULT, not a crash: the reason
            # says what the file would have needed and where the numbers are.
            print(t("cli.lean.declined", reason=str(e)))
            return 2
    else:
        try:
            graphs = lean.graphs_from_certificate(data)
        except ValueError:
            # The list comes from the registry: a hand-kept one went
            # stale the moment a new exporter landed, and an error
            # message that lies about what is supported is worse than
            # no message at all.
            print(t("cli.lean.no_exporter", kind=kind,
                    kinds=", ".join(sorted(leanexport.EXPORTERS))),
                  file=sys.stderr)
            return 3
        text = lean.graphs_to_lean(graphs, source)
    return _write_lean(text, args, [path], cert=data)


def _write_lean(text, args, sources, cert=None):
    from . import leanexport

    if not args.out:
        print(text, end="")
        return 0

    out = Path(args.out)
    out.write_text(text, encoding="utf-8")
    print(t("cli.lean.written", path=str(out)))

    if args.manifest:
        man = leanexport.manifest(list(sources) + [out])
        mp = Path(args.manifest)
        mp.write_text(json.dumps(man, indent=2) + "\n", encoding="utf-8")
        print("  " + t("cli.lean.manifest", path=str(mp)))

    # DOES THE FILE SAY WHAT THE CERTIFICATE ESTABLISHED. Separate from
    # compiling, and the question compiling never answered: a dropped
    # hypothesis or a flipped sign produces a theorem that builds and is not
    # the one the certificate supports. Checked by parsing the emitted text
    # BACK and comparing, so a bug in the exporter shows up as a mismatch
    # rather than as a second opinion that agrees with itself.
    from . import leancheck

    corr = ({"checked": False, "reason": t("leancheck.no_rows", kind="?")}
            if cert is None else leancheck.correspondence(cert, text))
    if not corr.get("checked"):
        print("  " + t("cli.lean.not_compared", reason=corr["reason"]))
    elif corr["ok"]:
        print("  " + t("cli.lean.corresponds", n=corr["hypotheses"]))
    else:
        print("  !! " + t("cli.lean.mismatch",
                          missing=", ".join(corr["missing"]) or "-",
                          extra=", ".join(corr["extra"]) or "-",
                          changed=", ".join(corr["changed"]) or "-",
                          goal="yes" if corr["goal_matches"] else "NO"))
        return 1

    if args.check:
        # "It should compile" is the claim most likely to be wrong and the one
        # nobody should take on trust from a text generator.
        rep = leanexport.check(out, args.lean_project,
                               timeout=getattr(args, "check_timeout_s", 900))
        if not rep["ran"]:
            print("  " + t("cli.lean.not_checked", reason=rep["reason"]))
            return 0
        extra = (t("cli.lean.sorries", n=rep["sorries"]) if rep["sorries"]
                 else "")
        hollow = rep.get("hollow") or 0
        # COMPILING WAS NEVER THE QUESTION. A file whose theorems all state
        # `True` builds cleanly and says nothing, and a user put one through a
        # build gate and a `sorry` audit before noticing by reading it. HOLLOW
        # is the headline when there is one, and the exit code is non-zero.
        state = "FAILED" if not rep["ok"] else ("HOLLOW" if hollow else "OK")
        print("  " + t("cli.lean.checked", state=state, sorries=extra))
        if hollow:
            print("  " + t("cli.lean.hollow", n=hollow))
        if not rep["ok"]:
            print(rep["output"], file=sys.stderr)
            return 1
        if hollow:
            return 1
    return 0



def build_parser():
    # Opciones comunes: van en un parent para que se escriban DESPUES del
    # subcomando, que es el orden natural (`certo synth spec.py --cert c.json`).
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--json", action="store_true", help="JSON output")
    common.add_argument("--brief", action="store_true",
                        help="with --json: the certificate as kind, digest "
                             "and size instead of its whole payload")
    common.add_argument("--lang", choices=available(),
                        help="output language (default: en, or $CERTO_LANG)")
    common.add_argument("--cert", metavar="FILE", help="write the certificate there")
    # It guarantees exactly one thing: no code from the spec file runs. Not
    # that the spec means what you think -- `lint` and the scope warnings are
    # what work on that, and a mode that made people stop reading their own
    # spec would trade a small risk for a larger one.
    common.add_argument("--safe", action="store_true",
                        help="refuse to EXECUTE a spec: only `.json` data "
                             "specs run (same as CERTO_NO_EXEC=1)")
    common.add_argument("--timeout-ms", type=int, default=10_000, dest="timeout_ms")
    common.add_argument("--rlimit", type=int, default=20_000_000,
                        help="DETERMINISTIC work limit for z3")
    common.add_argument("--max-memory-mb", type=int, default=2048,
                        dest="max_memory_mb")
    common.add_argument("--seed", type=int, default=0)
    # The WHOLE run, wall clock -- not one solver call, which is --timeout-ms.
    # At the deadline every thread's stack goes to stderr and the process
    # exits 2: the answer to "what was it waiting on", which a user whose run
    # sat at 0% CPU for 70 minutes had no way to get.
    common.add_argument("--deadline", type=float, default=None, metavar="S",
                        help="stop the whole run after S seconds, printing "
                             "where every thread was (or CERTO_DEADLINE_S)")
    common.add_argument("--heartbeat", type=float, default=None, metavar="S",
                        help="a line on stderr every S seconds while running "
                             "(or CERTO_HEARTBEAT_S)")
    # Separate from --timeout-ms ON PURPOSE -- see `Limits` -- and settable,
    # which it was not: the bound on `geng` existed and nobody could move it.
    common.add_argument("--enumerate-timeout-s", type=int, default=120,
                        dest="enumerate_timeout_s",
                        help="clock for an external enumeration (geng), "
                             "separate from a solver's --timeout-ms")
    common.add_argument("--max-output-mb", type=int, default=64,
                        dest="max_output_mb",
                        help="how much an external enumeration may print "
                             "before it is stopped")
    common.add_argument("--log", nargs="?", const="-", metavar="FILE",
                        help="append this run to the audit ledger "
                             "(default: ./ledger.jsonl)")
    common.add_argument("--self-check", action="store_true", default=None,
                        dest="self_check",
                        help="re-verify the certificate before reporting a "
                             "result. Solver-free certificates are checked "
                             "this way anyway; this also covers the ones that "
                             "need a solver")
    common.add_argument("--no-self-check", action="store_false",
                        dest="self_check",
                        help="skip it even for solver-free certificates")
    common.add_argument("--note", help="note to store with the ledger entry")
    common.add_argument("--tag", action="append", metavar="TAG",
                        help="repeatable tag for the ledger entry")

    p = argparse.ArgumentParser(
        prog="certo",
        description="Proof support: decide, enumerate, optimise and synthesise. "
                    "Everything with a certificate.",
    )
    p.add_argument("--version", action="store_true",
                   help="version, commit where available, and the newest "
                        "certificate schema this build writes")
    sub = p.add_subparsers(dest="cmd", required=False)

    def add(name, helptext, aliases=()):
        """A subcommand, and the other words somebody might type for it.

        `order` shipped, was documented, and was not found by the person who
        wanted it, because they were looking for "asymptotic" and "decays".
        An alias costs one tuple entry and removes that whole failure.
        """
        return sub.add_parser(name, help=helptext, parents=[common],
                              aliases=list(aliases))

    for name, fn, helptext in (
        ("prove", cmd_prove, "negate the claim and look for unsat -> unsat core"),

        ("core", cmd_core, "MUS: which hypotheses are actually needed "
                           "(a MultiSpec gives the hypothesis-by-goal table)"),
    ):
        sp = add(name, helptext)
        sp.add_argument("spec", help=".py file with a spec() function")
        sp.set_defaults(func=fn)

    #  no longer fits the three-liner block above: asking whether the
    # regime is non-empty is a different question from asking whether the
    # claim holds in it, and it needed its own flag to stop being asked by
    # accident.
    sp = add("check", "satisfiability of hypotheses AND claim; "
                      "--hypotheses-only asks if the regime is non-empty")
    sp.add_argument("spec", help=".py file with a spec() function")
    sp.add_argument("--hypotheses-only", action="store_true",
                    dest="hypotheses_only",
                    help="drop the claim and ask whether the hypotheses alone "
                         "have a model; on unsat, name the minimal clash")
    sp.set_defaults(func=cmd_check)

    sp = add("opt", "LP/ILP -> dual certificate in EXACT rationals")
    sp.add_argument("spec", help=".py file with a spec() function")
    sp.add_argument("--no-exact", action="store_true", dest="no_exact",
                    help="skip rational reconstruction; leaves a floating-point "
                         "certificate (faster, NOT citable)")
    sp.add_argument("--top", type=int, default=10, metavar="K",
                    help="how many non-zero variables to show (default 10)")
    sp.add_argument("--target", metavar="VALUE",
                    help="certify objective >= VALUE rather than only "
                         "reporting the optimum. For an existence proof the "
                         "question is usually whether a bound is reached, not "
                         "what the best possible value is")
    sp.add_argument("--dual-direction", metavar="ROW=W,...",
                    dest="dual_direction",
                    help="on a degenerate LP, the OPTIMAL dual maximising the "
                         "weighted sum of these constraints' multipliers -- "
                         "proved maximal by a second exact LP it carries")
    sp.add_argument("--gap", action="store_true",
                    help="with a PackingSpec: the integrality gap mu* - nu as "
                         "ONE exact rational, with both sides certified and "
                         "checked to be about the same packing")
    sp.add_argument("--by-type", action="store_true", dest="by_type",
                    help="with a PackingSpec: also report the optimum of each "
                         "item kind on its own, to see if mixing buys anything")
    sp.set_defaults(func=cmd_opt)

    sp = add("mixed", "a discrete skeleton found by search, with the "
                      "continuous part certified exactly against a target")
    sp.add_argument("spec", help=".py file returning an LPSpec with kinds")
    sp.add_argument("--target", metavar="VALUE",
                    help="the value to reach, as an exact rational like 602/9")
    sp.add_argument("--prove-optimal", action="store_true",
                    dest="prove_optimal",
                    help="prove the MILP optimum by branch and bound, with "
                         "every leaf certified and the tree checked to cover "
                         "the integer domain. Exponential, and it says so "
                         "rather than returning the incumbent when it runs out")
    sp.add_argument("--wall-timeout-ms", type=int, default=None,
                    dest="wall_timeout_ms", metavar="MS",
                    help="a budget for the WHOLE branch-and-bound search. "
                         "`--timeout-ms` is per solver call, which is a "
                         "different thing and does not bound the search. On "
                         "expiry: the best design, the best bound, the gap "
                         "and the node count, and NO certificate of "
                         "optimality")
    sp.add_argument("--max-nodes", type=int, default=5000, dest="max_nodes",
                    help="node budget for --prove-optimal (default 5000)")
    sp.add_argument("--freeze", metavar="FILE",
                    help="a JSON assignment for the discrete variables, from "
                         "YOUR solver rather than CBC: {\"y17\": 1, ...} or "
                         "{\"assignment\": {...}}. It is rounded and checked "
                         "exactly like any other, so where it came from does "
                         "not matter")
    sp.set_defaults(func=cmd_mixed)

    sp = add("farkas", "linarith/nlinarith: non-negative multipliers that "
                       "close the system, in exact rationals")
    sp.add_argument("spec", help=".py file with a spec() function")
    sp.add_argument("--nonlinear", action="store_true",
                    help="add products and squares of the hypotheses first "
                         "(this is exactly what nlinarith does)")
    sp.set_defaults(func=cmd_farkas)

    sp = add("reduce", "quotient a program by a group acting on it, with the "
                       "averaging argument checked")
    sp.add_argument("spec", help=".py file returning a SymmetrySpec")
    sp.set_defaults(func=cmd_reduce)
    sp.add_argument("--parametric", action="store_true",
                    help="require a ParametricSymmetrySpec: the symbolic "
                         "quotient of a family, not one instance")







    sp = add("cycle", "a parameter that depends on itself: compose the growth "
                      "classes around the chain and close the loop")
    sp.add_argument("spec", help=".py file returning a CycleSpec")
    sp.set_defaults(func=cmd_cycle)

    sp = add("bind", "tie a certificate to the Lean declaration meant to "
                     "justify it, and check that it does")
    sp.add_argument("spec", help=".py file returning a BindSpec")
    sp.set_defaults(func=cmd_bind)
    sp = add("range", "the admissible interval of one variable over the "
                      "regime, with the multipliers for each end")
    sp.add_argument("spec", help=".py file returning a Spec")
    sp.add_argument("--var", required=True, help="the variable to bound")
    sp.set_defaults(func=cmd_range)
    sp = add("cone", "local toric data: primitivity, multiplicity, the height "
                     "functional and discrepancies")
    sp.add_argument("spec", help=".py file returning a ConeSpec")
    sp.set_defaults(func=cmd_cone)
    sp = add("profile", "how an optimum responds to ONE capacity across an "
                        "interval: a piecewise-affine function, decided by "
                        "duals, sources and coverage")
    sp.add_argument("spec", help=".py file returning a ProfileSpec")
    sp.set_defaults(func=cmd_profile)
    sp = add("report", "run a command again, decide whose bug it is -- "
                       "certo's, the spec's or the environment's -- and write "
                       "it all to a local folder. Sends nothing")
    sp.add_argument("argv", nargs=argparse.REMAINDER,
                    help="the certo command to reproduce, e.g. "
                         "`opt spec.py --target 5`")
    sp.add_argument("--certificate", metavar="FILE",
                    help="a certificate to include and re-verify")
    sp.add_argument("--wrong", action="store_true",
                    help="the result is mathematically FALSE. A certificate "
                         "that verifies and is false is the worst bug this "
                         "tool can have, and it is reported privately")
    sp.add_argument("--coverage", action="store_true",
                    help="also include the coverage summary -- which kinds of "
                         "question certo could not settle here. Counts and "
                         "sizes only, never what was asked")
    sp.add_argument("--out", metavar="DIR",
                    help="where to write the folder (default: "
                         "./certo-report-<time>-<triage>)")
    sp.set_defaults(func=cmd_report)
    sp = add("columns", "an LP over EVERY clique of a graph, without listing "
                        "them: column generation, and a pricing search the "
                        "verifier reruns")
    sp.add_argument("spec", help=".py file returning a CliqueLPSpec")
    sp.add_argument("--top", type=int, default=20,
                    help="how many cliques of the support to print")
    sp.set_defaults(func=cmd_columns)
    sp = add("semigroup", "an affine semigroup as a CHECKER: pointedness, a "
                          "minimal generating set, and membership with the "
                          "coefficients or the bound that settles it")
    sp.add_argument("spec", help=".py file returning a SemigroupSpec")
    sp.set_defaults(func=cmd_semigroup)
    sp = add("quotient", "a partition of a program's rows and columns, and "
                         "the equivalence it induces: same attainable values")
    sp.add_argument("spec", help=".py file returning an EquitableQuotientSpec")
    sp.set_defaults(func=cmd_quotient)
    sp = add("solve", "an exact linear system: A x = b over the rationals "
                      "or the integers, with a witness either way")
    sp.add_argument("spec", help=".py file returning a LinearSystemSpec")
    sp.set_defaults(func=cmd_solve)
    sp = add("matrix", "exact integer linear algebra: rank, determinant, "
                       "Hermite and Smith, with the transforms")
    sp.add_argument("spec", help=".py file returning a MatrixSpec")
    sp.set_defaults(func=cmd_matrix)
    sp = add("audit", "does each hypothesis earn its place: drop it and "
                      "hunt a counterexample")
    sp.add_argument("spec", help=".py file returning a Spec")
    sp.set_defaults(func=cmd_audit)

    sp = add("ask", "one entry point: load a spec and run whatever command "
                    "its type asks for")
    sp.add_argument("spec", help=".py file returning any spec")
    sp.set_defaults(func=cmd_ask)

    sp = add("commands", "which command answers which question",
             aliases=("what",))
    # `certo what opt` read like the obvious thing to type and was an
    # `unrecognized arguments` error. Naming one asks the same question about
    # one command, which is what somebody typing it wanted.
    sp.add_argument("name", nargs="?",
                    help="one command: its spec, engine and certificate")
    sp.add_argument("--table", action="store_true",
                    help="the derived command/spec/engine/certificate table")
    sp.add_argument("--markdown", action="store_true",
                    help="with --table, as the documents carry it")
    sp.set_defaults(func=cmd_commands)

    sp = add("lint", "check a spec before spending the compute: no goal, an "
                     "empty family, an inductive step that starts too late")
    sp.add_argument("spec", help="the .py file to check")
    sp.add_argument("-q", "--quiet", action="store_true",
                    help="errors and warnings only, without the notes")
    sp.set_defaults(func=cmd_lint)

    sp = add("repro", "bundle spec, certificates, versions and hashes into "
                      "one directory a referee can check")
    sp.add_argument("where", nargs="?", default=".",
                    help="directory of certificates (searched recursively)")
    sp.add_argument("--out", default="repro", metavar="DIR",
                    help="where to write the bundle (default: ./repro)")
    sp.add_argument("--no-ledger", action="store_true", dest="no_ledger",
                    help="leave the audit ledger out")
    sp.set_defaults(func=cmd_repro)

    sp = add("status", "read a directory of certificates and say where the "
                       "proof stands: proved, owed, hollow, stale")
    sp.add_argument("where", nargs="?", default=".",
                    help="directory (searched recursively) or one .json file")
    sp.add_argument("--verify", action="store_true",
                    help="re-verify every certificate, not just read it")
    sp.add_argument("--manifest", nargs="?", const="-", metavar="RUTA",
                    help="the set in canonical order, with one number that "
                         "says it is that set; `-` prints it")
    sp.add_argument("--expect", metavar="RUTA",
                    help="a file of headlines, one per line: --manifest then "
                         "names what is missing rather than only what is here")
    sp.set_defaults(func=cmd_status)

    sp = add("doctor", "what this install can and cannot do, and what each "
                       "gap costs")
    sp.add_argument("--repair", action="store_true",
                    help="what an interrupted install left behind; shows it "
                         "and removes nothing")
    sp.add_argument("--apply", action="store_true",
                    help="with --repair: actually remove what it listed")
    sp.add_argument("--register-mcp", action="store_true", dest="register_mcp",
                    help="add certo to .mcp.json in the current directory, "
                         "merging with whatever is already registered")
    # `register_mcp` always took a path; the command line only ever gave it
    # the current directory, so registering for a project meant `cd` first.
    sp.add_argument("--mcp-path", metavar="FILE", dest="mcp_path",
                    help="with --register-mcp: the .mcp.json to write "
                         "instead of the one in the current directory")
    sp.set_defaults(func=cmd_doctor)

    sp = add("ideal", "polynomial equations: refute them outright, or certify "
                      "what follows, with Groebner cofactors")
    sp.add_argument("spec", help=".py file returning an IdealSpec")
    sp.set_defaults(func=cmd_ideal)

    sp = add("cover", "is this an exact cover -- every element in exactly "
                      "one part? A clique partition is one case")
    sp.add_argument("spec", help=".py file returning a CoverSpec")
    sp.add_argument("--optimize", action="store_true",
                    help="also bound the MINIMUM: the relaxation's exact "
                         "dual, over the spec's `candidates` pool. Your cover "
                         "is an upper bound and this is the lower one")
    sp.add_argument("--prove-optimal", action="store_true",
                    dest="prove_optimal",
                    help="and prove the integer optimum by branch and bound, "
                         "which may not finish")
    sp.add_argument("--max-nodes", type=int, default=5000, dest="max_nodes")
    sp.add_argument("--wall-timeout-ms", type=int, default=None,
                    dest="wall_timeout_ms", metavar="MS",
                    help="a budget for the whole search")
    sp.set_defaults(func=cmd_cover)

    sp = add("entry", "where a sequence first crosses a threshold, and how "
                      "far past it lands")
    sp.add_argument("spec", help=".py file returning an EntrySpec")
    sp.set_defaults(func=cmd_entry)

    sp = add("moment", "the expected number of bad events, exactly -- and the "
                       "existence a mean below one buys")
    sp.add_argument("spec", help=".py file returning a MomentSpec")
    sp.set_defaults(func=cmd_moment)

    sp = add("ratio", "a rational-function inequality, for every parameter "
                      "at once and with no solver")
    sp.add_argument("spec", help=".py file returning a RatioSpec")
    sp.set_defaults(func=cmd_ratio)

    sp = add("family", "the largest of a finite family of linear programs, "
                       "with every other one bounded below it")
    sp.add_argument("spec", help=".py file returning a FamilySpec")
    sp.set_defaults(func=cmd_family)

    sp = add("exists", "does a cover exist at all -- and when it does not, "
                       "the refutation that says so")
    sp.add_argument("spec", help=".py file returning a CoverSpec")
    sp.add_argument("--max-parts", type=int, default=None, metavar="K",
                    dest="max_parts",
                    help="ask whether one exists using at most K parts")
    sp.set_defaults(func=cmd_exists)

    sp = add("peak", "the best INTEGER choice for a family of concave "
                     "quadratics, and the value there")
    sp.add_argument("spec", help=".py file returning a PeakSpec")
    sp.set_defaults(func=cmd_peak)

    sp = add("parametric", "a bound that holds for EVERY value of a "
                           "parameter, from a dual you already have")
    sp.add_argument("spec", help=".py file returning a ParametricSpec")
    sp.set_defaults(func=cmd_parametric)

    sp = add("eliminate", "remove a variable from two polynomials: the "
                          "resultant, with the Bezout identity attached")
    sp.add_argument("spec", help=".py file returning an EliminateSpec")
    sp.add_argument("--variable", metavar="NAME",
                    help="the variable to eliminate, instead of the spec's")
    sp.set_defaults(func=cmd_eliminate)

    sp = add("sos", "certify a polynomial non-negative as an exact sum of "
                    "squares: numeric search, rational certificate")
    sp.add_argument("spec", help=".py file returning a SOSSpec")
    sp.set_defaults(func=cmd_sos)

    sp = add("number", "primality with a Pratt certificate, or a factorisation "
                       "whose factors carry one")
    sp.add_argument("spec", nargs="?", help=".py file returning a NumberSpec")
    sp.add_argument("--n", type=int, help="the integer, instead of a spec file")
    sp.add_argument("--question", choices=("prime", "factor"), default="prime")
    sp.set_defaults(func=cmd_number)

    sp = add("order", "does this term DECAY in n, or is it Theta(1)? "
                      "Substitutes magnitudes and reports the exponent -- the "
                      "asymptotic question a solver cannot ask",
             aliases=("asymptotics", "decays"))
    sp.add_argument("spec", help=".py file returning an OrderSpec")
    sp.add_argument("--expect", choices=("decays", "constant", "grows"),
                    help="what you claim; without it this measures rather "
                         "than decides")
    sp.set_defaults(func=cmd_order)

    sp = add("bounds", "settle a numeric inequality with rigorous interval "
                       "arithmetic: e, log, pi and friends, with a certificate")
    sp.add_argument("spec", help=".py file returning a BoundSpec")
    sp.add_argument("--prec", type=int, metavar="BITS",
                    help="starting precision (default: the spec's, 128)")
    sp.add_argument("--max-prec", type=int, metavar="BITS", dest="max_prec",
                    help="give up above this instead of doubling forever")
    sp.set_defaults(func=cmd_bounds)

    sp = add("induct", "finite base cases plus an inductive step, and the "
                       "check that the chain actually joins")
    sp.add_argument("spec", help=".py file returning an InductSpec")
    sp.set_defaults(func=cmd_induct)

    sp = add("compose", "assemble lemmas and their certificates into one "
                        "proof, with the link between them checked")
    sp.add_argument("spec", help=".py file returning a ProofSpec")
    sp.set_defaults(func=cmd_compose)

    sp = add("synth", "CEGIS: there exists an object, for every input...")
    sp.add_argument("spec")
    sp.add_argument("--trace", action="store_true", help="print every round")
    sp.add_argument("--prove-candidate", action="store_true",
                    dest="prove_candidate",
                    help="once found, fix the candidate and prove the "
                         "UNIVERSAL statement (the spec must carry "
                         "universal= or universal_behavior=)")
    sp.add_argument("--max-iterations", type=int, default=10_000, dest="max_iterations")
    sp.set_defaults(func=cmd_synth)

    sp = add("enum", "enumerate non-isomorphic graphs with filters")
    sp.add_argument("--n", type=int, required=True)
    sp.add_argument("--filter", action="append", default=[],
                    help="repeatable: chordal, connected, k4_free, min_degree=2, ...")
    sp.add_argument("--out", help="write the list in graph6")
    sp.add_argument("--no-geng", action="store_true", help="force the python engine")
    sp.set_defaults(func=cmd_enum)

    sp = add("sweep", "run a predicate and/or collect a value over a family")
    sp.add_argument("spec")
    sp.add_argument("--no-geng", action="store_true")
    sp.add_argument("--cert-all", action="store_true", dest="cert_all",
                    help="store the predicate certificate for EVERY graph, "
                         "not just the counterexamples (expensive)")
    sp.add_argument("--cert-none", action="store_true", dest="cert_none",
                    help="do not store predicate certificates")
    sp.add_argument("--witnesses", action="store_true",
                    help="after a refuted sweep with a symmetry: minimise one "
                         "representative per orbit and report the minimal "
                         "witnesses together, in one certificate")
    sp.add_argument("--by-orbit", action="store_true", dest="by_orbit",
                    help="with a DomainSpec declaring canonicalize: evaluate "
                         "ONE item per orbit and infer the rest. Sound only if "
                         "the predicate is invariant under your symmetry, "
                         "which nothing can prove -- so it is spot-checked "
                         "against real non-representatives and recorded as an "
                         "assumption in the certificate. Works for graph "
                         "sweeps too, where it is for a symmetry FINER than "
                         "isomorphism: the enumerator already quotients by "
                         "that one")
    sp.add_argument("--n-range", metavar="LO..HI", dest="n_range",
                    help="sweep every size in the range and report the first "
                         "one that fails (overrides the spec's n)")
    sp.add_argument("--stop-on-first", action="store_true", dest="stop_on_first",
                    help="stop at the first size that fails")
    sp.add_argument("--worst", type=int, default=3, metavar="K",
                    help="how many extremes to list when the spec collects a "
                         "value (default 3)")
    sp.set_defaults(func=cmd_sweep)

    sp = add("cases", "SAT with a verified DRAT proof -> citable finite case")
    sp.add_argument("spec", help=".py file with spec(), or a .cnf/.dimacs")
    sp.add_argument("--solver", default="internal",
                    help="internal (default, always with a proof) | "
                         "pysat:cadical153 | binary:PATH")
    sp.add_argument("--solver-binary", metavar="RUTA", dest="solver_binary",
                    help="external cadical/kissat: `solver input.cnf proof.drat`")
    sp.add_argument("--conflict-budget", type=int, default=1_000_000,
                    dest="conflict_budget", help="DETERMINISTIC budget")
    sp.add_argument("--proof", metavar="FILE", help="write the DRAT proof there")
    sp.add_argument("--no-check", action="store_true",
                    help="do not verify the proof (not recommended)")
    sp.set_defaults(func=cmd_cases)

    sp = add("shrink", "minimise a counterexample: a graph, or the MUS of a CNF")
    sp.add_argument("spec", help="SweepSpec (graphs) or CNFSpec (MUS)")
    sp.add_argument("--graph", "--from", metavar="G6", dest="graph",
                    help="starting graph in graph6; if absent, sweep finds one")
    sp.add_argument("--from-cert", metavar="FILE", dest="from_cert",
                    help="start from the WORST counterexample of a stored sweep "
                         "certificate instead of re-running the sweep")
    sp.add_argument("--item", metavar="ID",
                    help="with a DomainSpec: start from this item id")
    sp.add_argument("--objective", action="store_true",
                    help="reduce lexicographically: stay a counterexample "
                         "first, improve the spec's `collect` value second")
    sp.add_argument("--no-keep-filters", action="store_true",
                    help="allow leaving the family while reducing")
    sp.add_argument("--no-geng", action="store_true")
    sp.set_defaults(func=cmd_shrink)

    sp = add("bisect", "certified bisection on a constant")
    sp.add_argument("spec", help=".py file returning a BisectSpec")
    sp.add_argument("--trace", action="store_true", help="print every probe")
    sp.set_defaults(func=cmd_bisect)

    sp = add("ledger", "audit log: what was run and whether it still checks out")
    sp.add_argument("action", choices=["list", "verify"])
    sp.add_argument("--file", metavar="FILE", help="ledger path (default ./ledger.jsonl)")
    sp.add_argument("--limit", type=int, default=20, help="rows to list (default 20)")
    sp.set_defaults(func=cmd_ledger)

    sp = add("verify", "re-verify a stored certificate")
    sp.add_argument("certificate", help="the certificate .json file")
    sp.add_argument("--spec", metavar="FILE",
                    help="refuse unless this file is the one the certificate "
                         "was made from, by hash. Verifying an old "
                         "certificate correctly while believing it describes "
                         "the spec on your screen is the failure this catches")
    sp.add_argument("--tamper", action="store_true",
                    help="forge this certificate one payload field at a time "
                         "and report which changes the verifier catches. A "
                         "report, not a verdict: an uncaught field either "
                         "carries no claim or carries one nobody checks")
    sp.add_argument("--tamper-all", action="store_true", dest="tamper_all",
                    help="with --tamper, probe every field including the ones "
                         "certo records as descriptive for its OWN kinds -- "
                         "which is what you want for a certificate that is "
                         "not one of certo's")
    sp.set_defaults(func=cmd_verify)

    sp = add("export", "dump the spec to SMT-LIB2 or DIMACS, or a "
                       "counterexample to Lean")
    sp.add_argument("spec", help=".py spec, or a .json certificate with --lean")
    sp.add_argument("--manifest", metavar="FILE",
                    help="write a JSON manifest of the certificate and the "
                         "emitted file, with hashes, so the Lean side can say "
                         "which run it came from")
    sp.add_argument("--check", action="store_true",
                    help="run the Lean toolchain over the emitted file. "
                         "Without one it says so rather than staying quiet")
    sp.add_argument("--lean-project", metavar="DIR", dest="lean_project",
                    help="the Lean project to compile inside (default: the "
                         "output file's directory)")
    # Compiling against Mathlib is minutes, not a solver's ten seconds, so it
    # has its own clock -- which used to be a constant nobody could move.
    sp.add_argument("--check-timeout-s", type=int, default=900,
                    dest="check_timeout_s",
                    help="how long --check may compile before it is stopped")
    sp.add_argument("--lean", action="store_true",
                    help="emit a graph counterexample as Lean 4 data "
                         "(checked against Lean/Mathlib v4.28.0)")
    sp.add_argument("--graph", metavar="G6",
                    help="with --lean: export this graph6 instead of a certificate")
    sp.add_argument("--out", metavar="FILE", help="write to a file")
    sp.add_argument("--negate-goal", action="store_true",
                    help="export the refutation form (hypotheses + not claim)")
    sp.set_defaults(func=cmd_export)

    return p


def _version_line() -> str:
    """Version, the commit if this is a checkout, and the schema written.

    The schema matters as much as the version: it is what says whether a
    certificate from elsewhere can be read, and it moves on its own timetable.
    """
    import subprocess

    from .certificate import SCHEMA_VERSION

    commit = ""
    try:
        out = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                             cwd=str(Path(__file__).resolve().parent),
                             capture_output=True, text=True, timeout=5)
        if out.returncode == 0:
            commit = out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    line = t("cli.version", version=__version__,
             commit=commit or t("cli.version.no_commit"),
             schema=SCHEMA_VERSION)
    stale = installed_version()
    if stale is not None and stale != __version__:
        # A user reported the CLI saying one version and `pip show` another.
        # The two declarations are now one, so they cannot be WRITTEN apart --
        # but an editable install still goes stale on its own, and silence
        # here is what let it run for three releases.
        line += "\n" + t("cli.version.drift", installed=stale,
                          running=__version__)
    return line


def installed_version():
    """What the packaging metadata claims, or None when it is not installed.

    Deliberately not the source of `__version__`: a stale editable install
    would then make the CLI report the OLD number confidently, which is worse
    than reporting a disagreement.
    """
    # ONE implementation, in `doctor`. This used to ask
    # `importlib.metadata` itself, and so inherited the defect that module's
    # check was written to catch: `importlib.metadata` searches `sys.path`,
    # and `src/<name>.egg-info` answers like an install the moment anybody
    # runs `python -m build`. Two implementations of one question is how they
    # came to disagree, which is the failure this whole guard exists for.
    #
    # A version read from a source tree is not an installed version, so it
    # does not travel: comparing it against `__version__` would report drift
    # between a number and itself.
    from .doctor import _metadata_source

    found, installed, _where = _metadata_source()
    return found if installed else None


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)

    # One flag, one process-wide setting: every `load_spec` in every
    # engine reads it, so a command added later cannot forget to.
    if getattr(args, "safe", False):
        os.environ["CERTO_NO_EXEC"] = "1"
    if getattr(args, "lang", None):
        set_lang(args.lang)
    if getattr(args, "version", False):
        print(_version_line())
        return 0
    if getattr(args, "func", None) is None:
        build_parser().print_help()
        return 2
    # A run that dies or hangs leaves a trace -- see `watch`.
    from . import watch

    watch.enable_crash_traces()
    try:
        with watch.watched(command=getattr(args, "cmd", "") or "",
                           deadline=getattr(args, "deadline", None),
                           heartbeat=getattr(args, "heartbeat", None)):
            return args.func(args)
    except Exception as e:  # noqa: BLE001
        print(t("cli.error", type=type(e).__name__, message=e),
              file=sys.stderr)
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
