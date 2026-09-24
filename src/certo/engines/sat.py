"""SAT engine: the `cases` command.

A dedicated SAT solver rather than SMT for two reasons: it is far faster on
large boolean instances with symmetry broken, and it emits a DRAT proof. An
`unsat` with a verified proof is a CITABLE finite case: a referee checks it
without running your code and without trusting your solver.

Three backends, in order of preference by instance size:

  internal        Our own CDCL with DRUP. Slow, but always available and
                  always with a certificate. The default.
  binary:<path>   External cadical / kissat: `solver input.cnf proof.drat`.
                  The serious route for large instances.
  pysat:<name>    Fast at solving, but its proof logging does NOT work on
                  Windows (returns 0 lines). If there is no proof, we say so.

Determinism (rule 3): a conflict budget, not a clock.
"""
from __future__ import annotations

import subprocess
import tempfile
import time
from pathlib import Path

from .. import cdcl, drup
from ..certificate import cnf_model_certificate, drat_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

DEFAULT_BACKEND = "internal"


# ---------------------------------------------------------------------------
# motores
# ---------------------------------------------------------------------------


def _run_internal(cnf, lim):
    r = cdcl.solve(cnf.nvars, [c[:] for c in cnf.clauses],
                   max_conflicts=lim.conflict_budget,
                   timeout_s=max(1.0, lim.timeout_ms / 1000))
    return r.status, r.model, r.proof, "certo/cdcl", {
        "conflicts": r.conflicts, "decisions": r.decisions,
        "propagations": r.propagations, "detail": r.detail,
    }


def _run_binary(cnf, lim, exe):
    with tempfile.TemporaryDirectory() as d:
        cnf_p, prf_p = Path(d) / "f.cnf", Path(d) / "f.drat"
        cnf_p.write_text(cnf.to_dimacs(), encoding="utf-8")
        try:
            r = subprocess.run([exe, str(cnf_p), str(prf_p)], capture_output=True,
                               text=True, timeout=max(1.0, lim.timeout_ms / 1000))
        except subprocess.TimeoutExpired:
            return "unknown", None, None, "binary/" + Path(exe).stem, {
                "detail": "el binario se paso del tiempo"}
        out = r.stdout
        if "s SATISFIABLE" in out:
            model = []
            for line in out.splitlines():
                if line.startswith("v "):
                    model += [int(t) for t in line[2:].split() if t != "0"]
            return "sat", model, None, "binary/" + Path(exe).stem, {}
        if "s UNSATISFIABLE" in out:
            proof = prf_p.read_text(encoding="utf-8").splitlines() if prf_p.exists() else None
            return "unsat", None, proof, "binary/" + Path(exe).stem, {}
        return "unknown", None, None, "binary/" + Path(exe).stem, {
            "detail": (out.strip().splitlines() or ["sin salida"])[-1]}


def _run_pysat(cnf, lim, name):
    from pysat.solvers import Solver

    s = Solver(name=name, bootstrap_with=cnf.clauses, with_proof=True)
    try:
        try:
            s.conf_budget(lim.conflict_budget)
            got = s.solve_limited()
        except (NotImplementedError, AttributeError):
            got = s.solve()
        if got is None:
            return "unknown", None, None, "pysat/" + name, {
                "detail": t("engine.cases.exhausted",
                                    budget=lim.conflict_budget)}
        if got:
            return "sat", s.get_model(), None, "pysat/" + name, {}
        proof = s.get_proof()
        note = {}
        if not proof:
            note["detail"] = (
                "pysat no devolvio prueba (su proof logging no funciona en esta "
                "plataforma). Sin certificado: usa el motor internal o un binario.")
            proof = None
        return "unsat", None, proof, "pysat/" + name, note
    finally:
        s.delete()


# ---------------------------------------------------------------------------


def cases(spec, limits: Limits | None = None, backend: str = DEFAULT_BACKEND,
          check_proof: bool = True, cross_check: bool = True) -> Result:
    lim = limits or Limits()
    cnf = spec.cnf if hasattr(spec, "cnf") else spec
    dimacs = cnf.to_dimacs()
    t0 = time.perf_counter()

    if backend.startswith("binary:"):
        status, model, proof, engine, info = _run_binary(cnf, lim, backend[7:])
    elif backend.startswith("pysat:"):
        status, model, proof, engine, info = _run_pysat(cnf, lim, backend[6:])
    elif backend == "internal":
        status, model, proof, engine, info = _run_internal(cnf, lim)
    else:
        raise ValueError(t("engine.cases.unknown_backend", backend=backend))

    base_meta = {"vars": cnf.nvars, "clauses": len(cnf.clauses), **info}
    ms = lambda: (time.perf_counter() - t0) * 1000  # noqa: E731

    if status == "unknown":
        return Result("cases", Status.RESOURCE_EXHAUSTED, Verdict.INCONCLUSIVE,
                      engine, ms(), None,
                      detail=info.get("detail") or t("engine.cases.exhausted",
                                       budget=""), meta=base_meta)

    if status == "sat":
        true_vars = [v for v in (model or []) if v > 0]
        cert = cnf_model_certificate(dimacs, true_vars)
        return Result("cases", Status.SAT, Verdict.SATISFIABLE, engine, ms(), cert,
                      detail=t("engine.cases.sat"),
                      meta={**base_meta, "witness": cnf.decode(true_vars)})

    # unsat
    if not proof:
        return Result(
            "cases", Status.UNSAT, Verdict.PROVED, engine, ms(), None,
            detail=t("engine.cases.noproof", detail=info.get("detail", "")),
            meta=base_meta)

    solve_ms = ms()
    reports = {}
    if check_proof:
        rep = drup.check(cnf.clauses, proof,
                         timeout_s=max(1.0, lim.timeout_ms / 1000))
        reports["drup-python"] = rep.to_dict()
        if cross_check and drup.drat_trim_available():
            reports["drat-trim"] = drup.check_with_drat_trim(
                dimacs, proof,
                timeout_s=max(1.0, lim.timeout_ms / 1000)).to_dict()
        if not rep.ok:
            return Result(
                "cases", Status.UNKNOWN_SOLVER, Verdict.ERROR, engine, ms(), None,
                detail=t("engine.cases.badproof", detail=rep.detail),
                meta={**base_meta, "proof_check": reports})

    cert = drat_certificate(dimacs, list(proof), cnf.nvars, len(cnf.clauses))
    verified = reports.get("drup-python", {}).get("ok", False)
    return Result(
        "cases", Status.UNSAT, Verdict.PROVED, engine, ms(), cert,
        detail=t("engine.cases.unsat",
                 state=t("engine.cases.verified") if verified
                 else t("engine.cases.unverified"), lines=len(proof)),
        meta={**base_meta, "proof_lines": len(proof), "proof_check": reports,
              "solve_ms": round(solve_ms, 1)})
