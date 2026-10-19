"""`compose` over a `ConstructionSpec`: contracts across a construction.

The checking is `certo.construction`; this runs it once with the producers
on (embedding certificates, computing leaves and inclusion trees), and emits
a `construction` certificate that `verify` re-derives with them off.
"""
from __future__ import annotations

import time
from fractions import Fraction
from pathlib import Path

from ..budget import honours_timeout
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "certo/construction"


def _plain(x):
    """JSON-able: Fractions as text, tuples and sets as lists."""
    if isinstance(x, bool) or x is None or isinstance(x, (int, str)):
        return x
    if isinstance(x, Fraction):
        return str(x)
    if isinstance(x, float):
        return x
    if isinstance(x, dict):
        return {str(k): _plain(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_plain(v) for v in x]
    if isinstance(x, (set, frozenset)):
        return sorted((_plain(v) for v in x), key=str)
    return str(x)


@honours_timeout("compose", ENGINE)
def construct(spec, limits: Limits | None = None, spec_path: str = "",
              base_dir=None) -> Result:
    from .. import construction as C
    from ..certificate import construction_certificate

    t0 = time.perf_counter()
    base = [Path(spec_path).resolve().parent if spec_path else None,
            Path(base_dir) if base_dir is not None else Path.cwd()]
    graphs = _plain(spec.graphs or {})
    steps, report = C.run(graphs, _plain(list(spec.steps or [])), limits, base,
                          prepare=True)
    ms = (time.perf_counter() - t0) * 1000
    summary = [{"id": r["id"], "contract": r["contract"], "ok": r["ok"],
                "degree": r["degree"], "outputs": _plain(r["outputs"])} for r in report]
    meta = {"steps": [{"id": r["id"], "contract": r["contract"], "ok": r["ok"],
                       "degree": r["degree"],
                       "checks": [[label, ok, detail] for label, ok, detail in r["rows"]]}
                      for r in report]}
    failed = [r for r in report if not r["ok"]]
    if failed:
        r = failed[0]
        bad = next((row for row in r["rows"] if not row[1]), ("?", False, ""))
        meta["failed"] = [x["id"] for x in failed]
        return Result("compose", Status.SAT, Verdict.REFUTED, ENGINE, ms, None,
                      detail=t("engine.construction.failed", step=r["id"],
                               contract=r["contract"], check=bad[0],
                               why=bad[2], n=len(failed)), meta=meta)
    degree = C.degree_of(report)
    payload = {"title": spec.title, "conclusion": spec.conclusion, "graphs": graphs,
               "steps": _plain(steps), "summary": summary}
    cert = construction_certificate(payload, solver_free=(degree == "complete")
                                    ).stamp(spec_path or None)
    meta["degree"] = degree
    return Result("compose", Status.UNSAT, Verdict.PROVED, ENGINE, ms, cert,
                  detail=t("engine.construction.holds", n=len(report),
                           contracts=", ".join(sorted({r["contract"] for r in report})),
                           degree=degree,
                           conclusion=spec.conclusion or "-"), meta=meta)
