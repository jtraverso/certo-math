"""Motor de minimizacion de contraejemplos: el comando `shrink`.

Un contraejemplo de 30 vertices no ensena nada; uno de 7 si. Despacha segun
lo que devuelva spec():

  SweepSpec  -> minimiza un grafo que viola el predicado, borrando vertices y
                aristas mientras siga siendo contraejemplo.
  CNFSpec    -> MUS: subconjunto insatisfacible minimal de clausulas.

Los dos certificados incluyen el TESTIGO DE MINIMALIDAD, que es lo que
distingue "no supe reducir mas" de "esto es minimal":

  - grafo: cada reduccion de un paso falla un filtro o cumple el predicado;
  - CNF:   por cada clausula del MUS, un modelo del MUS sin ella.

Minimal (1-minimal), no minimo: no se afirma que no exista otro contraejemplo
mas pequeno por otro camino.
"""
from __future__ import annotations

import hashlib
import time
from pathlib import Path

from .. import cdcl, exact
from ..certificate import (mus_certificate, shrink_domain_certificate,
                           shrink_graph_certificate)
from ..i18n import t
from ..graphs import Graph, compile_filters
from ..limits import Limits
from ..spec import Outcome
from ..status import Result, Status, Verdict


def _sha(path):
    if not path:
        return ""
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# grafos
# ---------------------------------------------------------------------------


def _delete_vertex(g: Graph, v: int) -> Graph:
    keep = [u for u in range(g.n) if u != v]
    idx = {u: i for i, u in enumerate(keep)}
    return Graph.from_edges(
        g.n - 1, [(idx[a], idx[b]) for a, b in g.edges() if a != v and b != v]
    )


def _delete_edge(g: Graph, e) -> Graph:
    return Graph.from_edges(g.n, [x for x in g.edges() if x != e])


def _reductions(g: Graph):
    for v in range(g.n):
        yield ("del_vertex {}".format(v), _delete_vertex(g, v))
    for e in g.edges():
        yield ("del_edge {}-{}".format(*e), _delete_edge(g, e))


def shrink_graph(spec, start: Graph, limits: Limits | None = None,
                 spec_path: str = "", keep_filters: bool = True,
                 use_objective: bool = False) -> Result:
    """Reduce while it stays a counterexample.

    With `use_objective` and a `collect` on the spec, the reduction is
    LEXICOGRAPHIC: staying a counterexample comes first, improving the
    objective second. Smaller is not always more informative -- often what you
    want is the worst ratio, not the fewest edges.
    """
    t0 = time.perf_counter()
    fns = compile_filters(spec.filters) if keep_filters else []

    def is_counterexample(g):
        """Contraejemplo = esta en la familia y viola el predicado."""
        if g.n == 0:
            return False, t("engine.shrink.empty")
        for name, f in fns:
            if not f(g):
                return False, t("engine.shrink.filter_fails", name=name)
        try:
            r = spec.predicate(g)
        except Exception as e:  # noqa: BLE001
            return False, t("engine.shrink.raised", type=type(e).__name__)
        # The predicate may return a bool or an Outcome. An Outcome object is
        # always truthy, so it has to be unwrapped or every graph would look
        # like it satisfies the predicate.
        ok = r.ok if isinstance(r, Outcome) else bool(r)
        if ok is None:
            return False, t("engine.shrink.inconclusive")
        if ok:
            return False, t("engine.shrink.holds")
        return True, ""

    ok, why = is_counterexample(start)
    if not ok:
        return Result(
            "shrink", Status.SAT, Verdict.ERROR, "certo/shrink",
            (time.perf_counter() - t0) * 1000, None,
            detail=t("engine.shrink.not_ce", why=why),
            meta={"start": start.to_graph6()})

    objective = spec.collect if (use_objective and getattr(spec, "collect", None)) else None

    def score(g):
        if objective is None:
            return None
        try:
            return exact.to_fraction(objective(g))
        except Exception:  # noqa: BLE001
            return None

    current, steps, trace = start, 0, []
    changed = True
    while changed:
        changed = False
        candidates = []
        for op, cand in _reductions(current):
            good, _ = is_counterexample(cand)
            if not good:
                continue
            if objective is None:
                candidates = [(op, cand, None)]
                break                       # first valid one, as before
            candidates.append((op, cand, score(cand)))

        if not candidates:
            break
        if objective is not None:
            # "Worst ratio, not fewest edges": a reduction is only taken if it
            # does not WORSEN the objective. Otherwise shrinking always wins
            # and you end up with the smallest graph rather than the most
            # informative one.
            here = score(current)
            better = min if spec.worst == "min" else max
            scored = [c for c in candidates if c[2] is not None]
            if here is not None:
                scored = [c for c in scored if better(c[2], here) == c[2]]
            if not scored:
                break                       # nothing improves it: stop here
            pick = better(scored, key=lambda c: c[2])
        else:
            pick = candidates[0]

        op, cand, val = pick
        entry = {"step": steps + 1, "op": op, "from": current.to_graph6(),
                 "to": cand.to_graph6()}
        if val is not None:
            entry["objective"] = exact.fmt(val)
        trace.append(entry)
        current, steps, changed = cand, steps + 1, True

    # testigo de minimalidad: por que ninguna reduccion de un paso vale
    blocked = []
    for op, cand in _reductions(current):
        _, reason = is_counterexample(cand)
        # Always a graph here, so `g6` is the accurate name.
        blocked.append({"op": op, "g6": cand.to_graph6(), "reason": reason})

    cert = shrink_graph_certificate(
        spec_path=spec_path, spec_sha256=_sha(spec_path),
        original=start.to_graph6(), minimal=current.to_graph6(),
        filters=list(spec.filters or []), blocked=blocked, steps=steps,
    )
    meta = {"original": start.to_graph6(), "minimal": current.to_graph6(),
            "n": current.n, "m": current.m, "steps": steps, "trace": trace}
    final = score(current)
    if final is not None:
        meta["objective"] = exact.fmt(final)
        meta["objective_start"] = exact.fmt(score(start) or 0)
    return Result(
        "shrink", Status.SAT, Verdict.REFUTED, "certo/shrink",
        (time.perf_counter() - t0) * 1000, cert,
        detail=t("engine.shrink.minimal", n=current.n, m=current.m,
                 n0=start.n, m0=start.m, steps=steps),
        meta=meta,
    )


# ---------------------------------------------------------------------------
# CNF: MUS por borrado
# ---------------------------------------------------------------------------


def shrink_cnf(spec, limits: Limits | None = None) -> Result:
    lim = limits or Limits()
    cnf = spec.cnf if hasattr(spec, "cnf") else spec
    t0 = time.perf_counter()
    original = [list(c) for c in cnf.clauses]

    def solve(clauses):
        return cdcl.solve(cnf.nvars, [c[:] for c in clauses],
                          max_conflicts=lim.conflict_budget,
                          timeout_s=max(1.0, lim.timeout_ms / 1000))

    base = solve(original)
    if base.status != "unsat":
        return Result(
            "shrink", Status.SAT, Verdict.ERROR, "certo/mus",
            (time.perf_counter() - t0) * 1000, None,
            detail=t("engine.mus.not_unsat", status=base.status),
            meta={"clauses": len(original)})

    keep = list(range(len(original)))
    witnesses: dict = {}       # indice -> modelo que prueba que hace falta
    for i in list(keep):
        trial = [original[j] for j in keep if j != i]
        r = solve(trial)
        if r.status == "unsat":
            keep = [j for j in keep if j != i]      # sobraba
        elif r.status == "sat":
            witnesses[i] = [l for l in (r.model or []) if l > 0]
        else:
            return Result(
                "shrink", Status.RESOURCE_EXHAUSTED, Verdict.INCONCLUSIVE,
                "certo/mus", (time.perf_counter() - t0) * 1000, None,
                detail=t("engine.mus.inconclusive", i=i, detail=r.detail),
                meta={"clauses": len(original)})

    mus = [original[i] for i in keep]
    final = solve(mus)
    if final.status != "unsat" or not final.proof:
        return Result(
            "shrink", Status.UNKNOWN_SOLVER, Verdict.ERROR, "certo/mus",
            (time.perf_counter() - t0) * 1000, None,
            detail=t("engine.mus.noproof"),
            meta={"mus_size": len(mus)})

    cert = mus_certificate(
        nvars=cnf.nvars, original=original, mus_indices=keep, mus=mus,
        proof=list(final.proof),
        witnesses={str(i): witnesses.get(i, []) for i in keep},
        var_names=[cnf.name_of(v) for v in range(1, cnf.nvars + 1)],
    )
    return Result(
        "shrink", Status.UNSAT, Verdict.PROVED, "certo/mus",
        (time.perf_counter() - t0) * 1000, cert,
        detail=t("engine.mus.summary", mus=len(mus), total=len(original),
                 dropped=len(original) - len(mus)),
        meta={"original_clauses": len(original), "mus_clauses": len(mus),
              "dropped": len(original) - len(mus), "proof_lines": len(final.proof)},
    )


# ---------------------------------------------------------------------------
# arbitrary finite domains
# ---------------------------------------------------------------------------


def shrink_domain(spec, start, limits: Limits | None = None,
                  spec_path: str = "", use_objective: bool = False) -> Result:
    """The same reduction, for items that are not graphs.

    The reduction relation is the spec's: there is no sensible default for an
    arbitrary domain, so `reduce` is required rather than guessed.

    The trace records the INDEX taken into `reduce(item)` at each step, not
    just the resulting id. That is what lets verification replay the descent
    exactly instead of re-running the search.
    """
    t0 = time.perf_counter()
    reduce = spec.reducer()
    if reduce is None:
        raise ValueError(t("engine.shrink.no_reduce"))

    def is_counterexample(item):
        try:
            r = spec.predicate(item) if spec.predicate else True
        except Exception as e:  # noqa: BLE001
            return False, t("engine.shrink.raised", type=type(e).__name__)
        ok = r.ok if isinstance(r, Outcome) else bool(r)
        if ok is None:
            return False, t("engine.shrink.inconclusive")
        return (False, t("engine.shrink.holds")) if ok else (True, "")

    def score(item):
        if not (use_objective and spec.collect):
            return None
        try:
            return exact.to_fraction(spec.collect(item))
        except Exception:  # noqa: BLE001
            return None

    ok, why = is_counterexample(start)
    if not ok:
        return Result("shrink", Status.SAT, Verdict.ERROR, "certo/shrink",
                      (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.shrink.not_ce", why=why),
                      meta={"start": spec.id_of(start)})

    current, steps, trace = start, 0, []
    changed = True
    while changed:
        changed = False
        cands = []
        for i, cand in enumerate(reduce(current)):
            good, _ = is_counterexample(cand)
            if good:
                cands.append((i, cand, score(cand)))
        if not cands:
            break
        if use_objective and spec.collect:
            here = score(current)
            better = min if spec.worst == "min" else max
            scored = [c for c in cands if c[2] is not None]
            if here is not None:
                scored = [c for c in scored if better(c[2], here) == c[2]]
            if not scored:
                break
            pick = better(scored, key=lambda c: c[2])
        else:
            pick = cands[0]
        i, cand, val = pick
        entry = {"step": steps + 1, "index": i, "to": spec.id_of(cand)}
        if val is not None:
            entry["objective"] = exact.fmt(val)
        trace.append(entry)
        current, steps, changed = cand, steps + 1, True

    blocked = []
    for i, cand in enumerate(reduce(current)):
        _, reason = is_counterexample(cand)
        blocked.append({"index": i, "id": spec.id_of(cand), "reason": reason})

    cert = shrink_domain_certificate(
        spec_path=spec_path, spec_sha256=_sha(spec_path),
        original=spec.id_of(start), minimal=spec.id_of(current),
        trace=trace, blocked=blocked, steps=steps)
    meta = {"original": spec.id_of(start), "minimal": spec.id_of(current),
            "steps": steps, "trace": trace}
    final = score(current)
    if final is not None:
        meta["objective"] = exact.fmt(final)
    return Result("shrink", Status.SAT, Verdict.REFUTED, "certo/shrink",
                  (time.perf_counter() - t0) * 1000, cert,
                  detail=t("engine.shrink.minimal_item",
                           item=spec.id_of(current), start=spec.id_of(start),
                           steps=steps),
                  meta=meta)


def orbit_witnesses(spec, sweep_res, limits, spec_path=None):
    """Minimise one representative per orbit, and wrap the sweep, the orbits
    and the minimal witnesses as ONE certificate -- `sweep --witnesses`.
    Returns `(certificate, witnesses)`. Shared by the command and the MCP
    tool, which had no way to ask for it."""
    from ..certificate import orbit_witnesses_certificate

    rows = sweep_res.meta.get("orbits") or []
    by_id = {spec.id_of(i): i for i in spec.enumerate()}
    witnesses = []
    for row in rows:
        start = by_id.get(row["representative"])
        if start is None:
            continue
        r = shrink_domain(spec, start, limits, spec_path=spec_path)
        witnesses.append({
            "representative": row["representative"],
            "size": row["size"],
            "minimal": r.meta.get("minimal", "?"),
            "steps": r.meta.get("steps", 0),
            "cert": r.certificate.to_dict() if r.certificate else None,
        })
    # Stamp the sweep certificate before embedding it: an inner certificate
    # with no spec path cannot be replayed.
    return orbit_witnesses_certificate(
        sweep_cert=sweep_res.certificate.stamp(spec_path).to_dict(),
        witnesses=witnesses,
        labelled=sweep_res.meta.get("labelled", 0),
        title=spec.title,
    ), witnesses
