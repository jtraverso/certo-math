"""Exhaustive sweep over an arbitrary finite domain.

`graphsearch.sweep` answers the same question for graphs; this answers it for
anything you can enumerate. The contract is identical on purpose -- the same
six states, the same predicate certificates, the same calibration -- because
the only thing that really changes is where the items come from.

What it cannot do, and says so: certify that the domain is COMPLETE. The list
of items is whatever the spec produced. For graphs, `enumerate` at least
guarantees non-isomorphism; here the domain is the user's to define.
"""
from __future__ import annotations

import random
import time

from .. import clock as _clock

from .. import exact
from .. import orbits as orb
from ..certificate import (domain_sweep_certificate, outcome_code,
                           sweep_strength)
from ..i18n import t
from ..limits import Limits
from ..spec import Outcome
from ..status import Result, Status, Verdict
from .graphsearch import _calibration


def _evaluate(spec, item) -> Outcome:
    if spec.predicate is None:
        out = Outcome(ok=True)
    else:
        try:
            r = spec.predicate(item)
        except Exception as e:  # noqa: BLE001
            return Outcome(ok=None, errored=True,
                           detail="{}: {}".format(type(e).__name__, e))
        out = r if isinstance(r, Outcome) else Outcome(ok=bool(r))

    if out.value is None and spec.collect is not None:
        try:
            out.value = spec.collect(item)
        except Exception as e:  # noqa: BLE001
            out.detail = (out.detail + " | collect failed: {}".format(e)).strip(" |")
    return out


SPOT_CHECKS = 12


def orbit_codes(spec, items, groups):
    """The verdict vector a `--by-orbit` run produces, for this domain."""
    return orb.infer(lambda item: _evaluate(spec, item), items, groups,
                     outcome_code)


def _by_orbit(spec, items, groups, rng):
    """Representatives evaluated, the rest inferred -- and then spot-checked."""
    outcomes, codes, reps, evaluated = orbit_codes(spec, items, groups)
    ids = [spec.id_of(i) for i in items]
    spot, clash = orb.spot_check(lambda item: _evaluate(spec, item), items,
                                 groups, reps, evaluated, ids, outcome_code,
                                 rng)
    return outcomes, codes, spot, clash


def sweep_domain(spec, limits: Limits | None = None,
                 cert_mode: str = "failures", by_orbit: bool = False) -> Result:
    t0 = time.perf_counter()
    items = spec.enumerate()
    groups = orb.build(spec, items, [spec.id_of(i) for i in items])

    if by_orbit and groups is None:
        return Result("sweep", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      "certo/domain", (time.perf_counter() - t0) * 1000, None,
                      detail=t("engine.sweep.no_canonicalize"))

    spot, clash = [], None
    precomputed = None
    if by_orbit:
        rng = random.Random((limits or Limits()).seed or 0)
        precomputed, pre_codes, spot, clash = _by_orbit(spec, items, groups, rng)
        if clash is not None:
            return Result(
                "sweep", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                "certo/domain", (time.perf_counter() - t0) * 1000, None,
                detail=t("engine.sweep.not_invariant", item=clash[0],
                         rep=clash[1]),
                meta={"spot_checks": spot})

    failures, errors, unknowns, certs, values = [], [], [], [], []
    codes = []
    for pos, item in enumerate(items):
        # The RUN's deadline: the items not reached are INCONCLUSIVE, by
        # name, and the sweep says so -- never counted as examined.
        if precomputed is None and _clock.expired():
            for k in range(pos, len(items)):
                unknowns.append({"id": spec.id_of(items[k]), "detail": t("clock.not_reached")})
            break
        out = precomputed[pos] if precomputed is not None else _evaluate(spec, item)
        key = spec.id_of(item)
        codes.append(pre_codes[pos] if precomputed is not None
                     else outcome_code(out))
        if out.value is not None:
            values.append({"id": key, "value": exact.serialize(out.value)})
        if out.errored:
            errors.append({"id": key, "detail": out.detail})
            continue
        if out.ok is None:
            unknowns.append({"id": key, "detail": out.detail})
            continue
        if not out.ok:
            failures.append(key)
            if cert_mode in ("failures", "all"):
                certs.append({"id": key, "detail": out.detail,
                              "cert": out.cert.to_dict() if out.cert else None})
        elif cert_mode == "all" and out.cert is not None:
            certs.append({"id": key, "cert": out.cert.to_dict(),
                          "detail": out.detail})

    ms = (time.perf_counter() - t0) * 1000
    counts = {
        "enumerated": len(items), "in_family": len(items),
        "examined": len(items) - len(errors) - len(unknowns),
        "failures": len(failures), "errors": len(errors),
        "inconclusive": len(unknowns),
    }
    calib = _calibration(values, spec.worst)

    # The orbit structure OF THE COUNTEREXAMPLES, not of the domain: a
    # thousand failures that are four objects relabelled is one answer told a
    # thousand times, and the structure of everything that passed is rarely
    # what anyone wanted to read.
    failure_idx = {i for i, c in enumerate(codes) if c in ("F", "f")}
    orbit_rows = (groups.summary(only=failure_idx)
                  if groups is not None and failure_idx else None)
    cert = domain_sweep_certificate(
        ids=[spec.id_of(i) for i in items], entries=certs, mode=cert_mode,
        counts=counts, values=values,
        stats=calib["stats"] if calib else None, title=spec.title,
        outcomes="" if spec.predicate is None else "".join(codes),
        orbits=orbit_rows, labelled=len(failure_idx),
        by_orbit=by_orbit, spot_checks=spot or None,
        evaluated=groups.count if by_orbit else 0,
    )
    if spec.predicate is None:
        cert.payload["no_predicate"] = True
    level = sweep_strength(cert.payload, True)

    described = []
    if spec.describe:
        for item in items:
            if spec.id_of(item) in failures[:5]:
                try:
                    described.append(spec.describe(item))
                except Exception as e:  # noqa: BLE001
                    described.append("describe failed: {}".format(e))

    evaluations = cert.payload["evaluations"]
    certified = cert.payload["certified"]
    base = {**counts, "counterexamples": failures[:50], "describe": described,
            "errors_detail": errors[:5], "inconclusive_detail": unknowns[:5],
            "evaluations": evaluations,
            "predicate_certified": certified,
            "predicate_uncertified": evaluations - certified}
    if spec.predicate is not None:
        base["level"] = level
        base["banner_key"] = "scope.sweep." + level
    if by_orbit:
        base["by_orbit"] = True
        base["evaluated"] = groups.count
        base["inferred"] = len(items) - groups.count
        base["spot_checks"] = len(spot)
    if groups is not None:
        base["domain_orbits"] = groups.count
        base["labelled"] = len(failure_idx)
        if orbit_rows:
            base["orbits"] = orbit_rows
            base["orbit_count"] = len(orbit_rows)
    if calib:
        base["calibration"] = calib

    if spec.predicate is None and calib:
        return Result("sweep", Status.SAT, Verdict.SATISFIABLE, "certo/domain",
                      ms, cert,
                      detail=t("engine.sweep.calibration", count=len(items),
                               summary=calib["summary"]), meta=base)

    if failures:
        note = (t("engine.sweep.refuted.note", n=len(errors) + len(unknowns))
                if errors or unknowns else "")
        if orbit_rows:
            # `note` goes straight after "... examined" with no separator of
            # its own, so it brings one.
            note = (note + " -- " + t("engine.sweep.orbits",
                                      labelled=len(failure_idx),
                                      orbits=len(orbit_rows))).strip()
            note = " " + note
        return Result("sweep", Status.SAT, Verdict.REFUTED, "certo/domain", ms,
                      cert, detail=t("engine.sweep.refuted",
                                     failures=len(failures),
                                     examined=counts["examined"], note=note),
                      meta=base)

    if errors or unknowns:
        return Result("sweep", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      "certo/domain", ms, cert,
                      detail=t("engine.sweep.partial",
                               examined=counts["examined"],
                               n=len(errors) + len(unknowns)), meta=base)

    return Result("sweep", Status.UNSAT, Verdict.PROVED, "certo/domain", ms,
                  cert, detail=t("engine.domain.proved", count=len(items)),
                  meta=base)
