"""Motor de biseccion certificada: el comando `bisect`.

Mejorar una constante es buscar el umbral de un parametro. La biseccion lo
encuentra, y el certificado que devuelve es el par que lo encierra:

    una DEMOSTRACION en el lado bueno  +  una REFUTACION en el lado malo

Las dos se verifican por separado, asi que el resultado no depende de confiar
en la busqueda: si alguien duda del umbral, comprueba los dos extremos.

ADVERTENCIA IMPORTANTE: la biseccion supone MONOTONIA en el parametro. Eso no
se verifica (no se puede, con un numero finito de pruebas). Lo que si se
comprueba son los extremos del intervalo inicial, y si no se comportan como
deben, se dice en vez de devolver un umbral inventado.
"""
from __future__ import annotations

import time

import z3

from ..certificate import bisect_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

HOLDS, FAILS, UNKNOWN = "holds", "fails", "unknown"


def _probe(spec, t, lim):
    """Evalua la afirmacion en t. Devuelve (estado, Result)."""
    from ..cnf import CNF, CNFSpec
    from ..spec import Spec

    obj = spec.build(t)

    if isinstance(obj, Spec):
        from . import smt

        r = smt.prove(obj, lim)
        if r.verdict is Verdict.PROVED:
            return HOLDS, r
        if r.verdict is Verdict.REFUTED:
            return FAILS, r
        return UNKNOWN, r

    if isinstance(obj, (CNF, CNFSpec)):
        from . import sat

        s = obj if isinstance(obj, CNFSpec) else CNFSpec(cnf=obj, title=obj.title)
        r = sat.cases(s, lim)
        # convenio: "se cumple" = no existe contraejemplo = UNSAT
        if r.status is Status.UNSAT:
            return HOLDS, r
        if r.status is Status.SAT:
            return FAILS, r
        return UNKNOWN, r

    raise TypeError(t("engine.bisect.build_type", type=type(obj).__name__))


def instance(obj) -> dict:
    """What a probe at one t ASKED, recorded so `verify` can tie each end's
    certificate to it: the query of a `Spec` (its hypotheses and the negated
    claim), or the DIMACS of a CNF."""
    from .. import z3util
    from ..cnf import CNF, CNFSpec
    from ..spec import Spec

    if isinstance(obj, Spec):
        query = [f for _n, f in obj.assumptions] + [z3.Not(obj.goal)]
        return {"kind": "smt", "query_smt2": z3util.smt2(*query)}
    if isinstance(obj, (CNF, CNFSpec)):
        cnf = obj.cnf if isinstance(obj, CNFSpec) else obj
        return {"kind": "cnf", "dimacs": cnf.to_dimacs()}
    return {"kind": "unknown"}


def bisect(spec, limits: Limits | None = None, on_probe=None) -> Result:
    lim = limits or Limits()
    t0 = time.perf_counter()
    lo, hi = float(spec.lo), float(spec.hi)
    up = spec.direction == "min_true"   # True: se cumple para t grandes
    evals = []

    def probe(t):
        t = int(round(t)) if spec.integer else t
        st, r = _probe(spec, t, lim)
        evals.append({"t": t, "status": st, "verdict": r.verdict.value})
        if on_probe is not None:
            on_probe(evals[-1])
        return t, st, r

    def done(status, verdict, detail, cert=None, meta=None):
        return Result("bisect", status, verdict, "certo/bisect",
                      (time.perf_counter() - t0) * 1000, cert, detail,
                      meta={"evaluations": evals, **(meta or {})})

    # --- los extremos deben comportarse como dice la direccion -----------
    good_t, good_r = (hi, None) if up else (lo, None)
    bad_t, bad_r = (lo, None) if up else (hi, None)

    good_t, gst, good_r = probe(good_t)
    if gst is not HOLDS:
        return done(Status.UNKNOWN_SOLVER, Verdict.ERROR,
                    t("engine.bisect.bad_good", t=good_t, status=gst))

    bad_t, bst, bad_r = probe(bad_t)
    if bst is not FAILS:
        return done(Status.UNKNOWN_SOLVER, Verdict.ERROR,
                    t("engine.bisect.bad_bad", t=bad_t, status=bst))

    # --- biseccion --------------------------------------------------------
    tol = 1 if spec.integer else spec.tol
    while abs(good_t - bad_t) > tol:
        mid = (good_t + bad_t) / 2
        if spec.integer:
            mid = int(mid)
            if mid == int(bad_t) or mid == int(good_t):
                break
        mid, st, r = probe(mid)
        if st is UNKNOWN:
            return done(Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                        t("engine.bisect.unknown", t=mid, detail=r.detail),
                        meta={"bracket": [bad_t, good_t]})
        if st is HOLDS:
            good_t, good_r = mid, r
        else:
            bad_t, bad_r = mid, r

    cert = bisect_certificate(
        direction=spec.direction, integer=spec.integer, tol=tol,
        good_t=good_t, bad_t=bad_t,
        good_cert=good_r.certificate.to_dict() if good_r.certificate else None,
        bad_cert=bad_r.certificate.to_dict() if bad_r.certificate else None,
        good_instance=instance(spec.build(good_t)),
        bad_instance=instance(spec.build(bad_t)),
        evaluations=evals,
    )
    width = abs(good_t - bad_t)
    return done(
        Status.SAT, Verdict.PROVED,
        t("engine.bisect.summary",
          where="{}".format(good_t) if spec.integer else "[{:.6g}, {:.6g}]".format(
              min(good_t, bad_t), max(good_t, bad_t)),
          good=good_t, bad=bad_t, probes=len(evals)),
        cert,
        meta={"threshold": good_t, "fails_at": bad_t, "width": width,
              "probes": len(evals)})
