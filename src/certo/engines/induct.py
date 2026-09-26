"""The `induct` command: base cases, an inductive step, and the gap between.

"Checked by hand up to n = 8, and from there by induction" is how a large
fraction of combinatorial arguments end. Both halves already had a command --
`sweep` or `cases` for the base, `prove` for the step -- and the join was left
to a sentence in the write-up. That join is not decoration: a base covering
3..8 and a step valid only from k >= 10 proves nothing at all, and the
sentence reads exactly the same either way.

What this does NOT do is ask a solver to perform the induction. Z3 has no
induction schema and will not acquire one; the principle is applied here, and
the certificate's structure *is* the application. That is a different kind of
step from a bridge: bridges are claims about what a computation means, and
vary per problem, while induction over the naturals is one fixed, named
schema. So it is recorded, not warned about.

What IS checked, and is the reason to run this rather than write the sentence:

  * every base case holds, each with its own certificate;
  * the step holds with k FREE, so it is universally valid, not valid at one k;
  * the base cases are exactly k0 .. base_upto with no gap and no duplicate;
  * the step starts no later than the base ends, so the chain actually joins.

The last two are where induction proofs break, and neither is visible in a
pile of certificates sitting next to each other.
"""
from __future__ import annotations

import time

import z3

from .. import z3util
from ..certificate import induction_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "certo/induct+z3:" + z3.get_version_string()


def _fail(detail, t0, status=Status.UNKNOWN_SOLVER, meta=None) -> Result:
    return Result("induct", status, Verdict.INCONCLUSIVE, ENGINE,
                  (time.perf_counter() - t0) * 1000, None, detail=detail,
                  meta=meta or {})


def induct(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    from ..certificate import Certificate, entails, obligations_of
    from ..certificate import verify as verify_cert
    from . import smt

    lim = limits or Limits()
    t0 = time.perf_counter()

    step_from = spec.k0 if spec.step_from is None else spec.step_from
    ks = list(range(spec.k0, spec.base_upto + 1))
    if not ks:
        return _fail(t("engine.induct.empty_base", k0=spec.k0,
                       upto=spec.base_upto), t0, Status.OUT_OF_THEORY)
    if step_from > spec.base_upto:
        # Refuse up front rather than emitting a certificate whose own
        # verification would reject it.
        return _fail(t("engine.induct.gap", step=step_from,
                       upto=spec.base_upto), t0, Status.OUT_OF_THEORY)

    base = []
    for k in ks:
        sub = spec.base(k) if callable(spec.base) else spec.base[k]
        if isinstance(sub, str):                       # a stored certificate
            import json
            from pathlib import Path

            path = Path(sub)
            if not path.is_file():
                return _fail(t("engine.induct.base_missing", k=k,
                               path=str(path)), t0)
            data = json.loads(path.read_text(encoding="utf-8"))
            rep = verify_cert(Certificate.from_dict(data), lim)
            if not rep.ok:
                return _fail(t("engine.induct.base_invalid", k=k,
                               detail=rep.detail), t0, meta={"failed_k": k})
            base.append({"k": k, "cert": data, "bridge": spec.bridge,
                         "derived": False})
            continue

        res = _run(sub, lim)
        if res.verdict is not Verdict.PROVED or res.certificate is None:
            return _fail(t("engine.induct.base_failed", k=k,
                           status=res.status.value, detail=res.detail), t0,
                         meta={"failed_k": k})
        base.append({"k": k, "cert": res.certificate.to_dict(),
                     "bridge": spec.bridge, "derived": False})

    # The step, with k free: a proof with a free variable is a proof for all
    # of them, which is exactly what the schema needs.
    step = smt.prove(spec.step, lim)
    if step.verdict is not Verdict.PROVED or step.certificate is None:
        return _fail(t("engine.induct.step_failed", status=step.status.value,
                       detail=step.detail), t0)

    statement, kvar = _step_statement(spec, step_from)
    if statement is None:
        return _fail(t("engine.induct.which_k"), t0, Status.OUT_OF_THEORY)
    obl = obligations_of(step.certificate.to_dict())
    if not obl or not entails(z3.Not(statement), obl, lim):
        return _fail(t("engine.induct.step_link_from", step=step_from), t0)

    ms = (time.perf_counter() - t0) * 1000
    cert = induction_certificate(
        k0=spec.k0, base_upto=spec.base_upto, step_from=step_from,
        base=base, step=step.certificate.to_dict(),
        step_smt2=z3util.smt2(statement), k=str(kvar),
        conclusion=spec.describe or t("engine.induct.conclusion", k0=spec.k0),
        bridge=spec.bridge, title=spec.title,
    ).stamp(spec_path or None)

    return Result(
        "induct", Status.UNSAT, Verdict.PROVED, ENGINE, ms, cert,
        detail=t("engine.induct.proved", n=len(ks), k0=spec.k0,
                 upto=spec.base_upto, step=step_from),
        meta={"base_cases": ks, "step_from": step_from,
              "bridges": [b["k"] for b in base if not b["derived"]]},
    )


def _run(sub, limits):
    """Whichever engine the base case needs, chosen by the spec's type."""
    from ..cnf import CNFSpec
    from ..spec import DomainSpec, Spec, SweepSpec

    if isinstance(sub, Spec):
        from . import smt
        return smt.prove(sub, limits)
    if isinstance(sub, SweepSpec):
        from . import graphsearch
        return graphsearch.sweep(sub, limits)
    if isinstance(sub, DomainSpec):
        from . import domain
        return domain.sweep_domain(sub, limits)
    if isinstance(sub, CNFSpec):
        from . import sat
        return sat.cases(sub.cnf, limits)
    raise TypeError(t("engine.induct.bad_base", got=type(sub).__name__))


def induction_var(goal, declared=None):
    """The induction variable: the one declared, or the only integer the
    step's goal mentions. None when that is ambiguous."""
    from .. import z3util

    if declared is not None:
        return declared
    ints = [c for c in z3util.free_consts(goal) if c.sort() == z3.IntSort()]
    return ints[0] if len(ints) == 1 else None


def required_step(goal, k, step_from):
    """`(k >= step_from and P(k)) -> P(k+1)`, with `P(k)` read off the goal
    `P(k+1)` by substituting k -> k-1.

    THIS is what the step has to prove -- not the implication from whatever
    hypotheses the step spec happened to carry. A step proved under
    `k >= 10`, filed with `step_from = 0`, used to join a base at 0 and
    "prove" P(1) for `P(k) = (k = 0 or k >= 10)`, where P(1) is false: the
    comparison `step_from <= base_upto` read a declared number, and the step
    that was proved never mentioned it.
    """
    pk = z3.substitute(goal, (k, k - 1))
    return z3.Implies(z3.And(k >= step_from, pk), goal)


def _step_statement(spec, step_from):
    """The step as it must hold, or None when the induction variable cannot
    be identified."""
    k = induction_var(spec.step.goal, getattr(spec, "k", None))
    if k is None:
        return None, None
    return required_step(spec.step.goal, k, step_from), k
