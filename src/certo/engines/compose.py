"""The `compose` command: lemmas, their certificates, and the theorem.

Every other command produces a leaf. A real proof is "Lemma A and Lemma B,
therefore the theorem", and that join is the part nobody checks -- a lemma
proved under one hypothesis and used under a slightly different one is the
classic way an assembled argument goes wrong, and it is invisible when the
certificates sit in a directory next to each other.

So this does not merely run the lemmas. For each one it establishes the LINK:
the statement handed to the final step is entailed by what that lemma's
certificate actually closes. The check is uniform, because every certificate
worth composing can be asked the same question -- "which formulas did you
prove jointly unsatisfiable?" -- and the link is then

    not(statement)  =>  those formulas

which, with the certificate's own verification (they are contradictory), gives
exactly: the statement is valid.

Certificates that cannot answer that question -- a finite sweep, a DRAT proof
over propositional variables -- are not refused. They become BRIDGES: verified
on their own, with the step to a first-order formula recorded as prose and
reported every single time the proof is verified. The bridge is in the
author's head either way; the difference is whether the reader can see it.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import z3

from .. import z3util
from ..certificate import (Certificate, obligations_of, proof_certificate,
                           verify as verify_cert, entails)
from ..i18n import t
from ..limits import Limits
from ..spec import Spec
from ..status import Result, Status, Verdict

ENGINE = "certo/compose+z3:" + z3.get_version_string()


def _fail(detail, t0, status=Status.UNKNOWN_SOLVER, meta=None) -> Result:
    return Result("compose", status, Verdict.INCONCLUSIVE, ENGINE,
                  (time.perf_counter() - t0) * 1000, None, detail=detail,
                  meta=meta or {})


def _statement_of(sub_spec):
    """What a Spec proves: its hypotheses imply its goal."""
    hyps = [f for _, f in sub_spec.assumptions]
    if not hyps:
        return sub_spec.goal
    return z3.Implies(z3.And(*hyps) if len(hyps) > 1 else hyps[0], sub_spec.goal)


def _discharge(lem, limits):
    """Run the lemma's own engine. Returns (Result, engine label)."""
    if lem.via == "prove":
        from . import smt
        return smt.prove(lem.proves, limits), "prove"
    if lem.via in ("farkas", "nlinarith"):
        from . import farkas
        return (farkas.farkas(lem.proves, limits,
                              nonlinear=(lem.via == "nlinarith")),
                lem.via)
    raise ValueError(t("engine.compose.bad_via", name=lem.name, via=lem.via))


def compose(spec, limits: Limits | None = None, spec_path: str = "",
            base_dir=None) -> Result:
    lim = limits or Limits()
    t0 = time.perf_counter()

    if spec.goal is None:
        return _fail(t("engine.compose.no_goal"), t0, Status.OUT_OF_THEORY)

    entries, statements = [], []
    for lem in spec.lemmas:
        if getattr(lem, "cited", ""):
            # CITED: nothing to discharge and nothing to verify. The statement
            # goes into the final step, and the source goes into the
            # certificate, where every verification will repeat it.
            statements.append((lem.name, lem.states))
            entry = {"name": lem.name,
                     "statement_smt2": z3util.smt2(lem.states),
                     "derived": False, "bridge": "", "cited": lem.cited,
                     "engine": "cited", "cert": None}
            if lem.subject:
                entry["subject"] = list(lem.subject)
            if lem.transport:
                entry["transport"] = lem.transport
            entries.append(entry)
            continue
        if lem.proves is not None:
            res, engine = _discharge(lem, lim)
            if res.verdict is not Verdict.PROVED or res.certificate is None:
                return _fail(t("engine.compose.lemma_failed", name=lem.name,
                               status=res.status.value, detail=res.detail), t0,
                             meta={"failed_lemma": lem.name})
            phi = lem.states if lem.states is not None else _statement_of(lem.proves)
            sub = res.certificate.to_dict()
            # Refuse to emit what we could not link ourselves. A certificate
            # whose link fails verification should never have been written.
            obl = obligations_of(sub)
            if not obl or not entails(z3.Not(phi), obl, lim):
                return _fail(t("engine.compose.link_failed", name=lem.name), t0,
                             meta={"failed_lemma": lem.name})
            derived, bridge = True, ""
        else:
            path = Path(lem.certificate)
            if base_dir and not path.is_absolute():
                path = Path(base_dir) / path
            if not path.exists():
                return _fail(t("engine.compose.cert_missing", name=lem.name,
                               path=str(path)), t0)
            sub = json.loads(path.read_text(encoding="utf-8"))
            rep = verify_cert(Certificate.from_dict(sub), lim)
            if not rep.ok:
                return _fail(t("engine.compose.cert_invalid", name=lem.name,
                               detail=rep.detail), t0,
                             meta={"failed_lemma": lem.name})
            phi, engine = lem.states, sub.get("kind", "?")
            derived, bridge = False, lem.bridge

        statements.append((lem.name, phi))
        entry = {"name": lem.name, "statement_smt2": z3util.smt2(phi),
                 "derived": derived, "bridge": bridge,
                 "engine": engine, "cert": sub}
        if lem.subject:
            entry["subject"] = list(lem.subject)
        if lem.transport:
            entry["transport"] = lem.transport
        entries.append(entry)

    # The final step is an ordinary `prove`: the lemmas and the theorem's own
    # hypotheses as named premises, the theorem as the goal. Because it is
    # ordinary, its unsat core tells us which lemmas were actually needed.
    from . import smt

    final = Spec(title=spec.title)
    for name, phi in statements:
        final.assume(name, phi)
    for name, f in spec.assumptions:
        final.assume(name, f)
    final.claim(spec.goal)
    step = smt.prove(final, lim)
    ms = (time.perf_counter() - t0) * 1000

    if step.verdict is not Verdict.PROVED or step.certificate is None:
        return Result("compose", step.status, Verdict.INCONCLUSIVE, ENGINE, ms,
                      None, detail=t("engine.compose.step_failed",
                                     status=step.status.value,
                                     detail=step.detail),
                      meta={"lemmas": [e["name"] for e in entries]})

    used = [n for n in step.meta.get("hypotheses_used", [])]
    # A LEVEL CANNOT BE CROSSED SILENTLY. A lemma whose subject differs from
    # the theorem's has moved between objects, and the map has to be named.
    # certo does not check the map -- that is Lean's part, and the boundary
    # this project keeps -- but an unnamed crossing is refused, because it is
    # the step where a fact about a computation becomes a fact about the
    # mathematics without anybody deciding that it should.
    theorem_subject = list(spec.subject) if spec.subject else None
    unnamed = [e["name"] for e in entries
               if e.get("subject") and theorem_subject
               and e["subject"] != theorem_subject and not e.get("transport")]
    if unnamed:
        return _fail(t("engine.compose.silent_transport",
                       names=", ".join(unnamed[:4]), n=len(unnamed)), t0,
                     meta={"silent_transport": unnamed})

    crossings = [{"lemma": e["name"], "from": e["subject"],
                  "to": theorem_subject, "map": e["transport"]}
                 for e in entries
                 if e.get("subject") and theorem_subject
                 and e["subject"] != theorem_subject]

    unused = [e["name"] for e in entries if e["name"] not in used]
    ambient = [f for _, f in spec.assumptions]
    cert = proof_certificate(
        theorem_smt2=z3util.smt2(spec.goal),
        assumptions=spec.names,
        assumptions_smt2=z3util.smt2(*ambient) if ambient else "",
        lemmas=entries, step=step.certificate.to_dict(),
        used=used, unused=unused,
        vacuous=bool(step.meta.get("vacuous")), title=spec.title,
        subject=theorem_subject, crossings=crossings,
    ).stamp(spec_path or None)

    bridges = [e["name"] for e in entries
               if not e["derived"] and not e.get("cited")]
    cited = [e["name"] for e in entries if e.get("cited")]
    cited_used = [n for n in cited if n in used]
    detail = t("engine.compose.proved", lemmas=len(entries),
               derived=len(entries) - len(bridges) - len(cited),
               bridges=len(bridges))
    if cited_used:
        detail += " -- " + t("engine.compose.relative", n=len(cited_used),
                             names=", ".join(cited_used[:4]))
    return Result(
        "compose", Status.UNSAT, Verdict.PROVED, ENGINE, ms, cert,
        detail=detail,
        meta={"lemmas": [e["name"] for e in entries], "used": used,
              "unused": unused, "bridges": bridges, "cited": cited,
              "cited_used": cited_used,
              "vacuous": bool(step.meta.get("vacuous"))},
    )
