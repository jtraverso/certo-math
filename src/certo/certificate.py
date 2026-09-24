"""Certificates.

Cross-cutting rule 1: every command returns a certificate, or says why not.

Each certificate stores enough to be re-verified WITHOUT the original session
and without trusting the LLM that proposed the statement. `solver_free` says
whether verification needs a solver at all; those are the strong ones.

Notes are stored as CATALOGUE KEYS rather than rendered text, so a certificate
issued in one language reads correctly in another. What travels must not be
tied to the language of whoever produced it.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

from .i18n import t

# FROZEN AT 0.4. From this version an existing payload's fields do not move:
# no renames, no removals, no changes of meaning. Adding a NEW certificate
# kind stays allowed and always will -- that is additive and breaks nothing --
# and so does adding an OPTIONAL field that readers may ignore. Anything else
# needs a bump here and a migration note in CHANGELOG.md.
#
# What this buys: a certificate produced for a paper today still verifies
# against a later certo, which is the only way "re-verifiable" survives
# contact with time.
SCHEMA_VERSION = 4


def _without_provenance(value):
    """The same structure with every `provenance` block dropped, recursively.

    Used only by `digest`. Provenance is how a certificate is tied to its spec
    and its run; it is not what the certificate SAYS, and two runs of the same
    question say the same thing.
    """
    if isinstance(value, dict):
        return {k: _without_provenance(v) for k, v in value.items()
                if k != "provenance"}
    if isinstance(value, list):
        return [_without_provenance(v) for v in value]
    return value


@dataclass
class Certificate:
    kind: str
    solver_free: bool
    payload: dict = field(default_factory=dict)
    note_key: str = ""
    note_args: dict = field(default_factory=dict)
    provenance: dict = field(default_factory=dict)

    def __post_init__(self):
        # Version and date ALWAYS, whether issued from the CLI or the API.
        # Only the caller knows the spec path: stamp() adds it.
        if not self.provenance:
            from . import __version__

            self.provenance = {
                "certo_version": __version__,
                "created": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            }

    @property
    def note(self) -> str:
        """Rendered in the reader's language, not the writer's."""
        return t(self.note_key, **self.note_args) if self.note_key else ""

    def to_dict(self) -> dict:
        return {
            "schema": SCHEMA_VERSION,
            "kind": self.kind,
            "solver_free": self.solver_free,
            "note_key": self.note_key,
            "note_args": self.note_args,
            "note": self.note,          # rendered copy, for reading the raw JSON
            "provenance": self.provenance,
            "payload": self.payload,
        }

    @staticmethod
    def unwrap(d: dict) -> dict:
        """The certificate, whether it arrived alone or inside a run.

        `--cert FILE` writes the certificate; `--json` writes the RUN, which
        contains one under `certificate`. Both shapes are right and a reader
        who guesses wrong loses an afternoon, so anything that expects a
        certificate accepts either. They are told apart by what is at the
        root: a certificate has `kind`, a run has `command`.
        """
        if isinstance(d, dict) and "kind" not in d and "certificate" in d:
            inner = d["certificate"]
            if isinstance(inner, dict):
                return inner
        return d

    @classmethod
    def from_dict(cls, d: dict) -> "Certificate":
        d = cls.unwrap(d)
        return cls(
            kind=d["kind"],
            solver_free=d.get("solver_free", False),
            payload=d.get("payload", {}),
            note_key=d.get("note_key", ""),
            note_args=d.get("note_args", {}),
            provenance=d.get("provenance") or {"legacy": True},
        )

    def digest(self) -> str:
        """Content addressing: kind and payload, with every timestamp removed.

        Provenance carries a timestamp, so including it would give two
        identical runs different digests. The digest identifies the
        MATHEMATICAL CONTENT, not the run.

        AT EVERY LEVEL, which is the part that was wrong. A certificate that
        embeds sub-certificates -- a branch-and-bound tree, an `opt --gap`, a
        composed proof -- carries THEIR provenance inside its own payload, so
        its digest moved between two identical runs. That defeats exactly what
        a digest is for: comparing, deduplicating, and citing a result by id.
        """
        blob = json.dumps({"kind": self.kind,
                           "payload": _without_provenance(self.payload)},
                          sort_keys=True).encode()
        return hashlib.sha256(blob).hexdigest()[:16]

    def stamp(self, spec_path=None, extra=None) -> "Certificate":
        """Tie the certificate to the spec that produced it, and the version."""
        from . import __version__

        prov = {"certo_version": __version__,
                "created": datetime.now(timezone.utc).isoformat(timespec="seconds")}
        if spec_path:
            p = Path(spec_path)
            prov["spec_path"] = str(p)
            if p.exists():
                prov["spec_sha256"] = hashlib.sha256(p.read_bytes()).hexdigest()
        prov.update(extra or {})
        self.provenance = prov
        return self


@dataclass
class VerifyReport:
    ok: bool
    kind: str
    solver_free: bool
    checks: list = field(default_factory=list)  # [(name, ok, detail)]
    detail: str = ""
    warnings: list = field(default_factory=list)
    # How the checking was done. `solver_free` says a solver was not needed,
    # which is not the same as saying nothing was run: replaying a sweep runs
    # the user's own predicate. Naming the method keeps the header honest.
    method_key: str = ""

    def to_dict(self) -> dict:
        return {
            "ok": self.ok,
            "kind": self.kind,
            "solver_free": self.solver_free,
            "method": self.method_key,
            "checks": [{"check": c, "ok": o, "detail": d} for c, o, d in self.checks],
            "warnings": self.warnings,
            "detail": self.detail,
        }


def _provenance_warnings(cert: Certificate) -> list:
    """Provenance does not invalidate the mathematics, but a mismatch matters.

    A certificate stays valid even if the spec changed: it verifies on its
    own. What stops being true is the ASSOCIATION between the two, and that
    has to be said out loud.
    """
    prov = cert.provenance or {}
    out = []
    sp, want = prov.get("spec_path"), prov.get("spec_sha256")
    if sp and want:
        p = Path(sp)
        if not p.exists():
            out.append(t("verify.provenance.gone", path=sp))
        elif hashlib.sha256(p.read_bytes()).hexdigest() != want:
            out.append(t("verify.provenance.changed", path=sp))
    if prov.get("legacy"):
        out.append(t("verify.provenance.legacy"))
    return out


# ---------------------------------------------------------------------------
# constructores
# ---------------------------------------------------------------------------


def model_certificate(smt2: str, assignment: dict) -> Certificate:
    return Certificate(
        kind="model",
        solver_free=True,
        payload={"smt2": smt2, "assignment": assignment},
        note_key="cert.note.model",
    )


def unsat_core_certificate(core_smt2: str, names: list, dropped: list,
                           vacuous: bool = False, clash=None) -> Certificate:
    """`vacuous` means the hypotheses contradict each other.

    The proof is still valid -- anything follows from a contradiction -- so
    this is not an error and does not change the verdict. It travels in the
    payload because it is exactly the kind of thing that looks like success
    and must keep being said out loud, long after the run.
    """
    return Certificate(
        kind="unsat_core",
        # Flipped to True by `_with_farkas` when multipliers are found: a core
        # with them is checkable by arithmetic, and one without is not.
        solver_free=False,
        payload={"core_smt2": core_smt2, "names": names, "dropped": dropped,
                 # `clash` is optional, which the frozen schema allows: a
                 # reader that does not know it simply ignores it.
                 "vacuous": bool(vacuous), "clash": clash or []},
        note_key="cert.note.unsat_core",
    )


def _declared_values(sense, objective, integral_objective):
    """The same numbers in the sense the caller asked for.

    `A`, `b`, `c`, `primal`, `dual` and `objective` are stored in the internal
    MAXIMISED system, because `c.x == b.y` closes there and nowhere else. For
    `sense: min` the declared optimum is the negation, and a reader of the
    JSON had no way to know: the payload said `sense: "min", objective:
    "-3/2"` for a minimum of `3/2`, and verified, being consistent with itself
    in a frame it never named.

    So the artefact carries both. This field is OPTIONAL, the way `loads` is:
    a reader that does not know it verifies exactly as before, and the schema
    stays at 4. It is DERIVED here rather than passed in, so an engine cannot
    supply a different number -- and `verify` recomputes it anyway, because a
    field nothing checks is a field that can be forged.
    """
    from . import exact

    if objective is None:
        return {}
    flip = -1 if sense == "min" else 1

    def turn(v):
        if isinstance(v, str):
            return exact.serialize(flip * exact.to_fraction(v))
        return flip * v

    out = {"objective": turn(objective)}
    if integral_objective is not None:
        out["integral_objective"] = turn(integral_objective)
    return out


def lp_dual_certificate(sense, objective, dual, A, b, c, names,
                        primal=None, var_names=None, is_exact=False,
                        integer=False, integral_point=None,
                        integral_objective=None, kinds=None,
                        target=None, loads=None, backend=None) -> Certificate:
    payload = {
            "sense": sense, "objective": objective, "dual": dual,
            "primal": primal, "A": A, "b": b, "c": c,
            "names": names, "var_names": var_names, "exact": is_exact,
            # For an ILP the dual certifies the RELAXATION, which is a bound.
            # The integral point is the other side of it.
            "integer": bool(integer), "integral_point": integral_point,
            "integral_objective": integral_objective,
            # Which variables are discrete, by name. `integer: true` says a
            # discrete part exists; this says WHICH, so a reader of the
            # certificate alone can tell a design from a relaxation.
            "kinds": kinds or {}, "target": target,
            # The objective in the sense that was ASKED, beside the one in
            # the frame the arithmetic uses. Optional, derived, and checked.
            "declared": _declared_values(sense, objective,
                                         integral_objective),
            # Named regions the design was asked to respect, each with what
            # the solution actually does to it and what it cost. An OPTIONAL
            # field, which the frozen schema allows: a reader that does not
            # know about loads verifies the certificate exactly as before.
            "loads": loads or [],
    }
    # Which solver found the point the exact route started from. OPTIONAL and
    # descriptive: it changes nothing that is checked, but on a degenerate
    # program HiGHS and CBC return different optimal vertices, so two correct
    # certificates of the same optimum can differ -- and this says why.
    if backend is not None:
        payload["backend"] = backend
    return Certificate(
        kind="lp_dual",
        solver_free=True,
        payload=payload,
        note_key="cert.note.lp_dual.exact" if is_exact else "cert.note.lp_dual.float",
    )


def cegis_certificate(impl, counterexamples, smt2, iterations) -> Certificate:
    return Certificate(
        kind="cegis",
        solver_free=False,
        payload={
            "implementation": impl,
            "counterexamples": counterexamples,
            "smt2": smt2,
            "iterations": iterations,
        },
        note_key="cert.note.cegis",
    )


def cnf_model_certificate(dimacs: str, true_vars) -> Certificate:
    return Certificate(
        kind="cnf_model",
        solver_free=True,
        payload={"dimacs": dimacs, "true_vars": sorted(true_vars)},
        note_key="cert.note.cnf_model",
    )


def drat_certificate(dimacs: str, proof: list, nvars: int, nclauses: int) -> Certificate:
    return Certificate(
        kind="drat",
        solver_free=True,
        payload={"dimacs": dimacs, "proof": proof,
                 "nvars": nvars, "nclauses": nclauses},
        note_key="cert.note.drat",
    )


def shrink_graph_certificate(spec_path, spec_sha256, original, minimal,
                             filters, blocked, steps) -> Certificate:
    return Certificate(
        kind="shrink_graph",
        solver_free=True,
        payload={"spec_path": str(spec_path), "spec_sha256": spec_sha256,
                 "original": original, "minimal": minimal, "filters": filters,
                 "blocked": blocked, "steps": steps},
        note_key="cert.note.shrink_graph",
    )


def mus_certificate(nvars, original, mus_indices, mus, proof,
                    witnesses, var_names) -> Certificate:
    return Certificate(
        kind="mus",
        solver_free=True,
        payload={"nvars": nvars, "original": original, "mus_indices": mus_indices,
                 "mus": mus, "proof": proof, "witnesses": witnesses,
                 "var_names": var_names},
        note_key="cert.note.mus",
    )


def bisect_certificate(direction, integer, tol, good_t, bad_t,
                       good_cert, bad_cert, evaluations) -> Certificate:
    free = all(c is not None and c.get("solver_free", False)
               for c in (good_cert, bad_cert))
    return Certificate(
        kind="bisect",
        solver_free=free,
        payload={"direction": direction, "integer": integer, "tol": tol,
                 "good_t": good_t, "bad_t": bad_t,
                 "good_cert": good_cert, "bad_cert": bad_cert,
                 "evaluations": evaluations},
        note_key="cert.note.bisect",
    )


def sweep_certificate(n, filters, family_g6, entries, mode, counts,
                      values=None, stats=None, outcomes="",
                      orbits=None, labelled=0, by_orbit=False,
                      spot_checks=None, evaluated=0) -> Certificate:
    """The examined family, the VERDICT VECTOR, and whatever certificates the
    predicate supplied.

    Three things, and they establish three different amounts. The family and
    its hash say which objects were looked at. The verdict vector says what
    the predicate answered for each, and lets a later run confirm it answers
    the same -- reproducible, not certified. Only the third part, a
    certificate per evaluation, establishes the answers themselves without
    trusting the predicate.

    `evaluations` and `certified` are counted over the WHOLE sweep, not over
    the stored entries. A passing sweep stores no entries, and reporting
    "0 of 0 certified" for eleven thousand unchecked evaluations is how a
    certificate ends up claiming more than it holds.
    """
    h = hashlib.sha256("\n".join(sorted(family_g6)).encode()).hexdigest()
    certified = sum(1 for e in entries if e.get("cert"))
    free = all(e["cert"].get("solver_free") for e in entries if e.get("cert"))
    evaluations = counts.get("examined", len(family_g6))
    return Certificate(
        kind="sweep",
        solver_free=bool(free),
        payload={"n": n, "filters": filters, "family_sha256": h,
                 "family_count": len(family_g6), "family_graph6": family_g6,
                 "entries": entries, "mode": mode, "counts": counts,
                 "values": values or [], "stats": stats,
                 "evaluations": evaluations, "certified": certified,
                 "outcomes": outcomes,
                 "outcomes_sha256": outcomes_digest(outcomes) if outcomes else "",
                 "orbits": orbits, "labelled": labelled,
                 "by_orbit": by_orbit, "spot_checks": spot_checks,
                 "evaluated": evaluated},
        note_key="cert.note.sweep",
        note_args={"certified": certified, "total": evaluations},
    )


def synth_proved_certificate(candidate, synth_cert, universal_cert) -> Certificate:
    """Los dos pasos juntos: se encontro acotado, se demostro universal.

    Separados dicen cosas distintas y conviene que se vea: el primero es un
    DESCUBRIMIENTO sobre un dominio acotado, el segundo una PRUEBA simbolica
    del candidato. Solo el segundo es un teorema.
    """
    free = all(c is not None and c.get("solver_free", False)
               for c in (synth_cert, universal_cert))
    return Certificate(
        kind="synth_proved",
        solver_free=free,
        payload={"candidate": candidate, "synth": synth_cert,
                 "universal": universal_cert},
        note_key="cert.note.synth_proved",
    )


def domain_sweep_certificate(ids, entries, mode, counts, values=None,
                             stats=None, title="", outcomes="",
                             orbits=None, labelled=0, by_orbit=False,
                             spot_checks=None, evaluated=0) -> Certificate:
    """Same contract as `sweep`, for a domain the spec defines itself.

    Including the same three levels: the domain and its hash, the verdict
    vector that makes the run replayable, and the per-evaluation certificates
    that would make it certified.
    """
    h = hashlib.sha256(chr(10).join(sorted(ids)).encode()).hexdigest()
    free = all(e["cert"].get("solver_free") for e in entries if e.get("cert"))
    certified = sum(1 for e in entries if e.get("cert"))
    evaluations = counts.get("examined", len(ids))
    return Certificate(
        kind="domain_sweep", solver_free=bool(free),
        payload={"title": title, "ids": ids, "ids_sha256": h,
                 "count": len(ids), "entries": entries, "mode": mode,
                 "counts": counts, "values": values or [], "stats": stats,
                 "evaluations": evaluations, "certified": certified,
                 "outcomes": outcomes,
                 "outcomes_sha256": outcomes_digest(outcomes) if outcomes else "",
                 "orbits": orbits, "labelled": labelled,
                 "by_orbit": by_orbit, "spot_checks": spot_checks,
                 "evaluated": evaluated},
        note_key="cert.note.domain_sweep",
    )


def sweep_range_certificate(entries, first_failure, stopped_early,
                            vacuous=None) -> Certificate:
    """One sub-certificate per size. The answer to "from which n does it fail?"

    Each n is verified on its own; what this adds is the ORDER and the claim
    that nothing failed below `first_failure`. With --stop-on-first the sizes
    above it were never run, and that is recorded.
    """
    free = all(e["cert"].get("solver_free") for e in entries if e.get("cert"))
    return Certificate(
        kind="sweep_range", solver_free=bool(free),
        payload={"entries": entries, "first_failure": first_failure,
                 "stopped_early": stopped_early,
                 "sizes": [e["n"] for e in entries],
                 # The sizes whose family is EMPTY, so the statement holds
                 # there by vacuity. Optional, and recomputed by `verify`
                 # from each size's own family.
                 "vacuous": list(vacuous or [])},
        note_key="cert.note.sweep_range",
    )


def core_matrix_certificate(hypotheses, goals, table, subcerts,
                            inconclusive) -> Certificate:
    """One core per goal plus the table they induce."""
    return Certificate(
        kind="core_matrix", solver_free=False,
        payload={"hypotheses": hypotheses, "goals": goals, "table": table,
                 "cores": subcerts, "inconclusive": inconclusive},
        note_key="cert.note.core_matrix",
    )


def shrink_domain_certificate(spec_path, spec_sha256, original, minimal,
                              trace, blocked, steps) -> Certificate:
    """The descent, recorded as indices so it can be replayed exactly."""
    return Certificate(
        kind="shrink_domain", solver_free=True,
        payload={"spec_path": str(spec_path), "spec_sha256": spec_sha256,
                 "original": original, "minimal": minimal, "trace": trace,
                 "blocked": blocked, "steps": steps},
        note_key="cert.note.shrink_domain",
    )


def farkas_certificate(rows, multipliers, constant, strict, nonlinear,
                       base_rows, sorts=None, vacuous=False,
                       derived=None, spec_path="") -> Certificate:
    """Non-negative multipliers that close the system. Checked by arithmetic.

    This is what `linarith` emits, and what `nlinarith` emits once its
    preprocessing rows are counted as hypotheses of their own.
    """
    return Certificate(
        kind="farkas", solver_free=True,
        payload={"rows": rows, "multipliers": multipliers,
                 "constant": constant, "strict": strict,
                 "nonlinear": nonlinear, "base_rows": base_rows,
                 "sorts": sorts or {}, "vacuous": bool(vacuous),
                 "derived": derived or {}, "spec_path": str(spec_path)},
        note_key="cert.note.farkas",
    )



def proof_certificate(theorem_smt2, assumptions, assumptions_smt2, lemmas,
                      step, used, unused, vacuous=False, title="",
                      subject=None, crossings=None) -> Certificate:
    """A proof assembled from lemmas, each with its own certificate.

    What this adds over a pile of certificates in a directory is the LINK: for
    every lemma discharged here, the certificate records that the statement
    used downstream is entailed by what that lemma's certificate actually
    establishes. That is the join a human makes silently, and it is where
    assembled proofs break -- a lemma proved under one hypothesis and then
    used under another.

    Lemmas supplied as an existing certificate are BRIDGES: verified on their
    own, but the step from "these 156 graphs all satisfy P" to a first-order
    formula is a modelling decision no checker can make. They are listed by
    name and reported on every verification.

    And a lemma may be about a DIFFERENT OBJECT from the theorem -- a cone
    where the theorem is about a ring, a graph where it is about a monoid.
    That crossing is where a fact about a computation becomes a fact about the
    mathematics, and it is the step two users independently reported as the
    real risk. certo does not check the map: it requires that one be NAMED,
    records every crossing, and repeats them on each verification. Declaring
    no subjects keeps the old behaviour, because a proof that never mentions
    objects has no levels to cross.
    """
    bridges = [l["name"] for l in lemmas if not l.get("derived")]
    payload = {"title": title, "theorem_smt2": theorem_smt2,
               "assumptions": assumptions,
               "assumptions_smt2": assumptions_smt2,
               "lemmas": lemmas, "step": step,
               "used": used, "unused": unused, "bridges": bridges,
               "vacuous": bool(vacuous)}
    if subject:
        payload["subject"] = list(subject)
    if crossings:
        payload["crossings"] = crossings
    return Certificate(
        kind="proof", solver_free=False, payload=payload,
        note_key="cert.note.proof",
    )



def ball_certificate(describe, backend, prec, lo, hi, claim, spec_path="",
                     spec_sha256="", title="") -> Certificate:
    """A rigorous enclosure, and the claim it settles.

    The enclosure travels as EXACT rationals, so the half that matters -- does
    this interval settle the inequality -- is decided by comparing fractions,
    with no library involved at all. Reproducing the interval needs the spec
    and the same backend, and that half is checked separately and reported
    separately, because it is the half that can go stale.
    """
    return Certificate(
        kind="ball", solver_free=True,
        payload={"describe": describe, "backend": backend, "prec": prec,
                 "lo": str(lo), "hi": str(hi), "claim": list(claim) if claim else None,
                 "spec_path": str(spec_path), "spec_sha256": spec_sha256,
                 "title": title},
        note_key="cert.note.ball",
    )



def induction_certificate(k0, base_upto, step_from, base, step, step_smt2,
                          conclusion, bridge="", title="") -> Certificate:
    """The induction schema, applied, with both halves attached.

    The schema itself is not a solver result and is not pretending to be one.
    What travels is: a certificate per base case, a certificate for the step
    proved with the index FREE, and the two numbers that decide whether the
    chain actually joins up. Those numbers are the part a write-up gets wrong
    and a pile of certificates cannot expose.
    """
    return Certificate(
        kind="induction", solver_free=False,
        payload={"k0": k0, "base_upto": base_upto, "step_from": step_from,
                 "base": base, "step": step, "step_smt2": step_smt2,
                 "conclusion": conclusion, "bridge": bridge, "title": title},
        note_key="cert.note.induction",
    )



def orbit_witnesses_certificate(sweep_cert, witnesses, labelled,
                                title="") -> Certificate:
    """A refuted sweep, quotiented, and one minimal witness per orbit.

    The three steps a combinatorial refutation actually wants -- how many
    counterexamples there are, how many objects that really is, and what the
    smallest version of each looks like -- travel as one artefact instead of
    three files someone has to line up by hand.

    Nothing new is proved here: each part carries its own certificate and
    verification cascades into all of them. What this adds is that they are
    about THE SAME RUN, which a directory of certificates cannot say.
    """
    return Certificate(
        kind="orbit_witnesses", solver_free=False,
        payload={"title": title, "sweep": sweep_cert, "witnesses": witnesses,
                 "labelled": labelled, "orbits": len(witnesses)},
        note_key="cert.note.orbit_witnesses",
    )



def ideal_certificate(variables, equations, claim, cofactors, inconsistent,
                      title="") -> Certificate:
    """`f = sum h_i g_i`, with the cofactors attached.

    Finding them is a Groebner basis computation; checking them is expanding a
    product. That gap is the whole reason this travels as a certificate rather
    than as "the algebra system agreed".

    With `claim` absent the left-hand side is 1, and the certificate refutes
    the system outright -- over the complex numbers, hence over everything
    smaller. It does NOT say a real solution exists when it fails.
    """
    return Certificate(
        kind="ideal", solver_free=True,
        payload={"variables": list(variables), "equations": equations,
                 "claim": claim, "cofactors": cofactors,
                 "inconsistent": bool(inconsistent), "title": title},
        note_key="cert.note.ideal",
    )


def cover_certificate(universe, parts, exact, cliques, multiplicities,
                      part_report=None, max_size=None, title="") -> Certificate:
    """Every element of the universe in exactly one part, and how many parts.

    Checking it is counting, which is why the whole universe and the parts
    travel: a certificate that recorded only the verdict would need whatever
    produced it to still exist, and the point is that it does not.

    `exact` records WHICH claim was made. An at-least cover is a weaker and
    perfectly reasonable thing to certify, and a reader who assumed the
    stronger one would be wrong in the direction that matters.
    """
    return Certificate(
        kind="exact_cover", solver_free=True,
        payload={"universe": universe, "parts": parts,
                 "exact": bool(exact), "cliques": bool(cliques),
                 "multiplicities": multiplicities,
                 "part_report": part_report or [],
                 "max_size": max_size, "size": len(parts), "title": title},
        note_key="cert.note.exact_cover",
    )


def first_entry_certificate(index, prefix, threshold, direction, strict,
                            step_bound=None, window=None,
                            title="") -> Certificate:
    """`k` is the FIRST index where the sequence crosses, and how far it lands.

    Two claims, and the second carries the weight: it crosses at `k`, and it
    had not crossed at any `j < k`. The payload is `a_0 .. a_k` and nothing
    past it, because nothing past it is part of either claim.

    `window` is what a step bound buys: the step before the crossing was on
    the near side, so the crossing overshoots by at most `delta`. Only the
    last step is used for it, and `delta` is re-checked against every step of
    the prefix -- a bound that fails earlier is a bound somebody got wrong.
    """
    payload = {"index": index, "prefix": prefix, "threshold": threshold,
               "direction": direction, "strict": bool(strict), "title": title}
    if step_bound is not None:
        payload["step_bound"] = step_bound
    if window is not None:
        payload["window"] = window
    return Certificate(
        kind="first_entry", solver_free=True, payload=payload,
        note_key="cert.note.first_entry",
    )


def first_moment_certificate(terms, expectation, threshold, relation, counts,
                             concludes, masses=None, title="") -> Certificate:
    """`E[X] < 1`, in exact rationals, and the existence it buys.

    The probabilistic method in one line, and the line is a sum of rationals.
    Done in floating point, `0.9999999` and `1.0000001` have both been written
    down as "less than one"; done here, the sum is re-added on verification
    and compared exactly.

    What the certificate carries is every term, so the sum is re-derivable
    rather than asserted. `concludes` records whether the EXISTENCE statement
    was drawn -- which needs the quantity to be a count, non-negative and
    integer-valued, and the threshold to be one. A mean below one for a
    quantity that could be one half everywhere puts no outcome at zero.
    """
    payload = {"terms": terms, "expectation": expectation,
               "threshold": threshold, "relation": relation,
               "counts": bool(counts), "concludes": bool(concludes),
               "title": title}
    # `masses` present IS what makes this a tails certificate. A separate
    # flag would be a second source of truth, and turning it off would drop
    # the mass check while the rest still verified.
    if masses is not None:
        payload["masses"] = masses
    return Certificate(
        kind="first_moment", solver_free=True, payload=payload,
        note_key="cert.note.first_moment",
    )


def symmetry_reduction_certificate(sense, generators, orbits, system,
                                   quotient, title="") -> Certificate:
    """The quotient program has the same optimum, and here is why.

    "Averaging over the automorphism group, an optimal solution may be assumed
    constant on each orbit" is the sentence, and it is a bridge in every
    write-up that uses it. Its three hypotheses are finite:

        the action permutes the variables
        the constraint set is invariant under every generator
        the objective is invariant

    With those, the feasible region is convex and every image of a feasible
    point is feasible, so the average over the group is feasible; the
    objective is invariant and linear, so the average has the same value; and
    the average is constant on orbits. So an optimal solution constant on
    orbits exists, and the quotient loses nothing.

    Both the original system and the quotient travel, so verification rebuilds
    the quotient rather than believing it -- the same reason a branch-and-bound
    node derives its own linear program.
    """
    return Certificate(
        kind="symmetry_reduction", solver_free=True,
        payload={"sense": sense, "generators": generators, "orbits": orbits,
                 "system": system, "quotient": quotient, "title": title},
        note_key="cert.note.symmetry_reduction",
    )


def parametric_symmetry_certificate(payload, title="") -> Certificate:
    """The symbolic quotient of a family, and the window that tests it.

    TWO LEVELS, and the certificate keeps them apart because they are not the
    same claim.

    SYMBOLIC, wherever the declaration holds: which orbits the quotient has,
    which rows, with what coefficients, and which regimes the row conditions
    cut parameter space into. The objective is the sum of the multiplicities,
    which is what substituting one variable per orbit does -- so it is derived
    here rather than declared, and cannot disagree with them.

    PER INSTANCE, on a finite window: that the declared group really has these
    orbits, that they really have these sizes, and that the quotient the
    averaging argument produces really is the symbolic one evaluated there.

    The second does not become the first by adding points. What it does is
    make the first FALSIFIABLE -- a multiplicity that is wrong, a condition
    off by one, a regime boundary in the wrong place, each shows up as a
    disagreement at some parameter value. The step from the window to the
    region is the multiplicity polynomials' assertion, and `verify` says so
    every time rather than letting it pass as proved.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="parametric_symmetry", solver_free=True, payload=out,
        note_key="cert.note.parametric_symmetry",
    )


def linear_system_certificate(payload, title="") -> Certificate:
    """`A x = b`, and whatever makes the answer checkable.

    The certificate for a solved system is almost embarrassing: it is `x`, and
    checking it is one matrix-vector product. That IS the point -- a number
    from a numerical library is a number to be trusted, while `x` with `A` and
    `b` beside it is a number to be multiplied.

    THE SYSTEM TRAVELS WITH THE ANSWER, so re-checking is against the system
    that was stated rather than the one somebody remembers stating. A solution
    to a slightly different matrix is the failure mode here, and without the
    matrix in the payload it is invisible.

    UNSOLVABLE IS CERTIFIED TOO: `y` with `y.A = 0` and `y.b != 0` turns a
    negative result into two more products. An unsolvable system reported with
    nothing behind it is a claim, not an answer.

    WHAT IT DOES NOT SAY -- and `verify` repeats it every time -- is that the
    solution is NON-NEGATIVE, or over the rationals that it is INTEGRAL. Those
    are different questions, and letting a solved system stand in for either
    is the substitution the warning exists to prevent.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="linear_system", solver_free=True, payload=out,
        note_key="cert.note.linear_system",
    )


def equitable_quotient_certificate(payload, title="") -> Certificate:
    """Two programs with the same attainable values, and why.

    The claim is an EQUIVALENCE, not an agreement between two computed optima.
    `Proj(x)_j = sum over the class of x_C` sends a feasible physical point to
    a feasible quotient point of the same value; `Lift(z)_C = z_j / M_j` sends
    one back; and `Proj(Lift(z)) = z`. Equality of optima follows, and no
    duality is needed to get it.

    WHAT MAKES THE MAPS WORK is regularity in both directions, and the two are
    different quantities that are easy to confuse:

        H_ij   one resource of class i is used by this much of object class j
        B_ij   one object of class j uses this much of resource class i

    Lifting needs H -- every physical row must see the same load -- and the
    quotient's own matrix needs B. Using one where the other belongs builds a
    quotient that is simply wrong, and no comparison of optima inside the
    reduced world catches it. The double count `N_i H_ij = M_j B_ij` ties them
    and travels as a check rather than as a remark.

    WHAT IS NOT CLAIMED: INTEGRALITY. The equivalence is between the
    fractional programs. An integer orbit mass need not lift to integer
    objects, so this is never evidence about an integer program.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="equitable_quotient", solver_free=True, payload=out,
        note_key="cert.note.equitable_quotient",
    )


def toric_cone_certificate(payload, title="") -> Certificate:
    """The local data of a cone, computed rather than assumed.

    An audit of the crepant criterion, written before this existed, took
    `discrepancy == height - 1` and `multiplicity == height` as HYPOTHESES.
    They are the step where a cone becomes a number, and nothing was computing
    them from a cone. Here the generators go in and the numbers come out:
    primitivity, the index of the sublattice, the height functional found by
    an exact solve, and a discrepancy per ray.

    THE LATTICE IS PART OF EVERY ANSWER. The same cell is multiplicity 16 in
    `Z^4` and 1 in the lattice its generators are primitive in, so the payload
    records which one the number is about. Reading a multiplicity without its
    lattice is reading half a sentence.

    WHAT IT DOES NOT SAY: that multiplicity one gives a smooth chart, that
    discrepancy zero gives a crepant modification, that a fibre is SNC or
    reduced. Those are theorems about varieties. certo hands over what they
    consume and stops.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="toric_cone", solver_free=True, payload=out,
        note_key="cert.note.toric_cone",
    )


def capacity_profile_certificate(payload, title="") -> Certificate:
    """A FUNCTION, certified: how an optimum responds to one capacity.

    Every other kind here settles a number or a yes. This settles `f` on a
    whole interval -- concave, piecewise affine, with breakpoints -- from
    finite data, and the reason that is possible is worth carrying next to the
    payload:

      * a dual's feasibility is `A^T y >= c`, which never mentions a capacity,
        so ONE dual bounds every `t` in its segment at once;
      * two sources at a segment's ends attain the whole segment, because
        interpolating them is feasible at the interpolated capacity and its
        value is the interpolation;
      * sorted segments sharing endpoints tile the domain.

    Bound plus attainment plus coverage is equality on `[lo, hi]`.

    IT IS A STATEMENT ABOUT ITS COLUMN SET. Not that the columns are all the
    columns, nor that the rows mean what they are called. If they came from a
    graph, that translation is a separate obligation.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="capacity_profile", solver_free=True, payload=out,
        note_key="cert.note.capacity_profile",
    )


def clique_lp_certificate(out, title="") -> Certificate:
    """An LP over every clique of a graph: the generated support, the exact
    dual of the edge rows, and the pricing search that shows no clique
    outside the support has positive reduced cost. Weak duality does the
    rest; the verifier reruns the search rather than believing it."""
    g = out["graph"]
    pr = out["pricing"]
    payload = {
        "problem": out["problem"],
        "vertices": list(g.labels),
        "edges": [[g.labels[i], g.labels[j]] for i, j in g.edges],
        "min_size": out["min_size"],
        "weight": {"edges": str(out["alpha"]), "vertices": str(out["beta"]),
                   "constant": str(out["gamma"])},
        "rhs": [str(r) for r in out["rhs"]],
        "columns": [{"clique": [g.labels[i] for i in Q], "x": str(x)}
                    for Q, x in out["support"]],
        "dual": [str(v) for v in out["z"]],
        "objective": str(out["objective"]),
        "pricing": {"max_reduced": (None if pr["best"] is None
                                    else str(pr["best"])),
                    "argmax": (None if pr["argmax"] is None
                               else [g.labels[i] for i in pr["argmax"]]),
                    "nodes": pr["nodes"]},
        "rounds": out["rounds"], "generated": out["generated"],
        "title": title,
    }
    return Certificate(kind="clique_lp", solver_free=True, payload=payload,
                       note_key="cert.note.clique_lp")


def affine_semigroup_certificate(payload, title="") -> Certificate:
    """What is finite and checkable about `S = N.a_1 + ... + N.a_k`.

    THE GAP THIS FILLS. `toric_cone` answers questions about the RATIONAL
    cone. A semigroup is the lattice points you can actually reach by adding
    generators, and the difference between the two is exactly where normality
    lives: a point can be in the cone, and in the group, and still not be a
    non-negative integer combination of the generators.

    EVERY CLAIM CARRIES WHAT CHECKS IT. Membership carries coefficients.
    Absence from the cone carries a separating functional -- one vector and
    k+1 dot products, rather than a promise that a search was exhaustive.
    Absence from the SEMIGROUP carries the graded bound that made the search
    finite, so a verifier redoes it rather than believing it.

    WHAT IT NEVER SAYS IS THAT S IS NORMAL. A witness refutes normality and
    nothing here establishes it: that would mean deciding membership for every
    lattice point of the cone, which is what Normaliz is for. `normal` is null
    in the payload on purpose, so a reader of the certificate alone cannot
    mistake an absent witness for a proof.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="affine_semigroup", solver_free=True, payload=out,
        note_key="cert.note.affine_semigroup",
    )


def range_certificate(payload, title="") -> Certificate:
    """The admissible interval of one variable, with the multipliers for each
    end.

    `check --hypotheses-only` exhibits a POINT of the regime. That answers
    whether it is inhabited and nothing else, and the question people have
    next is how far the variable may go. Both ends here are LP duals, so the
    payload carries the non-negative combination of hypotheses that yields the
    bound, and checking one is multiplying out and adding fractions.

    AN EMPTY REGIME IS ITS OWN ANSWER, not an infinite interval. Over an empty
    regime every direction is unbounded, and reading that as "the variable
    ranges over everything" is the permissive-looking mistake; the payload says
    `empty` and the interval prints as such.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="variable_range", solver_free=True, payload=out,
        note_key="cert.note.variable_range",
    )


def dependency_cycle_certificate(payload, title="") -> Certificate:
    """A cycle in a parameter's own dependencies, and the class that closes it.

    The three lines that produce one never mention a cycle. Composing their
    growth CLASSES does, and the composition is finite: one walk of the chain
    and one comparison, both redone during verification.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="dependency_cycle", solver_free=True, payload=out,
        note_key="cert.note.dependency_cycle",
    )


def lean_binding_certificate(payload, title="") -> Certificate:
    """What a certificate assumed, against what a declaration provides.

    Not solver-free: the entailment is a satisfiability question, and it is
    re-asked during verification rather than believed.
    """
    out = dict(payload)
    out["title"] = title
    return Certificate(
        kind="lean_binding", solver_free=False, payload=out,
        note_key="cert.note.lean_binding",
    )


def integer_matrix_certificate(question, matrix, result, title="") -> Certificate:
    """An exact answer about an integer matrix, with the transforms that
    make it checkable by multiplication instead of by elimination.

    `U . A = H` with `U . U_inv = I` says U is unimodular, so A and H have the
    same row lattice; H's shape then gives the rank, and its diagonal gives
    the determinant up to `det(U)`. That last sign is the only quantity not
    settled by a product of integers, and it does not need to be recomputed
    over Z: it is known to be +1 or -1, and those are distinct modulo any odd
    prime.

    Smith carries a second transform on the columns and a diagonal whose
    divisibility chain is checked, which is what makes the invariant factors
    -- and so the torsion of the quotient group -- a finite checkable fact.
    """
    payload = {"question": question, "matrix": matrix, "title": title}
    payload.update(result)
    return Certificate(
        kind="integer_matrix", solver_free=True, payload=payload,
        note_key="cert.note.integer_matrix",
    )


def symmetric_inertia_certificate(question, matrix, S, S_inv, D, witness=None,
                                  title="") -> Certificate:
    """The inertia of a symmetric rational matrix as a congruence: `S A S^T`
    is the diagonal `D`, and `S` times `S_inv` is the identity. Sylvester's
    law makes the signs of `D` the inertia of `A`; the verifier multiplies.
    `witness`, when there is one, is a vector with `x^T A x < 0`."""
    from .inertia import counts

    def ser(M):
        return [[str(x) for x in r] for r in M]

    c = counts(D)
    payload = {
        "question": question, "matrix": ser(matrix), "S": ser(S),
        "S_inv": ser(S_inv), "D": [str(x) for x in D],
        "n_plus": c["n_plus"], "n_minus": c["n_minus"], "n_zero": c["n_zero"],
        "rank": c["n_plus"] + c["n_minus"],
        "psd": c["n_minus"] == 0,
        "pd": c["n_minus"] == 0 and c["n_zero"] == 0,
        "witness": None if witness is None else [str(x) for x in witness],
        "title": title,
    }
    return Certificate(kind="symmetric_inertia", solver_free=True,
                       payload=payload, note_key="cert.note.symmetric_inertia")


def hypothesis_audit_certificate(rows, counts, goal_smt2, hypotheses_smt2,
                                 obligations=(), title="") -> Certificate:
    """Per hypothesis: needed and why, redundant, or not settled.

    `core` says which hypotheses an unsat core NEEDED, which catches a theorem
    stated with slack. This catches the opposite and more expensive mistake --
    a theorem stated TOO STRONGLY, formalised, and only then found to be about
    a smaller class than the paper claims.

    The WITNESS is the content of a `needed` verdict. It says not only that a
    hypothesis matters but HOW, which is what tells somebody whether they
    wrote the right one, and checking it is evaluation rather than search:
    substitute, and the kept hypotheses must hold while the goal must not.

    THE DOMAIN OBLIGATIONS travel with it. Division is total in SMT -- `n/0`
    is a value the solver invents -- so a hypothesis guarding a denominator
    would otherwise read `needed` for a counterexample that is about the
    solver rather than the theorem. Every divisor that could vanish is listed,
    every search is guarded by them, and a hypothesis whose only job was
    holding one up is reported as `domain`: not needed, because the claim does
    not become false, and emphatically not redundant, because removing it does
    not generalise the theorem, it makes the statement meaningless.

    WHAT IT DOES NOT SAY, repeated on every verification: that the hypothesis
    set is MINIMAL. Dropping them one at a time says nothing about dropping
    two, and a pair can be jointly redundant with neither redundant alone.
    """
    payload = {"rows": rows, "counts": counts, "goal_smt2": goal_smt2,
               "hypotheses_smt2": hypotheses_smt2, "title": title}
    if obligations:
        payload["obligations"] = list(obligations)
    return Certificate(
        kind="hypothesis_audit", solver_free=False, payload=payload,
        note_key="cert.note.hypothesis_audit",
    )


def ratio_bound_certificate(parameters, left, right, relation, difference,
                            region=None, title="") -> Certificate:
    """`f/g <= h/k` for every parameter at or above the floor. No solver.

    Clearing the denominators turns it into `h*g - f*k >= 0` on a ray, which
    is the same shift test the parametric bound uses. The step that can go
    wrong is the clearing: multiplying through preserves the direction only
    when both denominators are POSITIVE, so both are checked, and a
    denominator not shown positive is a refusal -- a negative one would flip
    the inequality and make this certificate exactly backwards.

    The difference travels so it can be re-expanded; the denominators travel
    so their positivity can be re-checked. Nothing here is taken on trust from
    the producer, including the arithmetic that built the difference.
    """
    payload = {"parameters": parameters, "left": list(left),
               "right": list(right), "relation": relation,
               "difference": difference, "title": title}
    if region:
        payload["region"] = region
    return Certificate(
        kind="ratio_bound", solver_free=True, payload=payload,
        note_key="cert.note.ratio_bound",
    )


def family_extremum_certificate(value, argmax, primal, dual, bounds, ids,
                                count, title="") -> Certificate:
    """`max over this family = V`. Two claims, and they are not symmetric.

    The winner ATTAINS `V`: an exact primal and dual whose values meet, so its
    optimum IS `V` rather than a bound on it. Every other item is BOUNDED by
    it: a feasible dual with `b.y <= V`, which is weak duality and much less
    work than solving. A dual does not have to be optimal to bound.

    NOTHING STORES AN LP. Each item's program is rebuilt from the spec and the
    item at verification time. Carrying one program per item would be both
    enormous and unchecked -- a dual for a different item's program would fit
    it perfectly, which is the hole a branch-and-bound tree had. So this needs
    the spec to verify, and says so when it does not have it.
    """
    return Certificate(
        kind="family_extremum", solver_free=False,
        payload={"sense": "max", "value": value, "argmax": argmax,
                 "primal": primal, "dual": dual, "bounds": bounds,
                 "ids": ids, "ids_sha256": _digest_of(ids), "count": count,
                 "title": title},
        note_key="cert.note.family_extremum",
    )


def _digest_of(ids) -> str:
    import hashlib

    h = hashlib.sha256()
    for i in ids:
        h.update(str(i).encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def integer_peak_certificate(parameters, variable, objective, argmax, value,
                             region=None, title="") -> Certificate:
    """No integer beats `argmax`, and `argmax` attains `value`. For every p.

    A concave quadratic `q(x) = A x^2 + B x + C` whose coefficients are
    polynomials in the parameters. Moving the origin to the claimed maximiser,
    an integer step `t` changes the objective by `A t^2 + q'(x*) t`, which is
    `<= 0` for every non-zero integer `t` exactly when

        A  <=  q'(x*)  <=  -A.

    So the certificate is `x*`, the coefficients, and those two polynomial
    inequalities -- checked by the same shift the parametric bound uses. No
    floor appears anywhere, which is the point: the floor of a parametric
    expression is not a polynomial and cannot be expanded, and this says the
    same thing without one.

    The bound is attained rather than merely valid, because `x*` is an integer
    -- which is why the certificate refuses a non-integral `argmax` instead of
    taking "it is an integer really" on trust.
    """
    # Everything else -- the leading coefficient, the derivative at `x*`, the
    # two step inequalities, the region multipliers -- is ONE expansion away
    # from these and is recomputed on every verification. Carrying a second
    # copy would put fields in the payload that nothing checks, and a field
    # nothing checks can say anything.
    payload = {"parameters": parameters, "variable": variable,
               "objective": objective, "argmax": argmax, "value": value,
               "title": title}
    if region:
        payload["region"] = region
    return Certificate(
        kind="integer_peak", solver_free=True, payload=payload,
        note_key="cert.note.integer_peak",
    )


def parametric_bound_certificate(parameters, variables, objective,
                                 constraints, dual, bound, rows,
                                 title="", sense="max",
                                 dual_poly=None, region=None, free=None,
                                 claim=None, primal=None, box=None,
                                 box_trees=None) -> Certificate:
    """A bound on `opt(p)` for every p at or above the given floor.

    Weak duality holds symbolically. For a packing -- `max c.x, A x <= b` --
    any `y >= 0` with `A(p)^T y >= c(p)` bounds the optimum from ABOVE. For a
    cover -- `min w.z, M z >= 1` -- any `y >= 0` with `M(p)^T y <= w(p)` bounds
    it from BELOW. Same certificate, one sign apart, and `sense` says which.

    So the whole certificate is `y`, the polynomial data, and -- per column --
    the residual after substituting `p = p0 + u`, whose coefficients are all
    non-negative. Checking it is reading signs off a list.

    `dual_poly` carries `y` exactly. It is a separate field because a cover's
    dual is a packing, which GROWS with the instance and so need not be
    constant; `dual` keeps the readable form, and a certificate written before
    this existed has only the readable form and is read the same way.

    `region` is SCOPE, not content. Each entry means `g(p) >= 0` on the
    instances the bound is claimed for, and nothing here proves it -- the same
    standing as the parameter floors, which also say which instances are meant.
    It exists because the shift test proves non-negativity on a BOX, and a
    branch cut out by a curve is not one. `verify` re-derives the multipliers'
    effect and repeats every declared condition in its warnings, because a
    certificate whose scope is only in the spec file is a certificate nobody
    can read on its own.

    The shift is SUFFICIENT and not necessary. A certificate exists only when
    it succeeds; when it does not, no certificate is emitted, because "this
    route did not work" is not a bound.
    """
    payload = {"parameters": parameters, "variables": list(variables),
               "objective": objective, "constraints": constraints,
               "dual": dual, "bound": bound, "rows": rows, "title": title}
    # Optional, and only written when they say something: the schema is frozen
    # and an old reader must still see exactly what it used to see.
    if sense != "max":
        payload["sense"] = sense
    if dual_poly is not None:
        payload["dual_poly"] = dual_poly
    if region:
        payload["region"] = region
    # 0.17, all optional: variables with no sign, a claimed target, and a
    # primal witness in place of a dual.
    if free:
        payload["free"] = list(free)
    if claim is not None:
        payload["claim"] = claim
    if primal is not None:
        payload["witness"] = "primal"
        payload["primal"] = primal
    if box is not None:
        payload["box"] = box
        if box_trees:
            payload["box_trees"] = box_trees
    return Certificate(
        kind="parametric_bound", solver_free=True, payload=payload,
        note_key=("cert.note.parametric_bound_min" if sense == "min"
                  else "cert.note.parametric_bound"),
    )


def resultant_certificate(variables, eliminated, f, g, resultant, A, B,
                          deg_f, deg_g, lead_f, lead_g, lead_f_constant,
                          lead_g_constant, title="") -> Certificate:
    """`Res(f, g) = A*f + B*g`, with the cofactors attached.

    Computing a resultant is a determinant over a polynomial ring; checking
    one is expanding two products and subtracting. That gap is the reason this
    travels as a certificate: a determinant nobody can check is a number
    somebody has to take on faith.

    `lead_f_constant` and `lead_g_constant` are not decoration. `Res = 0` is
    necessary for a common root always, and SUFFICIENT only over an
    algebraically closed field and only when the leading coefficients in the
    eliminated variable do not both vanish. When they can, the certificate
    still verifies and `verify` says what it no longer licenses.
    """
    return Certificate(
        kind="resultant", solver_free=True,
        payload={"variables": list(variables), "eliminated": eliminated,
                 "f": f, "g": g, "resultant": resultant, "A": A, "B": B,
                 "deg_f": deg_f, "deg_g": deg_g,
                 "lead_f": lead_f, "lead_g": lead_g,
                 "lead_f_constant": bool(lead_f_constant),
                 "lead_g_constant": bool(lead_g_constant),
                 "title": title},
        note_key="cert.note.resultant",
    )


def sos_certificate(variables, poly, terms, basis_size, denom,
                    title="", backend=None) -> Certificate:
    """`p = sum d_i q_i^2` in exact rationals.

    The Gram matrix was found in floating point and is not here: it was the
    search. What is here are rational coefficients and rational linear forms,
    and checking them is multiplying polynomials out.

    `backend` says WHICH search found it -- provenance of the proposal, an
    optional field older readers ignore. The certificate means the same thing
    whichever it was, because the check below is the same.
    """
    payload = {"variables": list(variables), "poly": poly, "terms": terms,
               "squares": len(terms), "basis_size": basis_size,
               "denominator": denom, "title": title}
    if backend is not None:
        payload["backend"] = backend
    return Certificate(
        kind="sos", solver_free=True, payload=payload,
        note_key="cert.note.sos",
    )


def number_certificate(kind, tree, title="") -> Certificate:
    """A Pratt primality tree, or a factorisation whose factors carry one.

    `n.is_prime()` is true, fast and unciteable. This is the same fact with
    the evidence attached, and the evidence is a handful of `pow(a, e, n)`.
    """
    return Certificate(
        kind="number", solver_free=True,
        payload={"question": kind, "tree": tree, "n": tree["n"],
                 "title": title},
        note_key="cert.note.number",
    )



def mixed_design_certificate(assignment, continuous, kinds, system, objective,
                             sense, discrete_gain, conditional, achieved,
                             residual_cert, relaxation_cert, bound, target,
                             globally_optimal, level="conditional_optimum",
                             skeleton_from="CBC", title="") -> Certificate:
    """A discrete skeleton, the exact packing inside it, and what that reaches.

    Three numbers that are not the same number, kept apart on purpose:

      achieved     what this construction attains. Exact, and a genuine LOWER
                   bound on the true optimum, because the thing exists.
      conditional  the best the continuous part can do WITH THIS SKELETON,
                   from the residual LP's exact dual.
      bound        the relaxation over ALL skeletons: an UPPER bound.

    What is certified: the assignment is integral and in range, the full point
    satisfies every original constraint exactly, the residual LP really is the
    original problem with that assignment substituted, and its dual is exact.

    What is NOT certified, unless `achieved` meets `bound`: that this skeleton
    is the best one. The search was CBC and nothing here re-does it. For an
    existence proof that is the right amount to claim -- exhibiting a
    construction that reaches the target is the whole job.
    """
    return Certificate(
        kind="mixed_design", solver_free=True,
        payload={"assignment": assignment, "continuous": continuous,
                 "kinds": kinds, "system": system, "objective": objective,
                 "sense": sense, "discrete_gain": discrete_gain,
                 "conditional": conditional, "achieved": achieved,
                 "residual": residual_cert, "relaxation": relaxation_cert,
                 "bound": bound, "target": target,
                 "globally_optimal": bool(globally_optimal),
                 "level": level, "skeleton_from": skeleton_from,
                 "title": title},
        note_key="cert.note.mixed_design",
    )



def gap_certificate(fractional, integral, mu, nu, gap, tight, level,
                    title="") -> Certificate:
    """The integrality gap of a packing, with both sides attached.

    `nu` against `mu*` used to be two runs someone subtracted afterwards --
    two artefacts, and two chances to line up the wrong pair. Here they travel
    together and verification checks they are about THE SAME packing, which a
    folder of certificates cannot say.

    `tight` names the resources carrying positive load in the fractional dual:
    the obstruction, in the language of the problem rather than of the LP.
    """
    return Certificate(
        kind="gap", solver_free=False,
        payload={"fractional": fractional, "integral": integral,
                 "mu": mu, "nu": nu, "gap": gap, "tight": tight,
                 "level": level, "title": title},
        note_key="cert.note.gap",
    )



def farkas_ray_certificate(A, b, y, names) -> Certificate:
    """`Ax <= b, x >= 0` has no solution, and here is why.

    A ray `y >= 0` with `A^T y >= 0` and `b.y < 0`. For any feasible x this
    gives `0 <= (A^T y).x = y.(Ax) <= y.b < 0`, so there is no feasible x.
    Checking it is three dot products in exact rationals -- no solver, and no
    trusting the one that said "infeasible".
    """
    return Certificate(
        kind="farkas_ray", solver_free=True,
        payload={"A": A, "b": b, "y": y, "names": names},
        note_key="cert.note.farkas_ray",
    )


def _tree_is_exact(nodes, incumbent_cert) -> bool:
    """Does every node close by arithmetic alone, and the incumbent with it?"""
    if not incumbent_cert or not incumbent_cert.get("solver_free"):
        return False
    for n in nodes:
        why = n.get("why")
        if why == "branch":
            continue
        if why == "infeasible":
            if not n.get("ray"):
                return False
            continue
        if n.get("dual") is None or n.get("bound") is None:
            return False
    return True


def branch_bound_certificate(incumbent, incumbent_cert, nodes, order, sense,
                             title="", original_sense=None,
                             original_optimum=None, system=None) -> Certificate:
    """The optimum, and the account of every design that was not taken.

    To say "no design does better" you have to account for all of them, and
    each one has to be accounted for BY SOMETHING ABOUT IT. Two halves, and
    the second is the one that is easy to lose:

      COVERAGE. A branching node's children are all present, checked node by
      node. A tree with a missing child is a proof that some designs were
      never looked at, and it reads exactly like a complete one.

      IDENTITY. Each node's linear program is DERIVED from the root system and
      that node's own fixings, and the dual it carries is checked against the
      derived program. It is not stored: a certificate for a node's relaxation
      is a valid certificate for some linear program and says nothing about
      which node it belongs to, so storing one lets a cheap subtree's
      certificate close an expensive subtree. A tree with two node
      certificates exchanged used to verify.

    `system` carries the root problem once, which is where the identity check
    gets its second operand -- and, incidentally, most of the size: what a
    node holds is its fixings, its bound and the two vectors that close it.

    A certificate written before `system` existed has nodes that cannot be
    tied to anything, and `verify` says so in a warning rather than quietly
    checking less than it appears to.
    """
    return Certificate(
        kind="branch_bound",
        # Every node closes by exact rational arithmetic over a system derived
        # from the root, and so does the incumbent. Computed, not declared:
        # a node that could not be closed exactly never reaches here.
        solver_free=bool(system) and _tree_is_exact(nodes, incumbent_cert),
        payload={"incumbent": incumbent, "incumbent_cert": incumbent_cert,
                 "nodes": nodes, "order": order, "sense": sense,
                 "system": system,
                 # Optional, which the frozen schema allows. `sense` is what
                 # was SEARCHED; these say what was ASKED, when the two differ
                 # because a minimisation was negated to get here.
                 "original_sense": original_sense or sense,
                 "original_optimum": original_optimum
                 if original_optimum is not None else incumbent,
                 "title": title},
        note_key="cert.note.branch_bound",
    )



def order_certificate(laurent, orders, var, terms, collected, degree, verdict,
                      expect, cancelled, title="", derived=None) -> Certificate:
    """The exponent of `var`, and the substitution that produced it.

    The Laurent polynomial travels, so re-checking this needs neither z3 nor
    the spec: substitute the orders, collect, read the leading exponent. Pure
    exact arithmetic.

    What it certifies is the EXPONENT, not the constant in front of it. `≍`
    hides a factor, so a Theta(1) term with a coefficient of 1e-9 may be
    perfectly fine in practice. What the certificate says is that it does not
    shrink with `var`, and it says only that.
    """
    return Certificate(
        kind="asymptotic", solver_free=True,
        payload={"laurent": laurent, "orders": orders, "var": var,
                 "terms": terms, "collected": collected, "degree": degree,
                 "verdict": verdict, "expect": expect, "cancelled": cancelled,
                 # Present only when the exponents were DERIVED: the relations
                 # travel so `verify` re-solves them instead of trusting the
                 # numbers they produced.
                 "derived": derived,
                 "title": title},
        note_key="cert.note.asymptotic",
    )


def graph_set_certificate(n: int, filters: list, g6: list) -> Certificate:
    h = hashlib.sha256("\n".join(sorted(g6)).encode()).hexdigest()
    return Certificate(
        kind="graph_set",
        solver_free=True,
        payload={
            "n": n,
            "filters": filters,
            "count": len(g6),
            "sha256": h,
            "graph6": g6,
        },
        note_key="cert.note.graph_set",
    )



# ---------------------------------------------------------------------------
# how much a sweep actually establishes
# ---------------------------------------------------------------------------
#
# Three levels, and the distance between them is the whole point. A sweep
# whose predicate returns a bare `bool` establishes far less than one whose
# predicate returns certificates, and the difference used to be invisible:
# both printed "FINITE CASE VERIFIED". These names exist so it cannot be.

CERTIFIED = "certified"        # every evaluation carries its own certificate
REPRODUCIBLE = "reproducible"  # no certificates, but the run can be replayed
RECORDED = "recorded"          # neither: only the domain and its hash
NO_PREDICATE = "no_predicate"  # a calibration run: nothing to certify


def outcome_code(out) -> str:
    """One character per item. T true, F false, ? inconclusive, E error.

    Lower case means INFERRED from an orbit representative rather than
    computed -- `--by-orbit`. A reader can see at a glance how much of a
    verdict vector was actually run.
    """
    if getattr(out, "errored", False):
        return "E"
    if out.ok is None:
        return "?"
    return "T" if out.ok else "F"


def outcomes_digest(codes: str) -> str:
    """The whole verdict vector in 64 hex characters.

    Storing the vector itself would be megabytes on a large sweep and would
    add nothing: on a mismatch the verifier holds both vectors anyway and can
    name the first item that disagrees.
    """
    return hashlib.sha256(codes.encode()).hexdigest()


def sweep_strength(payload: dict, spec_replayable: bool) -> str:
    """What this certificate establishes about the PREDICATE, right now.

    Deliberately computed rather than stored: `reproducible` depends on the
    spec still being there, which is true at issue time and may not be true at
    verification time. A stored label would quietly become a lie.
    """
    ev = payload.get("evaluations", 0)
    if ev and payload.get("certified", 0) >= ev:
        return CERTIFIED
    if payload.get("outcomes_sha256") and spec_replayable:
        return REPRODUCIBLE
    return RECORDED


def _spec_from(cert):
    """The spec that produced a certificate, if it is still the same file."""
    prov = cert.provenance or {}
    sp, want = prov.get("spec_path"), prov.get("spec_sha256")
    if not sp:
        return None, "no_path"
    p = Path(sp)
    if not p.exists():
        return None, "gone"
    if want and hashlib.sha256(p.read_bytes()).hexdigest() != want:
        return None, "changed"
    return p, ""


# ---------------------------------------------------------------------------
# verificacion
# ---------------------------------------------------------------------------

def _replay(cert, limits, kind):
    """Re-run the predicate and compare the verdict vector.

    This is the honest middle ground between "we checked every evaluation" and
    "we checked nothing about the predicate". It does NOT verify the predicate
    -- it verifies that running it again gives the same answers, which makes
    the sweep reproducible rather than merely recorded. The difference is
    named everywhere it is reported.

    Returns (ok, detail) with ok=None when the replay could not be done at
    all, so that "not checked" never renders as "checked and fine".
    """
    import time

    from .limits import Limits

    p = cert.payload
    want = p.get("outcomes_sha256")
    if not want:
        return None, t("verify.sweep.replay.no_vector")

    path, why = _spec_from(cert)
    if path is None:
        return None, t("verify.sweep.replay." + (why if why else "no_path"))

    lim = limits or Limits()
    t0 = time.perf_counter()
    from .spec import load_spec

    spec = load_spec(path)

    if kind == "sweep":
        from .engines.graphsearch import _evaluate, orbit_codes
        from .graphs import Graph

        items = [Graph.from_graph6(s) for s in p.get("family_graph6", [])]
        ids = list(p.get("family_graph6", []))
        if p.get("by_orbit"):
            from . import orbits as orb

            groups = orb.build(spec, items, ids)
            if groups is None:
                return False, t("verify.sweep.replay.no_symmetry")
            got = "".join(orbit_codes(spec, items, groups)[1])
            if outcomes_digest(got) == want:
                return True, t("verify.sweep.replay.agrees", n=len(got))
            old = p.get("outcomes", "")
            where = next((i for i, c in enumerate(got)
                          if i < len(old) and c != old[i]), 0)
            return False, t("verify.sweep.replay.differs",
                            item=ids[where] if where < len(ids) else "?",
                            index=where)
    else:
        from .engines.domain import _evaluate

        items = spec.enumerate()
        ids = [spec.id_of(i) for i in items]
        if ids != list(p.get("ids", [])):
            return False, t("verify.sweep.replay.domain_moved")

        if p.get("by_orbit"):
            # Reproduce the INFERENCE, not a full evaluation: a --by-orbit run
            # never computed the non-representatives, so re-computing them here
            # would disagree with the stored vector by construction.
            from . import orbits as orb
            from .engines.domain import orbit_codes

            groups = orb.build(spec, items, ids)
            if groups is None:
                return False, t("verify.sweep.replay.no_symmetry")
            got = "".join(orbit_codes(spec, items, groups)[1])
            if outcomes_digest(got) == want:
                return True, t("verify.sweep.replay.agrees", n=len(got))
            old = p.get("outcomes", "")
            where = next((i for i, c in enumerate(got)
                          if i < len(old) and c != old[i]), 0)
            return False, t("verify.sweep.replay.differs",
                            item=ids[where] if where < len(ids) else "?",
                            index=where)

    codes = []
    for item in items:
        codes.append(outcome_code(_evaluate(spec, item)))
        if (time.perf_counter() - t0) * 1000 > lim.timeout_ms:
            return None, t("verify.sweep.replay.timeout", done=len(codes),
                           total=len(items))

    got = "".join(codes)
    if outcomes_digest(got) == want:
        return True, t("verify.sweep.replay.agrees", n=len(got))

    # Both vectors are in hand, so say WHICH item moved rather than "differs".
    old = p.get("outcomes", "")
    where = next((i for i, c in enumerate(got) if i < len(old) and c != old[i]),
                 min(len(got), len(old)))
    name = ids[where] if where < len(ids) else "?"
    return False, t("verify.sweep.replay.differs", item=name, index=where)



def verify(cert, limits=None) -> VerifyReport:
    """Re-check a certificate. Takes a `Certificate` or its serialised dict.

    THE DICT IS ACCEPTED ON PURPOSE. A user's revalidation adapter read
    certificates back from JSON and passed the dict straight here; what came
    back was `AttributeError: 'dict' object has no attribute 'kind'`, which
    names neither the problem nor the fix, in the one function an adapter is
    certain to call. A dict that round-tripped through JSON is unambiguously a
    serialised certificate, so it is deserialised rather than refused: the
    mistake stops being possible instead of getting a better error message.
    Anything else is refused by name, saying what would have worked.
    """
    if isinstance(cert, dict):
        try:
            cert = Certificate.from_dict(cert)
        except Exception as e:  # noqa: BLE001
            return VerifyReport(
                False, "?", False,
                detail=t("verify.bad_dict", message=e),
            )
    elif not isinstance(cert, Certificate):
        raise TypeError(t("verify.wrong_type", got=type(cert).__name__))

    fn = VERIFIERS.get(cert.kind)
    if fn is None:
        return VerifyReport(
            False, cert.kind, cert.solver_free,
            detail=t("verify.unknown_kind", kind=cert.kind),
        )
    try:
        rep = fn(cert, limits)
        rep.warnings = _provenance_warnings(cert) + list(rep.warnings)
        return rep
    except Exception as e:  # noqa: BLE001
        return VerifyReport(
            False, cert.kind, cert.solver_free,
            detail=t("verify.failed", type=type(e).__name__, message=e),
        )



# --- the link between a lemma and its certificate --------------------------


def obligations_of(sub: dict):
    """The formulas a sub-certificate establishes are JOINTLY UNSATISFIABLE.

    This is the only thing `compose` needs from a sub-certificate, and it is
    what makes the link checkable: if the negated statement entails these, and
    these are contradictory, the statement is valid. Returns None for kinds
    that establish something which is not a formula set at all -- a finite
    sweep, a DRAT proof over propositional variables -- and those become
    bridges rather than silent assumptions.
    """
    import z3

    kind, p = sub.get("kind"), sub.get("payload", {})
    if kind == "unsat_core":
        return list(z3.parse_smt2_string(p["core_smt2"]))
    if kind == "farkas":
        from fractions import Fraction

        from . import linarith

        rows = linarith.parse_rows(p["rows"])
        lams = [Fraction(x) for x in p["multipliers"]]
        sorts = p.get("sorts") or {}
        return [linarith.row_to_z3(poly, rel, sorts)
                for (_, poly, rel), lam in zip(rows, lams) if lam > 0]
    return None


def entails(negated_statement, obligations, limits) -> bool:
    """Does `not statement` imply everything the certificate closed?

    Together with the sub-certificate's own verification (those obligations
    are contradictory) this gives: `not statement` is unsatisfiable, i.e. the
    statement is valid. Checking the implication rather than syntactic
    equality is what lets a certificate be reused for any statement it is
    strong enough to support.
    """
    import z3

    from .limits import Limits

    s = z3.Solver()
    (limits or Limits()).apply_to(s)
    s.add(negated_statement)
    s.add(z3.Not(z3.And(*obligations)) if len(obligations) > 1
          else z3.Not(obligations[0]))
    return s.check() == z3.unsat


def _parse_one(smt2: str):
    """An smt2 blob back into a single formula."""
    import z3

    fs = list(z3.parse_smt2_string(smt2))
    if not fs:
        return z3.BoolVal(True)
    return fs[0] if len(fs) == 1 else z3.And(*fs)


def _verify_proof(cert, limits) -> VerifyReport:
    import z3

    p = cert.payload
    checks, warnings = [], []
    statements = []

    for lem in p["lemmas"]:
        name = lem["name"]
        phi = _parse_one(lem["statement_smt2"])
        statements.append(phi)
        sub = lem.get("cert")
        if sub is None:
            checks.append((t("verify.proof.lemma", name=name), False,
                           t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        checks.append((t("verify.proof.lemma", name=name), rep.ok,
                       "{}: {}".format(sub["kind"], rep.detail)))
        warnings.extend("{}: {}".format(name, w) for w in rep.warnings)

        if not lem.get("derived"):
            warnings.append(t("verify.proof.bridge", name=name,
                              why=lem.get("bridge") or sub["kind"]))
            continue
        obl = obligations_of(sub)
        linked = bool(obl) and entails(z3.Not(phi), obl, limits)
        checks.append((t("verify.proof.link", name=name), linked,
                       t("verify.proof.link_detail", n=len(obl or []))))

    # EVERY CROSSING, REPEATED. A lemma about a different object reached the
    # theorem by a map certo did not check and could not -- what it checked is
    # that the map was NAMED. A reader has to be told that on every
    # verification, the way bridges are, or the crossing is visible only to
    # whoever wrote the spec.
    crossings = p.get("crossings") or []
    if p.get("subject"):
        warnings.append(t("verify.proof.subject", kind=p["subject"][0],
                          id=p["subject"][1]))
    if crossings:
        warnings.append(t("verify.proof.crossings", n=len(crossings),
                          names="; ".join(
                              "{} ({}: {} -> {})".format(
                                  c["lemma"], c["map"], c["from"][0],
                                  (c["to"] or ["?"])[0])
                              for c in crossings[:4])))

    # The final step: the lemmas and the theorem's own hypotheses close it.
    ambient = list(z3.parse_smt2_string(p["assumptions_smt2"])) \
        if p.get("assumptions_smt2") else []
    theorem = _parse_one(p["theorem_smt2"])
    step = p.get("step")
    if step is None:
        checks.append((t("verify.proof.step"), False, t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(step), limits)
        checks.append((t("verify.proof.step"), rep.ok, rep.detail))
        premises = statements + ambient
        neg = z3.And(*(premises + [z3.Not(theorem)])) if premises \
            else z3.Not(theorem)
        obl = obligations_of(step)
        linked = bool(obl) and entails(neg, obl, limits)
        checks.append((t("verify.proof.step_link"), linked,
                       t("verify.proof.link_detail", n=len(obl or []))))
        # Nothing may enter the final step that was not declared.
        declared = set(p["assumptions"]) | {l["name"] for l in p["lemmas"]}
        smuggled = [n for n in step.get("payload", {}).get("names", [])
                    if n != "__goal__" and n not in declared]
        checks.append((t("verify.proof.declared"), not smuggled,
                       ", ".join(smuggled)))

    if p.get("vacuous"):
        warnings.append(t("verify.proof.vacuous"))
    if p.get("unused"):
        warnings.append(t("verify.proof.unused",
                          names=", ".join(p["unused"])))

    return VerifyReport(
        all(c[1] for c in checks), "proof", False, checks=checks,
        warnings=warnings,
        detail=t("verify.proof.detail", lemmas=len(p["lemmas"]),
                 bridges=len(p.get("bridges", []))),
    )



def _verify_ball(cert, limits) -> VerifyReport:
    """Two halves, and they fail differently.

    Whether the interval settles the claim is pure rational arithmetic and
    always runs. Whether the interval is the right interval needs the spec and
    the same backend; when that cannot be redone here it is reported as
    unchecked rather than quietly passed.
    """
    from fractions import Fraction

    from . import numerics

    p = cert.payload
    lo, hi = Fraction(p["lo"]), Fraction(p["hi"])
    claim = tuple(p["claim"]) if p.get("claim") else None
    checks, warnings = [], []

    checks.append((t("verify.ball.ordered"), lo <= hi,
                   "[{}, {}]".format(float(lo), float(hi))))
    settled = numerics.settle(claim, lo, hi)
    checks.append((t("verify.ball.settles"), settled is True,
                   numerics.render(claim) or t("verify.ball.no_claim")))

    path = Path(p.get("spec_path") or "")
    if not p.get("spec_path") or not path.exists():
        warnings.append(t("verify.ball.no_spec", path=p.get("spec_path") or "-"))
        return VerifyReport(
            all(c[1] for c in checks), "ball", True, checks=checks,
            warnings=warnings,
            detail=t("verify.ball.detail", prec=p["prec"], backend=p["backend"]))

    try:
        from .spec import load_spec

        sp = load_spec(path)
        rig = numerics.Rig(int(p["prec"]), p["backend"])
        got_lo, got_hi = sp.value(rig).enclosure()
        inside = lo <= got_lo and got_hi <= hi
        checks.append((t("verify.ball.reproduced"), inside,
                       "[{}, {}]".format(float(got_lo), float(got_hi))))
    except Exception as e:  # noqa: BLE001
        warnings.append(t("verify.ball.not_redone", reason=str(e)))

    return VerifyReport(
        all(c[1] for c in checks), "ball", True, checks=checks,
        warnings=warnings,
        detail=t("verify.ball.detail", prec=p["prec"], backend=p["backend"]))



def _verify_induction(cert, limits) -> VerifyReport:
    import z3

    p = cert.payload
    checks, warnings = [], []
    k0, upto, step_from = p["k0"], p["base_upto"], p["step_from"]

    # --- the chain joins up ------------------------------------------------
    ks = [b["k"] for b in p["base"]]
    want = list(range(k0, upto + 1))
    checks.append((t("verify.induction.covered"), ks == want,
                   t("verify.induction.range", k0=k0, upto=upto,
                     got=len(ks))))
    checks.append((t("verify.induction.joins"), step_from <= upto,
                   t("verify.induction.step_from", step=step_from, upto=upto)))

    # --- every base case ---------------------------------------------------
    for b in p["base"]:
        sub = b.get("cert")
        label = t("verify.induction.base", k=b["k"])
        if sub is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        checks.append((label, rep.ok, "{}: {}".format(sub["kind"], rep.detail)))
        warnings.extend("k={}: {}".format(b["k"], w) for w in rep.warnings)
        if not b.get("derived") and p.get("bridge"):
            warnings.append(t("verify.induction.bridge", k=b["k"],
                              why=p["bridge"]))

    # --- the step ----------------------------------------------------------
    step = p.get("step")
    if step is None:
        checks.append((t("verify.induction.step"), False,
                       t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(step), limits)
        checks.append((t("verify.induction.step"), rep.ok, rep.detail))
        phi = _parse_one(p["step_smt2"])
        obl = obligations_of(step)
        linked = bool(obl) and entails(z3.Not(phi), obl, limits)
        checks.append((t("verify.induction.step_link"), linked,
                       t("verify.proof.link_detail", n=len(obl or []))))

    warnings.append(t("verify.induction.schema"))
    return VerifyReport(
        all(c[1] for c in checks), "induction", False, checks=checks,
        warnings=warnings,
        detail=t("verify.induction.detail", n=len(ks), k0=k0, upto=upto),
    )



def _verify_orbit_witnesses(cert, limits) -> VerifyReport:
    p = cert.payload
    checks, warnings, free = [], [], True

    sub = p.get("sweep")
    if sub is None:
        checks.append((t("verify.witness.sweep"), False,
                       t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(sub), limits)
        checks.append((t("verify.witness.sweep"), rep.ok, rep.detail))
        warnings.extend(rep.warnings)
        free = free and rep.solver_free

        # The representatives minimised here must be the representatives the
        # sweep found. Otherwise this is three certificates about three runs.
        want = {row["representative"] for row in (sub["payload"].get("orbits") or [])}
        got = {w["representative"] for w in p["witnesses"]}
        checks.append((t("verify.witness.same_run"), got <= want,
                       t("verify.witness.stray",
                         names=", ".join(sorted(got - want)[:3]) or "-")))

    for w in p["witnesses"]:
        label = t("verify.witness.one", rep=w["representative"])
        wc = w.get("cert")
        if wc is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(wc), limits)
        checks.append((label, rep.ok, "{} -> {}".format(w["minimal"], rep.detail)))
        warnings.extend("{}: {}".format(w["representative"], x)
                        for x in rep.warnings)
        free = free and rep.solver_free

    return VerifyReport(
        all(c[1] for c in checks), "orbit_witnesses", free, checks=checks,
        warnings=warnings,
        detail=t("verify.witness.detail", labelled=p["labelled"],
                 orbits=p["orbits"]),
    )



def _verify_exact_cover(cert, limits) -> VerifyReport:
    """Recount from the universe and the parts. Nothing here is believed."""
    from .cover import check

    p = cert.payload
    out = check(p["universe"], p["parts"], exact=p.get("exact", True))

    checks = [
        (t("verify.cover.covered"), not out["missed"],
         t("verify.cover.missed", n=len(out["missed"]),
           names=", ".join(map(str, out["missed"][:4])) or "-")),
        (t("verify.cover.foreign"), not out["foreign"],
         t("verify.cover.foreign_detail", n=len(out["foreign"]))),
    ]
    if p.get("exact", True):
        checks.append((t("verify.cover.once"), not out["doubled"],
                       t("verify.cover.doubled", n=len(out["doubled"]),
                         names=", ".join(map(str, out["doubled"][:4])) or "-")))
    checks.append((t("verify.cover.size"), out["parts"] == p["size"],
                   t("verify.cover.size_detail", n=out["parts"],
                     declared=p["size"])))

    # A clique partition's parts have to BE cliques, and that is a statement
    # about the graph, not about the cover. Re-derived rather than trusted.
    if p.get("cliques"):
        from .cover import _key, edges_of

        present = {_key(e) for e in p["universe"]}
        bad = []
        for entry in p.get("part_report") or []:
            own = edges_of(entry["vertices"])
            if any(_key(e) not in present for e in own):
                bad.append(entry["vertices"])
            elif len(own) != entry["edges"]:
                bad.append(entry["vertices"])
        checks.append((t("verify.cover.cliques"), not bad,
                       t("verify.cover.not_cliques", n=len(bad))))

    ok = all(c[1] for c in checks)
    return VerifyReport(
        ok, "exact_cover", True, checks=checks,
        warnings=[t("verify.cover.not_minimum")],
        method_key="verify.cover.method",
        detail=t("verify.cover.detail", parts=p["size"],
                 n=out["universe"],
                 kind=t("verify.cover.exactly" if p.get("exact", True)
                        else "verify.cover.atleast")),
    )


def _verify_first_entry(cert, limits) -> VerifyReport:
    """Re-find the crossing in the stored prefix. Exact rationals, no solver."""
    from . import entry

    p = cert.payload
    if p["direction"] not in ("up", "down"):
        return VerifyReport(False, "first_entry", True,
                            detail=t("entry.direction", got=p["direction"]))
    got = entry.check(p)
    checks = [
        (t("verify.entry.crosses"), got["crosses"], got["value"]),
        (t("verify.entry.earliest"), got["earliest"],
         t("verify.entry.early", names=", ".join(got["early"]) or "-")),
        (t("verify.entry.indexed"), got["indexed"], str(p["index"])),
    ]
    if p.get("step_bound") is not None:
        checks.append((t("verify.entry.steps"), got["steps"],
                       str(p["step_bound"])))
        checks.append((t("verify.entry.window"), got["window_ok"],
                       str(p.get("window") or "-")))

    warnings = [t("verify.entry.scope", n=len(p["prefix"]))]
    return VerifyReport(
        all(c[1] for c in checks), "first_entry", True, checks=checks,
        warnings=warnings, method_key="verify.entry.method",
        detail=t("verify.entry.detail_window" if p.get("window")
                 else "verify.entry.detail", index=p["index"],
                 value=got["value"], threshold=str(p["threshold"]),
                 window=str(p.get("window") or "-")),
    )


def _verify_first_moment(cert, limits) -> VerifyReport:
    """Re-add the terms, re-derive the masses, re-make the comparison."""
    from fractions import Fraction

    p = cert.payload
    values = [Fraction(v) for _n, v in p["terms"]]
    checks = []

    out = [n for (n, _v), v in zip(p["terms"], values) if v < 0 or v > 1]
    checks.append((t("verify.moment.probabilities"), not out,
                   t("verify.moment.offenders", n=len(values),
                     names=", ".join(map(str, out[:3])) or "-")))

    if p.get("masses") is not None:
        from .moment import masses_from_tails

        got = masses_from_tails(values)
        want = [Fraction(m) for m in p.get("masses") or []]
        negative = [i for i, m in enumerate(got) if m < 0]
        checks.append((t("verify.moment.masses"),
                       got == want and not negative,
                       t("verify.moment.sum_to_one",
                         total=str(sum(got, Fraction(0))))))

    total = sum(values, Fraction(0))
    declared = Fraction(p["expectation"])
    checks.append((t("verify.moment.expectation"), total == declared,
                   str(declared)))

    threshold = Fraction(p["threshold"])
    if p["relation"] not in ("<", "<="):
        checks.append((t("verify.moment.relation"), False, str(p["relation"])))
        return VerifyReport(False, "first_moment", True, checks=checks,
                            detail=t("moment.relation", rel=p["relation"]))
    holds = total < threshold if p["relation"] == "<" else total <= threshold
    checks.append((t("verify.moment.comparison"), holds,
                   "{} {} {}".format(str(total), p["relation"],
                                     str(threshold))))

    # The existence conclusion is drawn only under conditions that are
    # re-checked here, not taken from the flag.
    earned = bool(p["counts"] and threshold == 1 and p["relation"] == "<"
                  and holds and not out)
    checks.append((t("verify.moment.conclusion"), earned == p["concludes"],
                   t("verify.moment.earned" if earned
                     else "verify.moment.bound_only")))

    warnings = [t("verify.moment.scope")]
    if not p["counts"]:
        warnings.append(t("verify.moment.not_a_count"))
    return VerifyReport(
        all(c[1] for c in checks), "first_moment", True, checks=checks,
        warnings=warnings, method_key="verify.moment.method",
        detail=t("verify.moment.detail_exists" if p["concludes"]
                 else "verify.moment.detail", value=str(declared),
                 rel=p["relation"], threshold=str(threshold)),
    )


def _verify_symmetry_reduction(cert, limits) -> VerifyReport:
    """Re-check the three hypotheses, and rebuild the quotient."""
    from . import symmetry, tree

    p = cert.payload
    root = tree.spec_of(p["system"])
    checks = []

    bad = []
    for name, perm in sorted(p["generators"].items()):
        try:
            symmetry.check_generator(root, name, perm)
        except symmetry.NotSymmetric as e:
            bad.append("{}: {}".format(name, e))
    checks.append((t("verify.symmetry.generators"), not bad,
                   t("verify.symmetry.offenders",
                     n=len(p["generators"]),
                     names="; ".join(bad[:2]) or "-")))

    got = symmetry.orbits(list(root.var_names), p["generators"])
    declared = [sorted(o) for o in p["orbits"]]
    checks.append((t("verify.symmetry.orbits"),
                   sorted(got) == sorted(declared),
                   t("verify.symmetry.counts", n=len(declared),
                     vars=len(root.var_names))))

    # The quotient is REBUILT, not believed.
    want = tree.system_of(symmetry.quotient(root, got))
    checks.append((t("verify.symmetry.quotient"),
                   _same_system(want, p["quotient"]),
                   t("verify.symmetry.reduced",
                     v=len(want["var_names"]), r=len(want["cons"]))))

    return VerifyReport(
        all(c[1] for c in checks), "symmetry_reduction", True, checks=checks,
        warnings=[t("verify.symmetry.scope")],
        method_key="verify.symmetry.method",
        detail=t("verify.symmetry.detail", vars=len(root.var_names),
                 orbits=len(declared)),
    )


def _same_system(a, b) -> bool:
    """Two programs as data, compared where order does not matter."""
    if a["sense"] != b["sense"] or set(a["var_names"]) != set(b["var_names"]):
        return False
    if a["obj"] != b["obj"] or a["bounds"] != b["bounds"]:
        return False
    key = lambda c: (tuple(sorted(c[1].items())), c[2], c[3])  # noqa: E731
    return sorted(map(key, a["cons"])) == sorted(map(key, b["cons"]))


def _verify_parametric_symmetry(cert, limits) -> VerifyReport:
    """Re-derive the symbolic side; the per-instance side was recorded."""
    from fractions import Fraction

    from . import paramsym
    from .polynomials import Poly

    p = cert.payload
    ring = tuple(p["parameters"])
    spec = _paramsym_view(p, ring)
    checks = []

    # 1. the multiplicities give the orbit sizes recorded at each point
    bad = []
    for row in p["points"]:
        want = {k: Fraction(v) for k, v in
                paramsym.sizes_at(spec, row["point"]).items()}
        got = {k: Fraction(str(v)) for k, v in row["sizes"].items()}
        if want != got:
            bad.append(paramsym._point_text(row["point"]))
    checks.append((t("verify.paramsym.orbits"), not bad,
                   t("verify.paramsym.sizes", n=len(p["points"]),
                     orbits=len(p["orbits"]), params=", ".join(ring))))

    # 2. the rows recorded present are the ones the conditions admit
    wrong = []
    for row in p["points"]:
        if paramsym.live_rows(spec, row["point"]) != list(row["rows"]):
            wrong.append(paramsym._point_text(row["point"]))
    checks.append((t("verify.paramsym.rows"), not wrong,
                   t("verify.paramsym.regimes", n=len(p["regimes"]),
                     names=", ".join(sorted(p["regimes"]))[:80])))

    # 3. the multiplicities account for every object. The count recorded at
    # each point came from the INSTANCE, which was built from the objects, so
    # this is the multiplicities against an independent number -- comparing
    # the polynomial sum against itself would be a check with no content.
    total = Poly(ring)
    for data in p["orbits"].values():
        total = total + Poly.parse(ring, data)
    short = []
    for row in p["points"]:
        recorded = row.get("objects")
        if recorded is None:
            continue
        if paramsym.evaluate(total, row["point"]) != Fraction(recorded):
            short.append(paramsym._point_text(row["point"]))
    checks.append((t("verify.paramsym.objects"),
                   not short and total == Poly.parse(ring, p["objects"]),
                   t("verify.paramsym.total", total=str(total),
                     params=", ".join(ring))))

    # 4. every window point agreed with the family when it was run
    agreed = sum(1 for row in p["points"] if row["ok"])
    checks.append((t("verify.paramsym.agreement"),
                   agreed == len(p["points"]),
                   t("verify.paramsym.points", ok=agreed, n=len(p["points"]))))

    return VerifyReport(
        all(c[1] for c in checks), "parametric_symmetry", True, checks=checks,
        warnings=[t("verify.paramsym.scope", n=len(p["points"])),
                  t("verify.paramsym.window_bridge", n=len(p["points"]))],
        method_key="verify.paramsym.method",
        detail=t("verify.paramsym.detail", params=", ".join(ring),
                 orbits=len(p["orbits"]), regimes=len(p["regimes"]),
                 n=len(p["points"])),
    )


def _paramsym_view(payload, ring):
    """The declaration, rebuilt from the payload so the checks can be redone.

    Deliberately NOT the original spec object: what verification is allowed to
    use is what travelled, and `instance` -- a Python callable -- did not.
    """
    import types

    from .polynomials import Poly

    return types.SimpleNamespace(
        parameters=ring,
        orbits={n: Poly.parse(ring, d) for n, d in payload["orbits"].items()},
        sense=payload["sense"],
        rows=[(r["name"],
               {o: Poly.parse(ring, d) for o, d in r["coefficients"].items()},
               r["sense"], Poly.parse(ring, r["rhs"]),
               [Poly.parse(ring, g) for g in r["when"]])
              for r in payload["rows"]],
        instance=None, window=(), title=payload.get("title", ""),
    )


def _verify_linear_system(cert, limits) -> VerifyReport:
    """One matrix-vector product, and the arithmetic around it."""
    from fractions import Fraction

    from . import linsolve

    p = cert.payload
    A = [[Fraction(v) for v in row] for row in p["matrix"]]
    b = [Fraction(v) for v in p["rhs"]]
    m = p["columns"]
    checks = []

    if p["status"] == linsolve.NONE:
        # WHICH argument is required is decided by the DOMAIN, not by which
        # evidence happens to be in the payload. Reading it off the payload
        # let a certificate claiming "no rational solution" verify by an
        # INTEGER argument once the witness was deleted -- and those are
        # different claims, the integer one being strictly weaker.
        if p["domain"] == "rational":
            # `y.A = 0` and `y.b != 0`: the negative result, made checkable.
            y = [Fraction(v) for v in (p.get("witness") or [])]
            ok = False
            if y and len(y) == len(A):
                cols = list(zip(*A))
                ok = (all(sum((a * c for a, c in zip(y, col)), Fraction(0)) == 0
                          for col in cols)
                      and sum((a * c for a, c in zip(y, b)), Fraction(0)) != 0)
            checks.append((t("verify.solve.witness"), ok,
                           t("verify.solve.no_solution")))
        else:
            # Over Z there is no such row vector -- `2x = 1` has no rational
            # obstruction at all -- so the decision rests on the invariant
            # factors, and it is redone rather than believed.
            checks.append((t("verify.solve.integer_blocked"),
                           _integer_unsolvable(A, b),
                           t("verify.solve.blocked",
                             values=", ".join(map(str, p.get("invariants")
                                                  or [])) or "-")))
        return VerifyReport(
            all(c[1] for c in checks), "linear_system", True, checks=checks,
            warnings=[t("verify.solve.scope")],
            method_key="verify.solve.method",
            detail=t("verify.solve.none", rows=len(A), cols=m))

    x = [Fraction(v) for v in p["solution"]]
    checks.append((t("verify.solve.satisfies"),
                   len(x) == m and linsolve.multiply(A, x) == b,
                   t("verify.solve.product", rows=len(A), cols=m)))

    if p["domain"] == "integer":
        checks.append((t("verify.solve.integral"),
                       all(v.denominator == 1 for v in x),
                       t("verify.solve.entries", n=len(x))))

    kernel = [[Fraction(v) for v in k] for k in p["kernel"]]
    zero = [Fraction(0)] * len(A)
    checks.append((t("verify.solve.kernel"),
                   all(linsolve.multiply(A, k) == zero for k in kernel),
                   t("verify.solve.kernel_size", n=len(kernel))))

    # The rank is DERIVED, not read: a payload claiming a smaller rank would
    # be claiming a bigger solution set than the system has.
    rank = _rational_rank(A)
    ok_rank = rank == p["rank"]
    if p["domain"] == "rational":
        ok_rank = ok_rank and len(kernel) == m - rank
    checks.append((t("verify.solve.rank"), ok_rank,
                   t("verify.solve.rank_is", r=rank, cols=m)))

    warnings = [t("verify.solve.scope")]
    if p["status"] == linsolve.MANY:
        warnings.append(t("verify.solve.many", n=len(kernel)))
    return VerifyReport(
        all(c[1] for c in checks), "linear_system", True, checks=checks,
        warnings=warnings, method_key="verify.solve.method",
        detail=t("verify.solve.detail", status=p["status"], rows=len(A),
                 cols=m, domain=p["domain"]),
    )


def _rational_rank(A) -> int:
    from fractions import Fraction

    from . import linsolve

    _aug, _T, pivots = linsolve._rref(A, [Fraction(0)] * len(A))
    return len(pivots)


def _integer_unsolvable(A, b) -> bool:
    """Redo the Smith decision rather than take the payload's word."""
    from . import linsolve

    try:
        return linsolve.solve_integer(A, b)["status"] == linsolve.NONE
    except linsolve.NotSolvable:
        return False


def _verify_equitable_quotient(cert, limits) -> VerifyReport:
    """Rebuild the quotient from the class data, and redo the double count."""
    from fractions import Fraction

    from . import equitable, tree

    p = cert.payload
    N = {k: int(v) for k, v in p["N"].items()}
    M = {k: int(v) for k, v in p["M"].items()}
    B = {tuple(k.split("|", 1)): Fraction(v) for k, v in p["B"].items()}
    H = {tuple(k.split("|", 1)): Fraction(v) for k, v in p["H"].items()}
    checks = []

    # 1. the double count. Both regularities were established against the
    # physical matrix when this was produced; that they COHERE is arithmetic,
    # and it is what catches one of them having been used as the other.
    off = [(i, j) for (i, j) in set(B) | set(H)
           if N[i] * H.get((i, j), Fraction(0))
           != M[j] * B.get((i, j), Fraction(0))]
    checks.append((t("verify.quotient.double_count"), not off,
                   t("verify.quotient.identities",
                     n=len(set(B) | set(H)),
                     bad=", ".join("{}|{}".format(*x) for x in off[:2]) or "-")))

    # 2. the quotient is REBUILT from B, N, the capacities and the weights,
    # not read from the payload.
    data = {"rows": {i: [None] * n for i, n in N.items()},
            "columns": {j: [None] * m for j, m in M.items()},
            "B": B, "N": N, "M": M,
            "capacities": {i: Fraction(v)
                           for i, v in p["capacities"].items()},
            "weights": {j: Fraction(v) for j, v in p["weights"].items()},
            "senses": p["senses"],
            "bounds": {j: tuple(v) if v else None
                       for j, v in (p.get("bounds") or {}).items()}}
    for j in data["columns"]:
        data["bounds"].setdefault(j, None)
    want = equitable.quotient(_sense_holder(p["sense"]), data)
    checks.append((t("verify.quotient.rebuilt"),
                   _same_system(tree.system_of(want), p["quotient"]),
                   t("verify.quotient.shape",
                     rows=len(N), cols=len(M),
                     prows=p["physical_rows"], pcols=p["physical_columns"])))

    # 3. `Proj(Lift(z)) = z` is an identity about the fibre sizes, and a
    # class of size zero would make lifting a division by nothing.
    empty = sorted(j for j, m in M.items() if m <= 0)
    checks.append((t("verify.quotient.roundtrip"),
                   not empty and not p.get("roundtrip_failures"),
                   t("verify.quotient.fibres", n=len(M),
                     bad=", ".join(empty[:3]) or "-")))

    return VerifyReport(
        all(c[1] for c in checks), "equitable_quotient", True, checks=checks,
        warnings=[t("verify.quotient.scope"),
                  t("verify.quotient.integrality")],
        method_key="verify.quotient.method",
        detail=t("verify.quotient.detail", rows=len(N), cols=len(M),
                 prows=p["physical_rows"], pcols=p["physical_columns"]),
    )


class _sense_holder:
    """The two fields `equitable.quotient` reads off the physical program."""

    def __init__(self, sense):
        self.sense = sense
        self.title = ""


def _verify_toric_cone(cert, limits) -> VerifyReport:
    """Redo every number from the generators: none of it needs a solver."""
    from fractions import Fraction

    from . import toric

    p = cert.payload
    rays = {n: list(map(int, v)) for n, v in p["rays"].items()}
    order = list(p["order"])
    basis = p.get("lattice")
    checks = []

    # 1. the multiplicity, in the lattice the payload says it is about
    try:
        mult = toric.multiplicity(rays, order, basis)
        ok = str(mult["value"]) == str(p["multiplicity"])
    except toric.NotToric:
        # No multiplicity is a legitimate answer -- a non-simplicial cone has
        # none in this sense -- and the certificate has to have SAID so.
        ok = p.get("multiplicity") is None
    checks.append((t("verify.toric.multiplicity"), ok,
                   t("verify.toric.index", value=str(p["multiplicity"]),
                     where=p.get("multiplicity_in", "?"))))

    # 2. primitivity, per generator, in that same lattice -- and the relative
    # matrix comes out of the same coordinates, so it is recomputed here
    # rather than read back. A stored matrix nobody recomputes is a matrix
    # anybody can edit, and this one is what a change of basis is built from.
    bad, recomputed = [], []
    for name in order:
        coords = toric.in_lattice(rays[name], basis)
        recomputed.append(None if coords is None
                          else [Fraction(c) for c in coords])
        got = None if coords is None else int(toric.content(
            [Fraction(c).numerator for c in coords]))
        if got != p["primitive"].get(name):
            bad.append(name)
    checks.append((t("verify.toric.primitive"), not bad,
                   t("verify.toric.contents",
                     n=sum(1 for v in p["primitive"].values() if v == 1),
                     total=len(order))))

    rel = p.get("relative")
    if rel is not None:
        want = (None if any(r is None for r in recomputed)
                else [[str(c) for c in row] for row in recomputed])
        checks.append((t("verify.toric.relative"), rel.get("matrix") == want,
                       t("verify.toric.relative_detail",
                         rows=len(rel.get("matrix") or []),
                         cols=len((rel.get("matrix") or [[]])[0]))))

    # 3. the height functional, and the pairing it has to satisfy
    u = p.get("height_functional")
    if u is None:
        checks.append((t("verify.toric.no_height"),
                       toric.height_functional(rays, order) is None,
                       t("verify.toric.height_absent")))
    else:
        vec = [Fraction(v) for v in u]
        ones = all(toric.pairing(vec, rays[n]) == 1 for n in order)
        checks.append((t("verify.toric.height"), ones,
                       t("verify.toric.height_is",
                         values=", ".join(u[:4]))))

        # 4. every discrepancy is the pairing minus one, recomputed
        wrong = [n for n in order
                 if str(toric.pairing(vec, rays[n]) - 1)
                 != str(p["discrepancies"].get(n))]
        for name, entry in (p.get("subdivision") or {}).items():
            if "discrepancy" in entry:
                got = toric.pairing(vec, [int(c) for c in entry["coords"]]) - 1
                if str(got) != str(entry["discrepancy"]):
                    wrong.append(name)
        checks.append((t("verify.toric.discrepancy"), not wrong,
                       t("verify.toric.discrepancies",
                         n=len(p["discrepancies"]) + len(p.get("subdivision")
                                                         or {}),
                         bad=", ".join(wrong[:3]) or "-")))

    return VerifyReport(
        all(c[1] for c in checks), "toric_cone", True, checks=checks,
        warnings=[t("verify.toric.scope"), t("verify.toric.lattice",
                                             where=p.get("multiplicity_in",
                                                         "?"))],
        method_key="verify.toric.method",
        detail=t("verify.toric.detail", n=len(order),
                 dim=p["dimension"], mult=str(p["multiplicity"])),
    )


def _verify_capacity_profile(cert, limits) -> VerifyReport:
    """Redo the whole profile from the columns. No solver, and no belief.

    The payload carries duals and sources; both are re-checked against the
    columns, the segment arithmetic is recomputed, and coverage is re-derived.
    A profile that no longer holds is refused, and so is one whose stated
    piecewise form disagrees with what its own duals give.
    """
    from types import SimpleNamespace

    from . import profile as pr

    p = cert.payload
    rebuilt = SimpleNamespace(
        columns=p["columns"], gain=p["gain"], capacity=p["capacity"],
        parameter=p["parameter"],
        domain=(p["domain"]["lo"], p["domain"]["hi"]),
        segments=[{"from": s["from"], "to": s["to"], "dual": s["dual"]}
                  for s in p["segments"]],
        sources={at: e["mass"] for at, e in (p.get("sources") or {}).items()},
        title="")
    try:
        got = pr.certify(rebuilt)
    except pr.NotAProfile as e:
        return VerifyReport(False, "capacity_profile", True,
                            detail=str(e))

    checks = [
        (t("verify.profile.dual"),
         all(f["why"] not in ("dual_infeasible", "negative_price")
             for f in got["failures"]),
         t("verify.profile.columns", n=len(p["columns"]),
           s=len(p["segments"]))),
        (t("verify.profile.sources"),
         all(f["why"] != "source_infeasible" for f in got["failures"]),
         t("verify.profile.at", n=len(p.get("sources") or {}))),
        (t("verify.profile.meet"),
         all(f["why"] not in ("bound_and_source_disagree", "no_source_at")
             for f in got["failures"]),
         t("verify.profile.equality")),
        (t("verify.profile.cover"),
         all(f["why"] != "not_covered" for f in got["failures"]),
         t("verify.profile.domain", lo=p["domain"]["lo"],
           hi=p["domain"]["hi"])),
        (t("verify.profile.concave"),
         all(f["why"] != "not_concave" for f in got["failures"]),
         t("verify.profile.slopes",
           values=", ".join(s["beta"] for s in p["segments"][:4]))),
        # And the stated shape has to be the shape the duals actually give.
        (t("verify.profile.stated"),
         got["piecewise"] == p["piecewise"] and got["holds"]
         and p.get("holds") is True,
         t("verify.profile.pieces", n=len(p["piecewise"]))),
        # THE BOOKKEEPING, recomputed. Each of these was found by the
        # adversarial suite: a derived list that nobody re-derives, and a
        # source whose own `at` need not match the capacity it is filed under.
        # Both are edits that leave every other number looking right.
        (t("verify.profile.bookkeeping"),
         got["breakpoints"] == p.get("breakpoints")
         and all(e.get("at") == at
                 for at, e in (p.get("sources") or {}).items()),
         t("verify.profile.derived", n=len(p.get("breakpoints") or []))),
    ]

    return VerifyReport(
        all(c[1] for c in checks), "capacity_profile", True, checks=checks,
        warnings=[t("verify.profile.scope")],
        method_key="verify.profile.method",
        detail=t("verify.profile.detail", param=p["parameter"],
                 lo=p["domain"]["lo"], hi=p["domain"]["hi"],
                 n=len(p["segments"])),
    )


def _zero_combination(A, c) -> bool:
    """Non-negative integers, not all zero, with `sum c_i a_i = 0`."""
    try:
        c = [int(x) for x in c]
    except (TypeError, ValueError):
        return False
    if len(c) != len(A) or any(x < 0 for x in c) or not any(c):
        return False
    return all(sum(c[j] * A[j][r] for j in range(len(A))) == 0
               for r in range(len(A[0]) if A else 0))


def _verify_clique_lp(cert, limits) -> VerifyReport:
    """The support, the dual and the pricing search, all recomputed."""
    from . import colgen

    p = cert.payload
    try:
        rows = colgen.check(p)
    except (colgen.NotACliqueLP, KeyError, TypeError, ValueError,
            ZeroDivisionError) as e:
        return VerifyReport(False, "clique_lp", True, checks=[(
            t("verify.colgen.readable"), False, "{}: {}".format(
                type(e).__name__, e))])
    labels = {"shape": "verify.colgen.shape",
              "columns": "verify.colgen.columns",
              "primal": "verify.colgen.primal",
              "objective": "verify.colgen.objective",
              "dual_sign": "verify.colgen.dual_sign",
              "strong": "verify.colgen.strong",
              "pricing": "verify.colgen.pricing"}
    checks = [(t(labels[k]), ok, str(detail)) for k, ok, detail in rows]
    return VerifyReport(
        all(c[1] for c in checks), "clique_lp", True, checks=checks,
        warnings=[t("verify.colgen.scope")],
        method_key="verify.colgen.method",
        detail=t("verify.colgen.detail", n=len(p.get("vertices") or []),
                 m=len(p.get("edges") or []), problem=p.get("problem")),
    )


def _verify_affine_semigroup(cert, limits) -> VerifyReport:
    """Redo every claim from the generators. None of it needs a solver.

    The asymmetry worth knowing about: a POSITIVE membership claim is checked
    by one multiplication, and a NEGATIVE one is checked by redoing the search
    the certificate says was exhaustive. The second costs what the original
    cost -- which is the price of a negative that means anything.
    """
    from fractions import Fraction

    from . import semigroup as sg

    p = cert.payload
    order = list(p["order"])
    gens = {n: list(map(int, v)) for n, v in p["generators"].items()}
    A = [gens[n] for n in order]
    checks = []

    # 1. the grading, which is what makes every search below terminate
    u = p.get("grading")
    wit = p.get("not_pointed_witness")
    if u is None:
        # Not pointed is a claim and is checked like one: non-negative
        # integers, not all zero, combining the generators to zero. A
        # certificate from before 0.17 says False with no witness; it is
        # accepted, and the warning says what was never shown.
        pointed = p.get("pointed")
        if wit is not None:
            ok = pointed is False and _zero_combination(A, wit)
            detail = t("verify.semigroup.not_pointed_is",
                       values=", ".join(map(str, wit[:6])))
        else:
            ok = pointed in (None, False)
            detail = t("verify.semigroup.no_grading" if pointed is False
                       else "verify.semigroup.pointed_undecided")
        checks.append((t("verify.semigroup.grading"), ok, detail))
        vec = None
    else:
        vec = [Fraction(x) for x in u]
        ok = bool(A) and all(sg.dot(vec, a) >= 1 for a in A)
        checks.append((t("verify.semigroup.grading"), ok,
                       t("verify.semigroup.grading_is",
                         values=", ".join(map(str, u[:4])))))

    # 2. every coefficient vector is redone by arithmetic
    bad = []
    for name, e in sorted((p.get("points") or {}).items()):
        v = [int(x) for x in e["point"]]
        cone = e.get("cone_coefficients")
        if cone is not None:
            lam = [Fraction(x) for x in cone]
            if any(c < 0 for c in lam) or not _combines(A, lam, v):
                bad.append(name)
        grp = e.get("group_coefficients")
        if grp is not None:
            if not _combines(A, [Fraction(c) for c in grp], v):
                bad.append(name)
        sgc = e.get("semigroup_coefficients")
        if sgc is not None:
            if (any(int(c) < 0 for c in sgc)
                    or not _combines(A, [Fraction(c) for c in sgc], v)):
                bad.append(name)
    checks.append((t("verify.semigroup.coefficients"), not bad,
                   t("verify.semigroup.points", n=len(p.get("points") or {}),
                     bad=", ".join(sorted(set(bad))[:3]) or "-")))

    # 3. every separating functional actually separates
    unsep = []
    for name, e in sorted((p.get("points") or {}).items()):
        y = e.get("separating")
        if y is None:
            continue
        v = [int(x) for x in e["point"]]
        if not (all(sg.dot(y, a) <= 0 for a in A) and sg.dot(y, v) > 0):
            unsep.append(name)
    checks.append((t("verify.semigroup.separating"), not unsep,
                   t("verify.semigroup.separators",
                     n=sum(1 for e in (p.get("points") or {}).values()
                           if e.get("separating")),
                     bad=", ".join(unsep[:3]) or "-")))

    # 4. THE NEGATIVES, redone rather than believed. A point the certificate
    # says is not in the semigroup is searched for again, under the bound the
    # certificate itself states.
    wrong = []
    if vec is not None:
        for name, e in sorted((p.get("points") or {}).items()):
            if e.get("in_semigroup") is not False:
                continue
            got = sg.in_semigroup(A, [int(x) for x in e["point"]], vec)
            if got.get("coefficients") is not None or got.get("gave_up"):
                wrong.append(name)
    checks.append((t("verify.semigroup.absence"), not wrong,
                   t("verify.semigroup.absences",
                     n=sum(1 for e in (p.get("points") or {}).values()
                           if e.get("in_semigroup") is False),
                     bad=", ".join(wrong[:3]) or "-")))

    # 5. a refutation of normality is the three parts together, or it is not
    # a refutation
    forged = [n for n, e in sorted((p.get("points") or {}).items())
              if e.get("refutes_normality")
              and not (e.get("in_cone") and e.get("in_group")
                       and e.get("in_semigroup") is False)]
    checks.append((t("verify.semigroup.witness"), not forged,
                   t("verify.semigroup.witnesses",
                     n=len(p.get("normality_witnesses") or []),
                     bad=", ".join(forged[:3]) or "-")))

    # 6. normality is never asserted, and a payload claiming it is refused
    checks.append((t("verify.semigroup.never_normal"),
                   p.get("normal") is None,
                   t("verify.semigroup.scope_note")))

    # 7. THE SUMMARIES, recomputed from the parts they summarise. Every one of
    # these was found by the adversarial suite: each is a field that states a
    # conclusion, and a stated conclusion nothing recomputes is a field anyone
    # can edit. `pointed` is the existence of the grading, `minimal` is the
    # emptiness of `redundant`, and the normality summary is the set of points
    # that carry all three parts of a refutation.
    want_w = sorted(n for n, e in (p.get("points") or {}).items()
                    if e.get("refutes_normality"))
    summaries = [
        ((p.get("pointed") is True) if u is not None
         else (p.get("pointed") is not True), "pointed"),
        # a grading and a zero combination cannot both be right
        (u is None or wit is None, "not_pointed_witness"),
        (p.get("dimension") == (len(A[0]) if A else 0), "dimension"),
        (p.get("rank") == sg._rank(A) if A else True, "rank"),
        (sorted(p.get("normality_witnesses") or []) == want_w, "witnesses"),
        (bool(p.get("not_normal")) == bool(want_w), "not_normal"),
        (p.get("minimal") is (None if u is None
                              else not p.get("redundant")), "minimal"),
    ]
    if u is not None:
        want_d = {n: str(sg.dot(vec, gens[n])) for n in order}
        summaries.append(((p.get("degrees") or {}) == want_d, "degrees"))
    off = [name for ok, name in summaries if not ok]
    checks.append((t("verify.semigroup.summaries"), not off,
                   t("verify.semigroup.summaries_off",
                     bad=", ".join(off[:4]) or "-")))

    # 8. every generator the payload calls redundant really is reachable from
    # the others, and no generator it leaves out is.
    wrong_r = []
    if u is not None:
        claimed = dict(p.get("redundant") or {})
        for i, name in enumerate(order):
            others = [a for j, a in enumerate(A) if j != i]
            if not others:
                continue
            got = sg.in_semigroup(others, gens[name], vec)
            reachable = got.get("coefficients") is not None
            if reachable != (name in claimed):
                wrong_r.append(name)
    checks.append((t("verify.semigroup.redundancy"), not wrong_r,
                   t("verify.semigroup.redundancies",
                     n=len(p.get("redundant") or {}),
                     bad=", ".join(wrong_r[:3]) or "-")))

    # 9. A PROPOSED minimal generating set, decided again. This is the one
    # claim here that is settled rather than merely refuted, so the verifier
    # cannot lean on a witness: it redoes all three questions.
    hb = p.get("hilbert")
    if hb is not None and u is not None:
        pairs = [(n, [int(x) for x in e["element"]])
                 for n, e in sorted((hb.get("elements") or {}).items())]
        want = sg.check_hilbert(A, pairs, vec, gen_names=order)
        same = (want["is_minimal_generating_set"]
                == hb.get("is_minimal_generating_set")
                and want["decided"] == hb.get("decided")
                and want["generates"] == hb.get("generates")
                and sorted(want["why_not"]) == sorted(hb.get("why_not") or [])
                and sorted(want["unreachable_generators"])
                == sorted(hb.get("unreachable_generators") or []))
        # And each element's own two answers, not only the summary.
        for name, got in want["elements"].items():
            claimed = (hb.get("elements") or {}).get(name) or {}
            if (got.get("in_semigroup") != claimed.get("in_semigroup")
                    or got.get("irreducible") != claimed.get("irreducible")):
                same = False
        checks.append((t("verify.semigroup.hilbert"), same,
                       t("verify.semigroup.hilbert_is",
                         n=len(pairs),
                         verdict=str(hb.get("is_minimal_generating_set")))))

    warnings = [t("verify.semigroup.scope")]
    if u is None and wit is None and p.get("pointed") is False:
        warnings.append(t("verify.semigroup.legacy_not_pointed"))
    return VerifyReport(
        all(c[1] for c in checks), "affine_semigroup", True, checks=checks,
        warnings=warnings,
        method_key="verify.semigroup.method",
        detail=t("verify.semigroup.detail", n=len(order),
                 dim=p.get("dimension"), rank=p.get("rank"),
                 witnesses=len(p.get("normality_witnesses") or [])),
    )


def _combines(A, coeffs, v) -> bool:
    """Does `sum coeffs[i] A[i]` equal `v`? One multiplication per entry."""
    from fractions import Fraction

    if len(coeffs) != len(A):
        return False
    for i in range(len(v)):
        got = sum((Fraction(c) * Fraction(A[j][i])
                   for j, c in enumerate(coeffs)), Fraction(0))
        if got != Fraction(v[i]):
            return False
    return True


def _verify_variable_range(cert, limits) -> VerifyReport:
    """Redo both ends from the rows: multipliers are checked, never believed."""
    from . import rangebound

    p = cert.payload
    got = rangebound.check(p)
    checks = []
    for side, key in (("upper", "verify.varrange.upper"),
                      ("lower", "verify.varrange.lower")):
        end, res = p[side], got[side]
        if end["bound"] is None:
            # A refusal has to say what is missing. "no bound in this
            # direction" told a reader nothing about WHY the check failed,
            # which is half of what a failed check is for.
            checks.append((t(key), res["ok"],
                           t("verify.varrange.open", why=end.get("why", "?"))
                           if res["ok"] else
                           t("verify.varrange.unproven",
                             reason=res.get("reason", "?"))))
        else:
            checks.append((t(key), res["ok"],
                           t("verify.varrange.combines",
                             value=end["bound"],
                             rows=", ".join(sorted(end["multipliers"]))[:48]
                             or "-")))

    warnings = [t("verify.varrange.regime_only")]
    if p.get("empty"):
        warnings.append(t("verify.varrange.empty_scope"))
    for side in ("lower", "upper"):
        if p[side].get("strict"):
            warnings.append(t("verify.varrange.strict", side=side))

    return VerifyReport(
        all(c[1] for c in checks), "variable_range", True, checks=checks,
        warnings=warnings, method_key="verify.varrange.method",
        detail=t("verify.varrange.detail", var=p["variable"],
                 interval=p["interval"]),
    )


def _verify_dependency_cycle(cert, limits) -> VerifyReport:
    """Redo every composition and the closing comparison from the steps."""
    from . import cycles

    p = cert.payload
    got = cycles.check(p)
    c = p["closes"]
    checks = [
        (t("verify.cycle.steps"), got["steps_ok"],
         t("verify.cycle.recomposed", n=len(p["steps"]),
           bad=", ".join(got["bad"][:3]) or "-")),
        (t("verify.cycle.comparison"), got["comparison_ok"],
         t("verify.cycle.compared", left=c["left"], rel=c["rel"],
           right=c["right"], cmp=got["comparison"])),
        (t("verify.cycle.verdict"), got["empty_ok"],
         t("verify.cycle.empty" if p["empty"] else "verify.cycle.open")),
    ]
    warnings = [t("verify.cycle.declared_classes")]
    if not p["empty"]:
        warnings.append(t("verify.cycle.not_refuted", why=p.get("why") or "-"))
    return VerifyReport(
        all(x[1] for x in checks), "dependency_cycle", True, checks=checks,
        warnings=warnings, method_key="verify.cycle.method",
        detail=t("verify.cycle.detail",
                 cycle=" -> ".join(p["cycle"]), empty=str(p["empty"])),
    )


def _verify_lean_binding(cert, limits) -> VerifyReport:
    """Re-ask the entailment from the formulas the payload carries."""
    from . import binding

    p = cert.payload
    got = binding.check(p, limits)
    checks = [
        (t("verify.bind.entails"), got["agrees"],
         t("verify.bind.covers" if got["covers"] else "verify.bind.gap",
           name=p["discharges"], decl=p["declaration"] or "-")),
    ]
    # The certificate this binding is ABOUT, when it travelled. Without it the
    # payload named a path and nothing else: a binding pointing at a file that
    # does not exist, of a kind it never was, verified exactly like an honest
    # one. Optional, so a binding written before this carries one check fewer
    # rather than failing.
    src = p.get("source")
    if isinstance(src, dict):
        try:
            inner = Certificate.from_dict(src)
            sub = verify(inner, limits)
        except (KeyError, TypeError, ValueError):
            inner, sub = None, None
        # The key is `spec_sha256`, which is what a certificate's provenance
        # calls it -- `binding` normalises it to `sha256` on the way in, and
        # reading the normalised name here found nothing and failed the
        # honest case. A check that rejects the truthful artefact is worse
        # than no check: it teaches people to ignore the one that fires.
        prov = (src.get("provenance") or {})
        recorded = p.get("spec") or {}
        agrees = (
            inner is not None and sub is not None and sub.ok
            and src.get("kind") == p.get("certificate_kind")
            and (not recorded.get("sha256_then")
                 or prov.get("spec_sha256") == recorded["sha256_then"])
        )
        checks.append((
            t("verify.bind.source"), bool(agrees),
            t("verify.bind.source_detail",
              kind=str(src.get("kind")), digest=(inner.digest() if inner
                                                 else "-"))))

    warnings = [t("verify.bind.bridge", decl=p["declaration"] or "-")]
    if p["spec"].get("stale"):
        warnings.append(t("verify.bind.stale", path=p["spec"]["path"]))
    if not p["covers"]:
        warnings.append(t("verify.bind.does_not_cover", name=p["discharges"]))
    return VerifyReport(
        all(x[1] for x in checks), "lean_binding", False, checks=checks,
        warnings=warnings, method_key="verify.bind.method",
        detail=t("verify.bind.detail", decl=p["declaration"] or "-",
                 name=p["discharges"], covers=str(p["covers"])),
    )


def _verify_symmetric_inertia(cert, limits) -> VerifyReport:
    """Two rational products and a diagonal. Nothing is re-eliminated."""
    from fractions import Fraction

    from . import inertia as inr

    p = cert.payload
    checks = []
    try:
        A = inr.parse(p["matrix"])
        S = [[Fraction(x) for x in r] for r in p["S"]]
        Si = [[Fraction(x) for x in r] for r in p["S_inv"]]
        D = [Fraction(x) for x in p["D"]]
        n = len(A)
        shaped = (len(S) == len(Si) == len(D) == n
                  and all(len(r) == n for r in S + Si))
    except (inr.NotSymmetric, KeyError, TypeError, ValueError,
            ZeroDivisionError):
        return VerifyReport(False, "symmetric_inertia", True,
                            checks=[(t("verify.inertia.readable"), False,
                                     t("verify.inertia.unreadable"))])
    checks.append((t("verify.inertia.readable"), shaped,
                   t("verify.inertia.shape", n=n)))
    if shaped:
        got = inr.check(A, S, Si, D)
        checks.append((t("verify.inertia.invertible"), got["invertible"],
                       t("verify.inertia.inverse", n=n)))
        checks.append((t("verify.inertia.congruent"), got["congruent"],
                       t("verify.inertia.equation")))
    # The counts and every summary of them, recomputed from D: each is a
    # field that states a conclusion, and a stated conclusion nothing
    # recomputes is a field anyone can edit.
    c = inr.counts(D)
    want = dict(c, rank=c["n_plus"] + c["n_minus"], psd=c["n_minus"] == 0,
                pd=c["n_minus"] == 0 and c["n_zero"] == 0)
    off = [k for k, v in want.items() if p.get(k) != v]
    checks.append((t("verify.inertia.counts"), not off,
                   t("verify.inertia.counts_are", plus=c["n_plus"],
                     minus=c["n_minus"], zero=c["n_zero"],
                     bad=", ".join(off) or "-")))
    # The refutation of PSD, on its own: one quadratic form.
    w = p.get("witness")
    if w is not None or not want["psd"]:
        ok = False
        if w is not None:
            try:
                x = [Fraction(v) for v in w]
                ok = len(x) == n and inr.quadratic(A, x) < 0
            except (TypeError, ValueError, ZeroDivisionError):
                ok = False
        checks.append((t("verify.inertia.witness"), ok,
                       t("verify.inertia.witness_is")))
    return VerifyReport(
        all(ch[1] for ch in checks), "symmetric_inertia", True, checks=checks,
        warnings=[t("verify.inertia.scope")],
        method_key="verify.inertia.method",
        detail=t("verify.inertia.detail", n=n),
    )


def _verify_integer_matrix(cert, limits) -> VerifyReport:
    """Every claim as integer multiplication, and the one sign as a modulus."""
    from . import lattice

    p = cert.payload
    A = lattice.parse(p["matrix"])
    n, m = lattice.shape(A)
    smith = p["question"] == "smith"
    checks = []

    U, U_inv = lattice.parse(p["u"]), lattice.parse(p["u_inv"])
    checks.append((t("verify.lattice.unimodular"),
                   lattice.is_identity(lattice.multiply(U, U_inv))
                   and lattice.is_identity(lattice.multiply(U_inv, U)),
                   t("verify.lattice.inverse", n=lattice.shape(U)[0])))

    sign = lattice.unimodular_sign(U)
    if smith:
        V, V_inv = lattice.parse(p["v"]), lattice.parse(p["v_inv"])
        checks.append((t("verify.lattice.unimodular_v"),
                       lattice.is_identity(lattice.multiply(V, V_inv))
                       and lattice.is_identity(lattice.multiply(V_inv, V)),
                       t("verify.lattice.inverse", n=lattice.shape(V)[0])))
        normal = lattice.parse(p["s"])
        checks.append((t("verify.lattice.transform_two"),
                       lattice.multiply(lattice.multiply(U, A), V) == normal,
                       t("verify.lattice.equation", eq="U.A.V = S")))
        checks.append((t("verify.lattice.smith_shape"),
                       lattice.is_smith(normal, p["invariants"]),
                       t("verify.lattice.invariants",
                         values=", ".join(map(str, p["invariants"])) or "-")))
        sign *= lattice.unimodular_sign(V)
        diag = [normal[i][i] for i in range(min(n, m))]
        rank = sum(1 for d in diag if d)
    else:
        normal = lattice.parse(p["h"])
        checks.append((t("verify.lattice.transform"),
                       lattice.multiply(U, A) == normal,
                       t("verify.lattice.equation", eq="U.A = H")))
        checks.append((t("verify.lattice.hermite_shape"),
                       lattice.is_hermite(normal, p["pivots"]),
                       t("verify.lattice.pivots", n=len(p["pivots"]))))
        diag = [normal[i][i] for i in range(min(n, m))]
        rank = len(p["pivots"])

    checks.append((t("verify.lattice.sign"), sign in (1, -1)
                   and sign == p["det_u"] * (p.get("det_v", 1) if smith else 1),
                   t("verify.lattice.sign_is", sign=sign)))

    checks.append((t("verify.lattice.rank"), rank == p["rank"],
                   t("verify.lattice.rank_is", r=rank, n=n, m=m)))

    # The fingerprint is recomputed from the matrix in the payload, so a
    # certificate whose matrix was edited after the fact disagrees with its
    # own number -- and so does one whose number was edited to match somebody
    # else's matrix.
    if p.get("fingerprint") is not None:
        from . import interchange

        checks.append((t("verify.lattice.fingerprint"),
                       str(interchange.fingerprint(A)) == str(p["fingerprint"]),
                       t("verify.lattice.fingerprint_is",
                         value=str(p["fingerprint"]))))

    if n == m:
        want = sign
        for d in diag:
            want *= d
        checks.append((t("verify.lattice.determinant"), want == p["det"],
                       t("verify.lattice.det_is", d=want)))

    return VerifyReport(
        all(c[1] for c in checks), "integer_matrix", True, checks=checks,
        warnings=([t("verify.lattice.scope")] if not p.get("fingerprint")
                  else [t("verify.lattice.scope_fingerprinted",
                          value=str(p["fingerprint"])),
                        t("verify.lattice.scope")]),
        method_key="verify.lattice.method",
        detail=t("verify.lattice.detail", question=p["question"], n=n, m=m),
    )


def _verify_hypothesis_audit(cert, limits) -> VerifyReport:
    """Re-run every witness against the formulas it claims to break."""
    from . import audit as _audit

    p = cert.payload
    rows = p["rows"]
    counts = {v: sum(1 for r in rows if r["verdict"] == v)
              for v in _audit.VERDICTS}
    # A certificate written before `domain` existed declares three counts, not
    # four. Comparing on the keys it declares keeps those verifying, and the
    # verdicts check below is what stops a forger from deleting a key to hide
    # a row.
    declared = {k: counts.get(k, 0) for k in p["counts"]}
    checks = [(t("verify.audit.counts"), declared == p["counts"],
               t("verify.audit.tally", needed=counts["needed"],
                 redundant=counts["redundant"], domain=counts["domain"],
                 unknown=counts["unknown"]))]

    stray = sorted({r["verdict"] for r in rows} - set(p["counts"]))
    checks.append((t("verify.audit.verdicts"), not stray,
                   ", ".join(stray) or "-"))

    got = _audit.recheck(p, limits)
    checks.append((t("verify.audit.witnesses"), not got["bad"],
                   t("verify.audit.reapplied", n=got["checked"],
                     bad=", ".join(got["bad"][:3]) or "-")))

    # Every `needed` verdict must actually carry its witness: one without is a
    # claim with nothing behind it.
    missing = [r["hypothesis"] for r in rows
               if r["verdict"] == "needed" and not r.get("witness")]
    checks.append((t("verify.audit.every_witness"), not missing,
                   ", ".join(missing[:3]) or "-"))

    # The obligations are DERIVED, not believed: a certificate that listed
    # fewer divisors than the formulas contain would be one whose searches ran
    # unguarded, which is exactly the defect this check exists for.
    duties = _audit.declared_obligations(p)
    checks.append((t("verify.audit.obligations"), duties["ok"],
                   t("verify.audit.divisors",
                     n=len(duties["found"]),
                     values=", ".join(duties["found"][:4]) or "-",
                     missing=", ".join(duties["missing"][:3]) or "-")))

    # And a `domain` verdict must name an obligation the kept hypotheses no
    # longer force -- otherwise it is `redundant` wearing a kinder label.
    bare = [r["hypothesis"] for r in rows
            if r["verdict"] == "domain" and not r.get("obligations")]
    checks.append((t("verify.audit.every_obligation"), not bare,
                   ", ".join(bare[:3]) or "-"))

    warnings = [t("verify.audit.not_minimal")]
    if counts["unknown"]:
        warnings.append(t("verify.audit.unknown", n=counts["unknown"]))
    if counts["domain"]:
        warnings.append(t("verify.audit.domain_scope", n=counts["domain"]))
    return VerifyReport(
        all(c[1] for c in checks), "hypothesis_audit", False, checks=checks,
        warnings=warnings, method_key="verify.audit.method",
        detail=t("verify.audit.detail", needed=counts["needed"],
                 redundant=counts["redundant"], domain=counts["domain"],
                 unknown=counts["unknown"]),
    )


def _verify_ratio_bound(cert, limits) -> VerifyReport:
    """Re-multiply, re-shift, re-read the signs. Nothing is trusted."""
    from .parametric import nonneg_on_region, region_terms
    from .polynomials import Poly
    from .ratio import positive_on_ray

    p = cert.payload
    ring = tuple(p["parameters"])
    lows = p["parameters"]
    ln, ld = (Poly.parse(ring, x) for x in p["left"])
    rn, rd = (Poly.parse(ring, x) for x in p["right"])
    region = [(n, Poly.parse(ring, g))
              for n, g in sorted(p.get("region", {}).items())]
    terms = region_terms(region, lows)

    left_ok, _ls = positive_on_ray(ld, lows, terms)
    right_ok, _rs = positive_on_ray(rd, lows, terms)
    checks = [(t("verify.ratio.denominators"), left_ok and right_ok,
               t("verify.ratio.which", left=str(ld) or "0",
                 right=str(rd) or "0"))]

    # The difference is REBUILT from the two sides, not read from the payload.
    want = Poly.parse(ring, p["difference"])
    got = rn * ld - ln * rd
    checks.append((t("verify.ratio.expanded"), not (got - want),
                   str(want) or "0"))

    # An unrecognised relation must not fall back to the weaker reading: a
    # payload saying something this verifier does not understand has to be
    # refused, or every future spelling silently means `<=`.
    if p["relation"] not in ("<=", "<"):
        checks.append((t("verify.ratio.relation"), False, str(p["relation"])))
        return VerifyReport(False, "ratio_bound", True, checks=checks,
                            detail=t("ratio.relation", rel=p["relation"]))
    strict = p["relation"] == "<"
    if strict:
        sign_ok, _sh = positive_on_ray(got, lows, terms)
    else:
        sign_ok, _sh, _u, _r = nonneg_on_region(got, lows, terms)
    checks.append((t("verify.ratio.sign_strict" if strict
                     else "verify.ratio.sign"), bool(sign_ok),
                   str(got) or "0"))

    floor = ", ".join("{} >= {}".format(k, v) for k, v in lows.items())
    warnings = [t("verify.ratio.scope", floor=floor)]
    if region:
        warnings.append(t("verify.param.region", n=len(region),
                          conditions="; ".join("{} >= 0".format(g)
                                               for _n, g in region)))
    return VerifyReport(
        all(c[1] for c in checks), "ratio_bound", True, checks=checks,
        warnings=warnings, method_key="verify.ratio.method",
        detail=t("verify.ratio.detail", left=_ratio_text(ln, ld),
                 rel=p["relation"], right=_ratio_text(rn, rd), floor=floor),
    )


def _ratio_text(num, den) -> str:
    text = str(num) or "0"
    return text if str(den) == "1" else "({}) / ({})".format(text, str(den))


def _verify_family_extremum(cert, limits) -> VerifyReport:
    """Re-derive every item's program and re-check the vector stored for it."""
    from . import family

    p = cert.payload
    checks, warnings = [], []

    got = _digest_of(p["ids"])
    checks.append((t("verify.family_max.ids"), got == p["ids_sha256"],
                   got[:16]))
    covered = 1 + len(p["bounds"])
    checks.append((t("verify.family_max.every_item"),
                   covered == p["count"] == len(p["ids"]),
                   t("verify.family_max.counts", n=covered,
                     total=p["count"])))

    path, why = _spec_from(cert)
    if path is None:
        # Without the spec there is no way to rebuild the programs, and the
        # stored vectors are numbers about nothing. Said, not skipped.
        warnings.append(t("verify.family_max.no_spec",
                          reason=t("verify.sweep.replay."
                                   + (why if why else "no_path"))))
        return VerifyReport(
            False, "family_extremum", False, checks=checks, warnings=warnings,
            detail=t("verify.family_max.unverified", value=p["value"]))

    from .spec import load_spec

    spec = load_spec(path)
    try:
        ok_argmax, bad, missing = family.check(p, spec, limits)
    except (family.NotAFamily, KeyError, TypeError, ValueError) as e:
        return VerifyReport(False, "family_extremum", False, checks=checks,
                            warnings=warnings,
                            detail=t("verify.failed", type=type(e).__name__,
                                     message=e))

    checks.append((t("verify.family_max.attained"), ok_argmax,
                   t("verify.lp.declared", value=p["value"])))
    checks.append((t("verify.family_max.bounded"), not bad and not missing,
                   t("verify.family_max.offenders",
                     n=len(p["bounds"]),
                     bad=", ".join(map(str, bad[:3])) or "-",
                     missing=", ".join(map(str, missing[:3])) or "-")))
    warnings.append(t("verify.family_max.scope"))
    return VerifyReport(
        all(c[1] for c in checks), "family_extremum", False, checks=checks,
        warnings=warnings, method_key="verify.family_max.method",
        detail=t("verify.family_max.detail", value=p["value"],
                 argmax=p["argmax"], n=p["count"]),
    )


def _verify_integer_peak(cert, limits) -> VerifyReport:
    """Re-derive the coefficients from the objective, and re-read the signs."""
    from fractions import Fraction

    from .parametric import nonneg_on_region, region_terms
    from .peak import split
    from .polynomials import Poly

    p = cert.payload
    params = tuple(p["parameters"])
    lows = p["parameters"]
    full = tuple(list(params) + [p["variable"]])
    objective = Poly.parse(full, p["objective"])
    star = Poly.parse(params, p["argmax"])

    # From the objective itself, not from what the payload says they are.
    A, B, C = split(objective, p["variable"])
    neg_a = A.scaled(-1)
    region = [(n, Poly.parse(params, g))
              for n, g in sorted(p.get("region", {}).items())]
    terms = region_terms(region, lows)

    shape, _sh, _u, _r = nonneg_on_region(neg_a, lows, terms)
    const = neg_a.terms.get((0,) * len(params), Fraction(0))
    concave = shape and const > 0
    checks = [(t("verify.peak.concave"), concave, str(A) or "0")]

    integral = all(co.denominator == 1 for co in star.terms.values())
    checks.append((t("verify.peak.integral"), integral, str(star) or "0"))

    slope = A.scaled(2) * star + B
    up_ok, _s1, _m1, _r1 = nonneg_on_region(neg_a - slope, lows, terms)
    low_ok, _s2, _m2, _r2 = nonneg_on_region(slope - A, lows, terms)
    checks.append((t("verify.peak.step"), up_ok and low_ok, str(slope) or "0"))

    want = Poly.parse(params, p["value"])
    got = A * star * star + B * star + C
    matches = not (got - want)
    checks.append((t("verify.peak.value"), matches, str(want) or "0"))

    floor = ", ".join("{} >= {}".format(k, v) for k, v in lows.items())
    warnings = [t("verify.peak.scope", floor=floor)]
    if region:
        warnings.append(t("verify.param.region", n=len(region),
                          conditions="; ".join("{} >= 0".format(g)
                                               for _n, g in region)))
    return VerifyReport(
        concave and integral and up_ok and low_ok and matches,
        "integer_peak", True, checks=checks, warnings=warnings,
        method_key="verify.peak.method",
        detail=t("verify.peak.detail", value=str(want) or "0",
                 argmax=str(star) or "0", floor=floor),
    )


def _verify_parametric_bound(cert, limits) -> VerifyReport:
    """Re-derive every residual and re-read the signs. No solver, no search."""
    from fractions import Fraction

    from .parametric import (dual_text, nonneg_on_region, region_terms)
    from .polynomials import Poly

    p = cert.payload
    ring = tuple(p["parameters"])
    lows = p["parameters"]
    minimising = p.get("sense", "max") == "min"
    if p.get("witness") == "primal":
        return _verify_parametric_primal(cert, limits)
    free = set(p.get("free") or [])
    senses = {row[0]: row[2] for row in p["constraints"]}
    if "dual_poly" in p:
        y = {n: Poly.parse(ring, v) for n, v in p["dual_poly"].items()}
    else:
        y = {n: Poly.const(ring, Fraction(v)) for n, v in p["dual"].items()}

    # `y >= 0`. Constant or not, it is the same shift test; a constant just
    # shifts to itself.
    region = [(n, Poly.parse(ring, g))
              for n, g in sorted(p.get("region", {}).items())]
    terms = region_terms(region, lows)
    nn = _param_nonneg(p, ring, lows, terms)
    off = sorted(n for n, poly in y.items() if senses.get(n) != "=="
                 and not nn("dual", n, poly))
    nonneg = not off
    checks = [(t("verify.param.nonneg"), nonneg,
               t("verify.param.offenders", names=", ".join(off) or "-"))]

    # When the dual is carried twice -- once to be read, once to be recomputed
    # from -- the readable copy is checked against the other. A field nobody
    # checks is a field that can say anything.
    if "dual_poly" in p:
        drift = sorted(n for n, poly in y.items()
                       if p["dual"].get(n) != dual_text(poly))
        checks.append((t("verify.param.dual_text"), not drift,
                       t("verify.param.differing",
                         names=", ".join(drift) or "-")))
        nonneg = nonneg and not drift

    # The residual, rebuilt from the payload rather than trusted from it.
    bad = []
    for var in p["variables"]:
        acc = Poly(ring)
        for name, row, _sense, _rhs in p["constraints"]:
            if var in row and y.get(name) and y[name].terms:
                acc = acc + Poly.parse(ring, row[var]) * y[name]
        obj = Poly.parse(ring, p["objective"].get(var, {}))
        residual = (obj - acc) if minimising else (acc - obj)
        if var in free:
            ok = not residual.terms          # a free column must balance
        else:
            ok = nn("columns", var, residual)
        if not ok:
            bad.append(var)
    checks.append((t("verify.param.feasible"), not bad,
                   t("verify.param.columns", n=len(p["variables"]),
                     bad=", ".join(bad[:4]) or "-")))

    # and the bound itself
    want = Poly.parse(ring, p["bound"])
    got = Poly(ring)
    for name, _row, _sense, rhs in p["constraints"]:
        if y.get(name) and y[name].terms:
            got = got + Poly.parse(ring, rhs) * y[name]
    matches = not (got - want)
    checks.append((t("verify.param.bound"), matches, str(want) or "0"))
    claim_ok = _param_claim_check(p, want, lows, terms, ring, minimising,
                                  checks, witness="dual")

    floor = ", ".join("{} >= {}".format(k, v) for k, v in lows.items())
    if p.get("box"):
        floor = ", ".join("{} in [{}, {}]".format(n, lo, hi)
                          for n, (lo, hi) in p["box"].items())
    detail_key = "verify.param.detail_min" if minimising \
        else "verify.param.detail"
    warnings = [t("verify.param.scope", floor=floor)]
    if region:
        # Louder than the floor, because a floor looks like scope and a
        # polynomial side condition can be mistaken for something proved.
        warnings.append(t("verify.param.region", n=len(region),
                          conditions="; ".join("{} >= 0".format(g)
                                               for _n, g in region)))
        floor = floor + ", " + ", ".join("{} >= 0".format(g)
                                         for _n, g in region)
    return VerifyReport(
        nonneg and not bad and matches and claim_ok, "parametric_bound", True,
        checks=checks,
        warnings=warnings,
        method_key="verify.param.method",
        detail=t(detail_key, bound=str(want) or "0", floor=floor),
    )


def _param_nonneg(p, ring, lows, terms):
    """The non-negativity test a parametric payload asks for: Bernstein on the
    recorded box -- with the recorded splits and degrees, recomputed -- or the
    shift test on the ray. Returns `nn(kind, name, poly) -> bool`."""
    from fractions import Fraction

    from .parametric import nonneg_on_region

    raw = p.get("box")
    if raw is None:
        return lambda kind, name, poly: nonneg_on_region(poly, lows, terms)[0]
    from . import bernstein

    box = {n: (Fraction(lo), Fraction(hi)) for n, (lo, hi) in raw.items()}
    if set(box) != set(ring):
        return lambda kind, name, poly: False
    trees = p.get("box_trees") or {}

    def nn(kind, name, poly):
        tree = (trees.get("claim") if kind == "claim"
                else (trees.get(kind) or {}).get(name))
        return bernstein.check(poly, box, tree)
    return nn


def _param_claim_check(p, bound, lows, terms, ring, minimising, checks,
                       witness):
    """A claimed target, recomputed: its `holds` must be what the shift test
    says, in the direction the witness bounds."""
    from .parametric import nonneg_on_region
    from .polynomials import Poly

    c = p.get("claim")
    if c is None:
        return True
    target = Poly.parse(ring, c["target"])
    upper = (witness == "dual") != minimising     # does `bound` bound above?
    diff = (target - bound) if upper else (bound - target)
    holds = _param_nonneg(p, ring, lows, terms)("claim", None, diff)
    want_rel = "<=" if upper else ">="
    ok = holds == bool(c.get("holds")) and c.get("relation") == want_rel
    checks.append((t("verify.param.claim"), ok,
                   "{} {} {}".format("bound", want_rel, target or "0")))
    return ok


def _verify_parametric_primal(cert, limits) -> VerifyReport:
    """A feasible x(p): signs, rows and the objective, all recomputed."""
    from .parametric import nonneg_on_region, region_terms
    from .polynomials import Poly

    p = cert.payload
    ring = tuple(p["parameters"])
    lows = p["parameters"]
    minimising = p.get("sense", "max") == "min"
    free = set(p.get("free") or [])
    region = [(n, Poly.parse(ring, g))
              for n, g in sorted(p.get("region", {}).items())]
    terms = region_terms(region, lows)
    x = {v: Poly.parse(ring, e) for v, e in (p.get("primal") or {}).items()}
    nn = _param_nonneg(p, ring, lows, terms)
    checks = []
    neg = sorted(v for v, e in x.items() if v not in free
                 and not nn("primal", v, e))
    checks.append((t("verify.param.primal_nonneg"), not neg,
                   ", ".join(neg[:4]) or "-"))
    bad = []
    for name, row, sense, rhs in p["constraints"]:
        lhs = Poly(ring)
        for var, coef in row.items():
            if var in x and x[var].terms:
                lhs = lhs + Poly.parse(ring, coef) * x[var]
        r = Poly.parse(ring, rhs)
        if sense == "==":
            ok = not (lhs - r)
        else:
            slack = (r - lhs) if sense == "<=" else (lhs - r)
            ok = nn("rows", name, slack)
        if not ok:
            bad.append(name)
    checks.append((t("verify.param.primal_rows"), not bad,
                   ", ".join(bad[:4]) or "-"))
    got = Poly(ring)
    for var, coef in p["objective"].items():
        if var in x and x[var].terms:
            got = got + Poly.parse(ring, coef) * x[var]
    want = Poly.parse(ring, p["bound"])
    matches = not (got - want)
    checks.append((t("verify.param.bound"), matches, str(want) or "0"))
    claim_ok = _param_claim_check(p, want, lows, terms, ring, minimising,
                                  checks, witness="primal")
    floor = ", ".join("{} >= {}".format(k, v) for k, v in lows.items())
    if p.get("box"):
        floor = ", ".join("{} in [{}, {}]".format(n, lo, hi)
                          for n, (lo, hi) in p["box"].items())
    warnings = [t("verify.param.scope", floor=floor)]
    if region:
        warnings.append(t("verify.param.region", n=len(region),
                          conditions="; ".join("{} >= 0".format(g)
                                               for _n, g in region)))
    return VerifyReport(
        not neg and not bad and matches and claim_ok, "parametric_bound", True,
        checks=checks, warnings=warnings, method_key="verify.param.method",
        detail=t("verify.param.detail_primal_min" if minimising
                 else "verify.param.detail_primal_max",
                 bound=str(want) or "0", floor=floor))


def _verify_resultant(cert, limits) -> VerifyReport:
    """Expand `A*f + B*g` and compare with the resultant. That is the whole check."""
    from .polynomials import Poly

    p = cert.payload
    variables = tuple(p["variables"])
    f = Poly.parse(variables, p["f"])
    g = Poly.parse(variables, p["g"])
    A = Poly.parse(variables, p["A"])
    B = Poly.parse(variables, p["B"])
    res = Poly.parse(variables, p["resultant"])

    ok = not (A * f + B * g - res)
    checks = [(t("verify.resultant.identity"), ok,
               t("verify.resultant.res", res=str(res) or "0"))]

    # The Bezout normalisation. Not needed for soundness -- the identity above
    # is the whole claim -- but a construction that broke it produced these
    # cofactors by some other route, and that is worth knowing.
    k = variables.index(p["eliminated"]) if p["eliminated"] in variables else None
    if k is not None:
        da = max((e[k] for e in A.terms), default=-1)
        db = max((e[k] for e in B.terms), default=-1)
        shaped = da < p["deg_g"] and db < p["deg_f"]
        checks.append((t("verify.resultant.degrees"), shaped,
                       t("verify.resultant.deg_detail", da=da, db=db,
                         m=p["deg_g"], n=p["deg_f"])))
        ok = ok and shaped

    warnings = []
    if not p.get("lead_f_constant") and not p.get("lead_g_constant"):
        # Both leading coefficients can vanish, and there sufficiency goes.
        warnings.append(t("verify.resultant.leading"))
    warnings.append(t("verify.resultant.closed_field"))

    return VerifyReport(
        ok, "resultant", True, checks=checks, warnings=warnings,
        method_key="verify.resultant.method",
        detail=t("verify.resultant.detail", var=p["eliminated"],
                 n=p["deg_f"], m=p["deg_g"]),
    )


def _verify_ideal(cert, limits) -> VerifyReport:
    """Expand the combination and compare. No solver, no algebra system."""
    from .polynomials import Poly, combination

    p = cert.payload
    variables = tuple(p["variables"])
    gs = [Poly.parse(variables, g) for g in p["equations"]]
    hs = [Poly.parse(variables, h) for h in p["cofactors"]]
    lhs = (Poly.const(variables, 1) if p["inconsistent"]
           else Poly.parse(variables, p["claim"]))

    checks = [(t("verify.ideal.count"), len(hs) == len(gs),
               t("verify.ideal.n", h=len(hs), g=len(gs)))]
    if len(hs) == len(gs):
        got = combination(hs, gs)
        checks.append((t("verify.ideal.expands"), got == lhs,
                       t("verify.ideal.difference", d=str(got - lhs)[:60])))

    warnings = []
    if p["inconsistent"]:
        warnings.append(t("verify.ideal.field"))
    return VerifyReport(
        all(c[1] for c in checks), "ideal", True, checks=checks,
        warnings=warnings,
        detail=t("verify.ideal.detail", n=len(gs),
                 what=t("verify.ideal.inconsistent") if p["inconsistent"]
                 else t("verify.ideal.member")),
    )


def _verify_sos(cert, limits) -> VerifyReport:
    """Square the forms, add them up, compare coefficients."""
    from . import sos as sosmod
    from .polynomials import Poly

    p = cert.payload
    variables = tuple(p["variables"])
    target = Poly.parse(variables, p["poly"])
    terms = sosmod.parse(variables, p["terms"])

    checks = [(t("verify.sos.nonneg"), all(d >= 0 for d, _ in terms),
               t("verify.sos.count", n=len(terms)))]
    got = sosmod.expand(terms, variables)
    checks.append((t("verify.sos.expands"), got == target,
                   t("verify.ideal.difference", d=str(got - target)[:60])))
    return VerifyReport(
        all(c[1] for c in checks), "sos", True, checks=checks,
        detail=t("verify.sos.detail", n=len(terms)),
    )


def _verify_number(cert, limits) -> VerifyReport:
    """Modular exponentiation, and nothing else."""
    from . import numbers

    p = cert.payload
    tree = p["tree"]

    # The tree has to be about the number the certificate NAMES. Without this,
    # a perfectly good Pratt tree for 2^31 - 1 relabelled as 2^31 verified --
    # and 2^31 is even. The tree was never wrong; nothing tied it to the claim.
    claimed = p.get("n")
    root = tree.get("n") if isinstance(tree, dict) else None
    tied = root is not None and claimed is not None and root == claimed
    checks = [(t("verify.number.same_n"), tied,
               t("verify.number.n_detail", claimed=claimed, root=root))]

    if p["question"] == "factor":
        checks += numbers.verify_factorisation(tree)
    else:
        checks += numbers.verify_pratt(tree)
    return VerifyReport(
        all(c[1] for c in checks), "number", True, checks=checks,
        detail=t("verify.number.detail", n=p["n"], checks=len(checks)),
    )



def _verify_mixed_design(cert, limits) -> VerifyReport:
    """The construction, checked; the optimality, not claimed."""
    from fractions import Fraction

    from . import exact

    p = cert.payload
    kinds = p["kinds"]
    assign = {k: exact.to_fraction(v) for k, v in p["assignment"].items()}
    cont = {k: exact.to_fraction(v) for k, v in p["continuous"].items()}
    point = dict(assign)
    point.update(cont)
    checks, warnings = [], []

    # 1. the discrete part really is discrete
    off = [k for k, v in assign.items() if v.denominator != 1]
    binary_off = [k for k, v in assign.items()
                  if kinds.get(k) == "binary" and v not in (0, 1)]
    checks.append((t("verify.mixed.integral"), not off and not binary_off,
                   t("verify.mixed.offenders",
                     names=", ".join((off + binary_off)[:3]) or "-")))

    # 2. every ORIGINAL constraint, at the full point
    bad = []
    for row in p["system"]:
        lhs = sum((exact.to_fraction(c) * point.get(v, Fraction(0))
                   for v, c in row["coeffs"].items()), Fraction(0))
        rhs = exact.to_fraction(row["rhs"])
        ok = (lhs <= rhs if row["sense"] == "<=" else
              lhs >= rhs if row["sense"] == ">=" else lhs == rhs)
        if not ok:
            bad.append(row["name"])
    checks.append((t("verify.mixed.feasible"), not bad,
                   t("verify.mixed.violated", names=", ".join(bad[:3]) or "-",
                     n=len(p["system"]))))

    # 3. the value it claims to attain
    got = sum((exact.to_fraction(c) * point.get(v, Fraction(0))
               for v, c in p["objective"].items()), Fraction(0))
    checks.append((t("verify.mixed.value"),
                   got == exact.to_fraction(p["achieved"]),
                   t("verify.lp.declared", value=p["achieved"])))

    # 4. the residual LP is the original with THIS assignment substituted.
    #    Without this the sub-certificate could be about a different problem,
    #    which is the same gap `compose` closes between a lemma and its use.
    sub = p.get("residual")
    if sub is None:
        checks.append((t("verify.mixed.residual"), False,
                       t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(sub), limits)
        checks.append((t("verify.mixed.residual"), rep.ok, rep.detail))
        warnings.extend(rep.warnings)
        checks.append((t("verify.mixed.substituted"),
                       _residual_matches(p, assign, sub), ""))

    # 5. the target, compared exactly.
    #    A design that falls short is not an INVALID certificate -- it is a
    #    valid certificate for a design that falls short, and saying otherwise
    #    would read as "something is broken" when nothing is. So the shortfall
    #    is a warning and what gets CHECKED is that the arithmetic is right.
    if p.get("target") is not None:
        want = exact.to_fraction(p["target"])
        got = exact.to_fraction(p["achieved"])
        if got < want:
            warnings.append(t("verify.mixed.short",
                              value=p["achieved"], target=p["target"],
                              deficit=exact.serialize(want - got)))
        else:
            checks.append((t("verify.mixed.target"), True,
                           t("verify.mixed.margin", value=p["achieved"],
                             target=p["target"],
                             margin=exact.serialize(got - want))))

    # 6. optimality: claimed only when the two bounds meet
    if p.get("globally_optimal"):
        bound = p.get("bound")
        checks.append((t("verify.mixed.optimal"),
                       bound is not None
                       and exact.to_fraction(bound) == exact.to_fraction(p["achieved"]),
                       t("verify.lp.declared", value=bound or "-")))
    else:
        warnings.append(t("verify.mixed.not_optimal",
                          bound=p.get("bound") or "-"))
    if p.get("skeleton_from") == "external":
        warnings.append(t("verify.mixed.external"))

    level = p.get("level", "conditional_optimum")
    return VerifyReport(
        all(c[1] for c in checks), "mixed_design", True, checks=checks,
        warnings=warnings,
        detail=t("verify.mixed.level." + level) + " -- "
        + t("verify.mixed.detail", value=p["achieved"],
            n=len([k for k, v in assign.items() if v])),
    )


#: How `LPSpec.as_leq_system` renames and flips a row when it normalises to
#: `A x <= b`. Reading this wrong is how a certificate for a perfectly good
#: design came out INVALID: the check looked up the original name in a table
#: keyed by the normalised one, missed, and reported a mismatch that was not
#: there. Every consumer of a normalised row set needs this mapping, so it
#: lives in one place and is used by name.
def normalised_rows(name, sense):
    """The rows `as_leq_system` produces for one declared constraint.

    Returns [(row name, sign)], where the sign is what the original
    coefficients were multiplied by. An equality becomes TWO rows and both
    have to agree, which is the case the old code did not have at all.
    """
    if sense == "<=":
        return [(name, 1)]
    if sense == ">=":
        return [(name + "_geq", -1)]
    return [(name + "_le", 1), (name + "_ge", -1)]


def _residual_matches(p, assign, sub) -> bool:
    """Is the sub-certificate's system the original one, frozen at `assign`?"""
    from fractions import Fraction

    from . import exact

    names = sub["payload"].get("names") or []
    var_names = sub["payload"].get("var_names") or []
    A = [exact.parse_all(r) for r in sub["payload"]["A"]]
    b = exact.parse_all(sub["payload"]["b"])
    by_name = dict(zip(names, zip(A, b)))

    for row in p["system"]:
        moved = sum((exact.to_fraction(c) * assign[v]
                     for v, c in row["coeffs"].items() if v in assign),
                    Fraction(0))
        want_rhs = exact.to_fraction(row["rhs"]) - moved
        for rname, flip in normalised_rows(row["name"],
                                           row.get("sense", "<=")):
            if rname not in by_name:
                return False
            got_row, got_rhs = by_name[rname]
            if got_rhs != flip * want_rhs:
                return False
            for j, v in enumerate(var_names):
                if got_row[j] != exact.to_fraction(row["coeffs"].get(v, 0)) * flip:
                    return False
    return True



def _verify_gap(cert, limits) -> VerifyReport:
    from . import exact

    p = cert.payload
    checks, warnings = [], []

    for key, label in (("fractional", t("verify.gap.fractional")),
                       ("integral", t("verify.gap.integral"))):
        sub = p.get(key)
        if sub is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        checks.append((label, rep.ok, rep.detail))
        warnings.extend(rep.warnings)

    # The two halves must be about the SAME packing. Without this the gap is
    # a subtraction of two numbers that were never compared.
    same = _same_packing(p)
    checks.append((t("verify.gap.same"), same, ""))

    mu, nu = exact.to_fraction(p["mu"]), exact.to_fraction(p["nu"])
    checks.append((t("verify.gap.arithmetic"),
                   mu - nu == exact.to_fraction(p["gap"]),
                   "{} - {} = {}".format(p["mu"], p["nu"], p["gap"])))
    checks.append((t("verify.gap.order"), nu <= mu,
                   t("verify.gap.relaxation")))

    if p.get("level") != "global_optimum":
        warnings.append(t("verify.gap.nu_not_optimal"))

    return VerifyReport(
        all(c[1] for c in checks), "gap", False, checks=checks,
        warnings=warnings,
        detail=t("verify.gap.detail", mu=p["mu"], nu=p["nu"], gap=p["gap"]),
    )


def _same_packing(p) -> bool:
    """Both sides must carry the same constraint matrix and objective."""
    frac = (p.get("fractional") or {}).get("payload") or {}
    whole = (p.get("integral") or {}).get("payload") or {}
    system = whole.get("system")
    if not system or not frac.get("names"):
        return False
    # The mixed certificate keeps the original rows by name; the lp_dual one
    # keeps them positionally. Same names, same count, is what can be checked
    # from the two payloads alone.
    return [r["name"] for r in system] == list(frac["names"])



def _verify_farkas_ray(cert, limits) -> VerifyReport:
    """Three dot products. That is the whole thing."""
    from fractions import Fraction

    from . import exact

    p = cert.payload
    A = [exact.parse_all(r) for r in p["A"]]
    b, y = exact.parse_all(p["b"]), exact.parse_all(p["y"])
    cols = len(A[0]) if A else 0

    checks = [
        (t("verify.ray.nonneg"), all(v >= 0 for v in y),
         "min(y) = {}".format(exact.serialize(min(y)) if y else "-")),
        (t("verify.ray.columns"),
         all(sum(A[i][j] * y[i] for i in range(len(A))) >= 0
             for j in range(cols)), "A^T y >= 0"),
    ]
    dot = sum(bi * yi for bi, yi in zip(b, y))
    checks.append((t("verify.ray.negative"), dot < 0,
                   "b.y = {}".format(exact.serialize(dot))))
    return VerifyReport(
        all(c[1] for c in checks), "farkas_ray", True, checks=checks,
        detail=t("verify.ray.detail", n=len(y)),
    )


def _node_closes(root, node, incumbent):
    """Does this node close ITS OWN problem? Returns (ok, reason).

    The node's linear program is rebuilt from the root system and the node's
    fixings -- by the same function the producer used, so there is no second
    reading of it -- and then the stored vectors are checked against THAT.
    A dual belonging to another node no longer fits, because the matrix it is
    checked against is not the one it came from.
    """
    from . import exact, tree

    fixed = tree.fixings(node["fixed"])
    try:
        node_spec, const = tree.restrict(root, fixed)
        A, b, c = _leq_parts(node_spec)
    except (KeyError, ValueError, TypeError):
        return False, "bad"

    if node["why"] == "infeasible":
        ray = node.get("ray")
        if ray is None:
            return False, "open"
        y = exact.parse_all(ray)
        if len(y) != len(A):
            return False, "bad"
        # y >= 0, A^T y >= 0, b.y < 0: the subtree is empty.
        if any(v < 0 for v in y):
            return False, "bad"
        for j in range(len(c)):
            if sum(A[i][j] * y[i] for i in range(len(A))) < 0:
                return False, "bad"
        return (sum(bi * yi for bi, yi in zip(b, y)) < 0), "bad"

    if node.get("dual") is None or node.get("bound") is None:
        return False, "open"
    x = exact.parse_all(node.get("primal") or [])
    y = exact.parse_all(node["dual"])
    if len(y) != len(A) or len(x) != len(c):
        return False, "bad"
    if any(v < 0 for v in y) or any(v < 0 for v in x):
        return False, "bad"
    # dual feasible: A^T y >= c, so b.y bounds the relaxation from above
    for j in range(len(c)):
        if sum(A[i][j] * y[i] for i in range(len(A))) < c[j]:
            return False, "bad"
    # primal feasible, so the two values bracket the optimum
    for i in range(len(A)):
        if sum(A[i][j] * x[j] for j in range(len(c))) > b[i]:
            return False, "bad"
    value = sum(bi * yi for bi, yi in zip(b, y))
    if sum(cj * xj for cj, xj in zip(c, x)) != value:
        return False, "bad"
    # and the bound the node claims is that value plus what the fixings pay
    if const + value != exact.to_fraction(node["bound"]):
        return False, "bad"
    # closing on a bound means the subtree cannot beat what is already held
    return exact.to_fraction(node["bound"]) <= incumbent, "bad"


def _node_bound_holds(root, node) -> bool:
    """Is the node's declared bound an upper bound for ITS OWN subproblem?

    The same arithmetic `_node_closes` performs, without the last question.
    Closing asks two things -- the bound is real, AND it does not beat the
    incumbent -- and a frontier needs only the first: an OPEN node has not
    been closed, and the point of carrying its dual is that its subtree still
    cannot exceed the number it declares.
    """
    from . import exact

    if node.get("dual") is None or node.get("bound") is None:
        return False
    fake = dict(node, why="bound")
    ok, _why = _node_closes(root, fake,
                            exact.to_fraction(node["bound"]))
    return ok


def _leq_parts(node_spec):
    """`max c.x, A x <= b, x >= 0` for a node, the same way the producer saw it."""
    from . import exact

    A, b, c, _names = node_spec.as_leq_system()
    return ([[exact.to_fraction(v) for v in row] for row in A],
            [exact.to_fraction(v) for v in b],
            [exact.to_fraction(v) for v in c])


def branch_frontier_certificate(incumbent, incumbent_cert, nodes, open_nodes,
                                bound, order, sense, system, reason,
                                original_sense=None, original_optimum=None,
                                title="") -> Certificate:
    """A search that ran out of budget, as an artefact instead of a log.

    `bb` used to return `RESOURCE_EXHAUSTED` with no certificate at all, and
    its own status report said so in as many words: "Not a certificate -- a
    status report". It also discarded the stack of nodes it had not opened.
    So hours of search left nothing that could be verified, archived, resumed
    or combined, which is the whole of what a user meant by asking for a
    frontier.

    WHAT IT CLAIMS, and it is an interval rather than a number:

        the optimum lies in [incumbent, bound]
        this design attains `incumbent`
        these OPEN subproblems are everything that remains

    The third clause is the one that makes it a certificate rather than a
    log. It is checked the way `branch_bound` checks completeness -- every
    branching node has all its children, and every child is closed, branching
    or declared open -- so a frontier that quietly dropped a subtree fails
    exactly as a tree that dropped one does.

    WHAT IT DOES NOT CLAIM: that `incumbent` is optimal. That is the point.

    An open node carries its own dual. Inheriting the parent's bound would
    have been free, and would have inherited a number nothing checks: a
    branching node's `bound` is not verified anywhere, because in a completed
    tree no claim rests on it. Here one does.
    """
    return Certificate(
        kind="branch_frontier",
        solver_free=True,
        payload={
            "incumbent": incumbent, "incumbent_cert": incumbent_cert,
            "nodes": nodes, "open": open_nodes, "bound": bound,
            "order": list(order), "sense": sense, "system": system,
            "reason": reason,
            "original_sense": original_sense or sense,
            "original_optimum": original_optimum,
            "title": title,
        },
        note_key="cert.note.branch_frontier",
    )


def _verify_branch_frontier(cert, limits) -> VerifyReport:
    """An interval, a design that reaches its lower end, and a frontier that
    accounts for everything still open."""
    from . import exact, tree

    p = cert.payload
    incumbent = exact.to_fraction(p["incumbent"])
    claimed = exact.to_fraction(p["bound"])
    nodes, opens = p["nodes"], p["open"]
    checks, warnings = [], []

    by_key = {_node_id(n["fixed"]): n for n in nodes}
    open_by_key = {_node_id(o["fixed"]): o for o in opens}
    both = set(by_key) & set(open_by_key)
    checks.append((t("verify.bb.unique"),
                   len(by_key) == len(nodes)
                   and len(open_by_key) == len(opens) and not both,
                   t("verify.bb.duplicates",
                     n=len(nodes) - len(by_key) + len(opens)
                     - len(open_by_key) + len(both))))

    sub = p.get("incumbent_cert")
    if sub is None:
        checks.append((t("verify.bb.incumbent"), False,
                       t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(sub), limits)
        reached = exact.to_fraction(
            (sub.get("payload") or {}).get("achieved") or p["incumbent"])
        checks.append((t("verify.bb.incumbent"),
                       rep.ok and reached == incumbent,
                       t("verify.lp.declared", value=p["incumbent"])))

    system = p.get("system")
    root = tree.spec_of(system) if system else None
    if root is None:
        # Without it a node's dual is a dual for SOME linear program and
        # nothing says which, so nothing below can be tied down.
        checks.append((t("verify.bb.tied"), False, t("verify.bb.untied")))
        return VerifyReport(False, "branch_frontier", True, checks=checks,
                            detail=t("verify.frontier.detail",
                                     lo=p["incumbent"], hi=p["bound"],
                                     n=len(opens)))

    # Every branching node has all its children, and each child is accounted
    # for: closed, branching, or open. A frontier that dropped a subtree
    # reads exactly like one that explored it.
    missing = []
    for n in nodes:
        if n["why"] != "branch":
            continue
        for val in n["values"]:
            child = _node_id(list(n["fixed"]) + [[n["on"], val]])
            if child not in by_key and child not in open_by_key:
                missing.append("{}={}".format(n["on"], val))
    checks.append((t("verify.bb.covered"), not missing,
                   t("verify.bb.missing", names=", ".join(missing[:3]) or "-",
                     n=len(missing))))

    bad_close = []
    for n in nodes:
        if n["why"] == "branch":
            continue
        ok, _why = _node_closes(root, n, incumbent)
        if not ok:
            bad_close.append(_node_id(n["fixed"]) or "root")
    checks.append((t("verify.bb.closed"), not bad_close,
                   t("verify.bb.open", names=", ".join(bad_close[:3]) or "-",
                     n=len(bad_close))))

    # An OPEN node carries its own dual, and the interval's upper end is the
    # largest of them. A node whose dual does not hold is worse than an
    # unexplored one: it claims a limit it cannot support.
    bad_open, worst = [], incumbent
    for o in opens:
        # The dual belongs to the PARENT's program, and the open node is a
        # restriction of it: fixing one more variable can only shrink the
        # feasible set, so the parent's bound bounds the child too. Both
        # halves are checked -- the dual against the parent's derived matrix,
        # and that the child really does extend the parent.
        parent = dict(o, fixed=o.get("from") or [], why="bound")
        extends = (list(o.get("from") or [])
                   == list(o["fixed"])[:len(o.get("from") or [])])
        if not extends or not _node_bound_holds(root, parent):
            bad_open.append(_node_id(o["fixed"]) or "root")
            continue
        worst = max(worst, exact.to_fraction(o["bound"]))
    checks.append((t("verify.frontier.bounded"), not bad_open,
                   t("verify.frontier.unbounded",
                     names=", ".join(bad_open[:3]) or "-", n=len(bad_open))))

    checks.append((t("verify.frontier.interval"),
                   not bad_open and worst == claimed and incumbent <= claimed,
                   t("verify.frontier.range", lo=exact.serialize(incumbent),
                     hi=exact.serialize(worst))))

    warnings.append(t("verify.frontier.scope"))
    return VerifyReport(
        all(c[1] for c in checks), "branch_frontier", True, checks=checks,
        warnings=warnings,
        detail=t("verify.frontier.detail", lo=p["incumbent"], hi=p["bound"],
                 n=len(opens)),
    )


def _verify_branch_bound(cert, limits) -> VerifyReport:
    """Every leaf closed, and the tree covering everything it should."""
    from fractions import Fraction

    from . import exact, tree

    p = cert.payload
    incumbent = exact.to_fraction(p["incumbent"])
    nodes = p["nodes"]
    checks, warnings = [], []

    by_key = {_node_id(n["fixed"]): n for n in nodes}
    checks.append((t("verify.bb.unique"), len(by_key) == len(nodes),
                   t("verify.bb.duplicates", n=len(nodes) - len(by_key))))

    # The incumbent is a design that exists and attains the claimed value.
    sub = p.get("incumbent_cert")
    if sub is None:
        checks.append((t("verify.bb.incumbent"), False,
                       t("verify.bisect.no_cert")))
    else:
        rep = verify(Certificate.from_dict(sub), limits)
        reached = exact.to_fraction(
            (sub.get("payload") or {}).get("achieved") or p["incumbent"])
        checks.append((t("verify.bb.incumbent"), rep.ok and reached == incumbent,
                       t("verify.lp.declared", value=p["incumbent"])))

    # The root problem, from which every node's problem is DERIVED. Without
    # it a node's certificate is a certificate for some linear program and
    # nothing says which -- so an easy subtree's dual closes a hard one.
    system = p.get("system")
    root = tree.spec_of(system) if system else None
    if root is None:
        warnings.append(t("verify.bb.untied"))

    # Every node is closed, or branches and its children are all present.
    bad_close, missing, open_nodes = [], [], []
    for n in nodes:
        why = n["why"]
        if why == "branch":
            for val in n["values"]:
                child = list(n["fixed"]) + [[n["on"], val]]
                if _node_id(child) not in by_key:
                    missing.append("{}={}".format(n["on"], val))
            continue

        where = _node_id(n["fixed"]) or "root"
        if root is not None:
            ok, why_not = _node_closes(root, n, incumbent)
            if why_not == "open":
                open_nodes.append(where)
            elif not ok:
                bad_close.append(where)
            continue

        # Older certificates: the nested form, checked on its own terms. The
        # warning above says what that does not establish.
        if n.get("cert") is None or (why != "infeasible"
                                     and n.get("bound") is None):
            open_nodes.append(where)
            continue
        r = verify(Certificate.from_dict(n["cert"]), limits)
        if not r.ok or (why != "infeasible"
                        and exact.to_fraction(n["bound"]) > incumbent):
            bad_close.append(where)

    checks.append((t("verify.bb.covered"), not missing,
                   t("verify.bb.missing", names=", ".join(missing[:3]) or "-",
                     n=len(missing))))
    if root is not None:
        checks.append((t("verify.bb.tied"), not bad_close,
                       t("verify.bb.derived", n=sum(
                           1 for n in nodes if n["why"] != "branch"))))
    checks.append((t("verify.bb.closed"), not bad_close and not open_nodes,
                   t("verify.bb.open", names=", ".join(
                       (bad_close + open_nodes)[:3]) or "-",
                     n=len(bad_close) + len(open_nodes))))

    kinds = {}
    for n in nodes:
        kinds[n["why"]] = kinds.get(n["why"], 0) + 1
    return VerifyReport(
        all(c[1] for c in checks), "branch_bound",
        # Not hardcoded any more. A tied tree closes every node by exact
        # rational arithmetic over a system it derives itself, which is the
        # whole point of carrying the root system.
        bool(cert.solver_free), checks=checks,
        warnings=warnings,
        detail=t("verify.bb.detail", value=p["incumbent"], n=len(nodes),
                 bound=kinds.get("bound", 0), inf=kinds.get("infeasible", 0),
                 leaf=kinds.get("leaf", 0)),
    )


def _node_id(fixed) -> str:
    return ",".join("{}={}".format(v, x) for v, x in fixed)



def _verify_asymptotic(cert, limits) -> VerifyReport:
    """Substitute, collect, read off the exponent. No solver, no spec."""
    from fractions import Fraction

    from . import asymptotics

    p = cert.payload
    orders = {k: Fraction(v) for k, v in p["orders"].items()}
    poly = asymptotics.Laurent({
        tuple((s, int(e)) for s, e in row["monomial"]): Fraction(row["coefficient"])
        for row in p["laurent"]})

    checks, warnings = [], []
    try:
        got = asymptotics.order(poly, orders, p["var"])
    except asymptotics.NotAsymptotic as e:
        return VerifyReport(False, "asymptotic", True,
                            detail=str(e))

    checks.append((t("verify.order.degree"), got["degree"] == p["degree"],
                   t("verify.order.recomputed", degree=got["degree"] or "-",
                     declared=p["degree"] or "-")))
    checks.append((t("verify.order.verdict"), got["verdict"] == p["verdict"],
                   t("order." + got["verdict"])))
    checks.append((t("verify.order.cancelled"),
                   got["cancelled"] == p.get("cancelled", 0),
                   t("verify.order.cancelled_n", n=got["cancelled"])))

    if p.get("expect") is not None and p["expect"] != p["verdict"]:
        warnings.append(t("verify.order.disagrees",
                          want=t("order." + p["expect"]),
                          got=t("order." + p["verdict"])))
    # Said every time, because it is the one thing a reader will forget.
    warnings.append(t("verify.order.constants", var=p["var"]))

    return VerifyReport(
        all(c[1] for c in checks), "asymptotic", True, checks=checks,
        warnings=warnings,
        detail=t("verify.order.detail", degree=p["degree"] or "-",
                 var=p["var"], verdict=t("order." + p["verdict"])),
    )


def _verify_model(cert, limits) -> VerifyReport:
    import z3

    p = cert.payload
    formula = z3.And(*z3.parse_smt2_string(p["smt2"]))
    subs = []
    for name, pair in p["assignment"].items():
        sort, val = pair
        subs.append((_const(z3, name, sort), _value(z3, sort, val)))
    got = z3.simplify(z3.substitute(formula, *subs)) if subs else z3.simplify(formula)
    ok = z3.is_true(got)
    return VerifyReport(
        ok, "model", True,
        checks=[(t("verify.model.satisfies"), ok, str(got))],
        detail="" if ok else t("verify.model.fails"),
    )


def _verify_unsat_core(cert, limits) -> VerifyReport:
    # With Farkas multipliers attached the core needs no solver at all: expand
    # the combination and read off the contradiction. That is the difference
    # between "z3 says so again" and "here is the arithmetic".
    if cert.payload.get("multipliers"):
        return _verify_core_by_farkas(cert)
    return _verify_core_by_solver(cert, limits)


def _verify_core_by_farkas(cert) -> VerifyReport:
    """`sum lambda_i * row_i` is a contradiction, in exact rationals."""
    from fractions import Fraction

    from . import linarith

    p = cert.payload
    rows = linarith.parse_rows(p["rows"])
    lams = [Fraction(x) for x in p["multipliers"]]
    nonneg = all(l >= 0 for l in lams)
    ok, const, strict = linarith.is_contradiction(rows, lams)

    # The rows have to BE the core. Both forms are in the payload and only one
    # was being read, so a certificate could carry a bogus `core_smt2` beside
    # a valid multiplier set -- and `compose` reads the SMT2 for its entailment
    # check, so the two disagreeing is exactly the gap `compose` exists to
    # close, reopened one level down.
    tied = _rows_match_smt2(rows, p.get("core_smt2") or "")

    used = [n for (n, _, _), l in zip(rows, lams) if l]
    checks = [
        (t("verify.core.rows_match"), tied, ""),
        (t("verify.farkas.nonneg"), nonneg, ""),
        (t("verify.core.combination"), ok,
         t("verify.core.closes", const=str(const),
           rel="<" if strict else "<=")),
    ]
    good = nonneg and ok and tied
    return VerifyReport(
        good, "unsat_core", True,
        checks=checks,
        warnings=_core_warnings(cert),
        method_key="verify.core.by_farkas",
        detail=t("verify.core.detail_farkas", n=len(used),
                 names=", ".join(n for n in used if n != "__goal__")),
    )


def _rows_match_smt2(rows, smt2: str) -> bool:
    """Are the stored rows the same system as the stored SMT-LIB2?

    Re-parsed and re-normalised rather than compared as text: the same
    inequality has many spellings, and a check that only caught a different
    spelling would be a check on formatting.
    """
    import z3

    from . import linarith

    if not smt2.strip():
        return False
    try:
        formulas = list(z3.parse_smt2_string(smt2))
    except z3.Z3Exception:
        return False

    want = []
    for f in formulas:
        try:
            poly, rel = linarith.as_row(f)
        except Exception:
            return False
        if rel == "=":
            want.append((poly, "<="))
            want.append(({m: -c for m, c in poly.items()}, "<="))
        else:
            want.append((poly, rel))
    got = [(poly, rel) for _, poly, rel in rows]
    if len(got) != len(want):
        return False
    return all(any(p == q and r == s for q, s in want) for p, r in got)


def _core_warnings(cert) -> list:
    if cert.payload.get("clash"):
        return [t("verify.core.vacuous_named",
                  names=", ".join(cert.payload["clash"]))]
    return [t("verify.core.vacuous")] if cert.payload.get("vacuous") else []


def _verify_core_by_solver(cert, limits) -> VerifyReport:
    import z3

    from .limits import Limits

    lim = limits or Limits()
    s = z3.Solver()
    lim.apply_to(s)
    for f in z3.parse_smt2_string(cert.payload["core_smt2"]):
        s.add(f)
    r = s.check()
    ok = r == z3.unsat
    n = len(cert.payload["names"])
    return VerifyReport(
        ok, "unsat_core", False,
        checks=[(t("verify.core.unsat"), ok, str(r))],
        warnings=_core_warnings(cert),
        detail=t("verify.core.detail", n=n),
    )


def _verify_lp_dual(cert, limits) -> VerifyReport:
    p = cert.payload
    if p.get("exact"):
        return _verify_lp_dual_exact(p)
    return _verify_lp_dual_float(p)


def _verify_lp_dual_exact(p) -> VerifyReport:
    """No tolerances. If this passes, that is the optimum and there is no more to say."""
    from . import exact

    A = [exact.parse_all(r) for r in p["A"]]
    b, c = exact.parse_all(p["b"]), exact.parse_all(p["c"])
    x, y = exact.parse_all(p["primal"]), exact.parse_all(p["dual"])

    # Shapes first. `zip` truncates in silence, so a primal one entry short
    # verified: every check ran over the prefix and none of them noticed the
    # variable that was missing.
    shapes = (len(x) == len(c) and len(y) == len(A)
              and all(len(row) == len(c) for row in A) and len(b) == len(A))
    if not shapes:
        return VerifyReport(
            False, "lp_dual", True,
            checks=[(t("verify.lp.shapes"), False,
                     t("verify.lp.shape_detail", x=len(x), c=len(c),
                       y=len(y), rows=len(A)))],
            detail=t("verify.lp.shape_detail", x=len(x), c=len(c),
                     y=len(y), rows=len(A)))

    rep = exact.check_lp(A, b, c, x, y)

    # Free variables were split as x = x_pos - x_neg. The two columns must be
    # exact negatives, in every row and in the objective, or the certified
    # program is not the one with a free variable in it.
    split_checks = []
    if p.get("free_split"):
        index = {v: j for j, v in enumerate(p.get("var_names") or [])}
        wrong = []
        for v, (pos, neg) in sorted(p["free_split"].items()):
            i, k = index.get(pos), index.get(neg)
            if (i is None or k is None or c[i] != -c[k]
                    or any(row[i] != -row[k] for row in A)):
                wrong.append(v)
        split_checks.append((t("verify.lp.free_split"), not wrong,
                             ", ".join(wrong[:4]) or
                             ", ".join(sorted(p["free_split"]))))

    checks = split_checks + [
        (t("verify.lp.primal_nonneg"), rep["primal_nonneg"], ""),
        (t("verify.lp.primal_feasible"), rep["primal_feasible"], ""),
        (t("verify.lp.dual_nonneg"), rep["dual_nonneg"],
         "min(y)={}".format(exact.serialize(min(y)) if y else "-")),
        (t("verify.lp.dual_feasible"), rep["dual_feasible"], ""),
        (t("verify.lp.strong"), rep["strong_duality"],
         "c.x={} | b.y={}".format(exact.serialize(rep["objective"]),
                                  exact.serialize(rep["dual_bound"]))),
        (t("verify.lp.objective"),
         exact.to_fraction(p["objective"]) == rep["objective"],
         t("verify.lp.declared", value=p["objective"])),
    ]

    warnings = []
    if p.get("integer"):
        # The dual is a bound on the integer optimum, never the optimum
        # itself. Whether the two coincide is a separate, checkable fact.
        pt = p.get("integral_point")
        if pt is None:
            warnings.append(t("verify.lp.ilp_bound"))
        else:
            xi = exact.parse_all(pt)
            feasible = all(v >= 0 for v in xi) and all(
                sum(a * v for a, v in zip(row, xi)) <= rhs
                for row, rhs in zip(A, b))
            value = sum(ci * v for ci, v in zip(c, xi))

            # The point is called integral, so check that it IS. Feasibility
            # and the objective say nothing about it: `x = 3/2` satisfies
            # `x <= 3` and hits its declared value perfectly well, and used to
            # pass. Per-variable, against the DECLARED kind, because a mixed
            # problem's continuous weights are fractional on purpose.
            kinds = p.get("kinds") or {}
            names = p.get("var_names") or []
            off, binary_off = [], []
            for j, v in enumerate(xi):
                name = names[j] if j < len(names) else str(j)
                kind = kinds.get(name, "integer" if p.get("integer")
                                 else "continuous")
                if kind == "continuous":
                    continue
                if v.denominator != 1:
                    off.append(name)
                elif kind == "binary" and v not in (0, 1):
                    binary_off.append(name)
            checks.append((t("verify.lp.integral_integral"),
                           not off and not binary_off,
                           t("verify.lp.offenders",
                             names=", ".join((off + binary_off)[:3]) or "-")))
            checks.append((t("verify.lp.integral_feasible"), feasible,
                           t("verify.lp.declared",
                             value=exact.serialize(value))))
            checks.append((t("verify.lp.integral_declared"),
                           exact.to_fraction(p["integral_objective"]) == value,
                           p["integral_objective"]))
            if value != rep["objective"]:
                # In the declared sense, like everything else a reader sees.
                f = -1 if p.get("sense") == "min" else 1
                warnings.append(t("verify.lp.ilp_gap",
                                  value=exact.serialize(f * value),
                                  bound=exact.serialize(f * rep["objective"])))

    # The declared loads, recomputed from the primal rather than believed.
    for load in p.get("loads") or []:
        xs = {v: f for v, f in zip(p.get("var_names") or [],
                                   exact.parse_all(p["primal"] or []))}
        got = sum((exact.to_fraction(c) * xs.get(v, 0)
                   for v, c in (load.get("coeffs") or {}).items()),
                  exact.to_fraction(0))
        want = exact.to_fraction(load["bound"])
        declared = exact.to_fraction(load["achieved"])
        sense = load.get("sense", "<=")
        holds = (got <= want if sense == "<=" else
                 got >= want if sense == ">=" else got == want)
        checks.append((t("verify.lp.load", name=load["name"]),
                       holds and got == declared,
                       t("verify.lp.load_detail", got=exact.serialize(got),
                         sense=sense, bound=load["bound"],
                         slack=load.get("slack", "?"))))

    # A target turns "here is the optimum" into "here is a bound that meets
    # what you needed", which for an existence proof is the whole question.
    if p.get("target") is not None:
        want = exact.to_fraction(p["target"])
        value = exact.to_fraction(p.get("integral_objective")
                                  or p["objective"])
        if value >= want:
            checks.append((t("verify.lp.target"), True,
                           t("verify.lp.margin", value=exact.serialize(value),
                             target=p["target"],
                             margin=exact.serialize(value - want))))
        else:
            warnings.append(t("verify.lp.short", value=exact.serialize(value),
                              target=p["target"],
                              deficit=exact.serialize(want - value)))

    # THE FRAME. `A`, `b`, `c`, `primal` and `dual` are stored in the
    # internal MAXIMISED system, because that is the one the arithmetic above
    # closes: `c.x == b.y` only holds there. For `sense: min` the declared
    # optimum is the negation, and nothing here used to perform it -- so a
    # minimisation whose answer is 3/2 was reported, archived and re-verified
    # as -3/2, and it verified, because the artefact was consistent with
    # itself and wrong about what it claimed. Found by putting a minimisation
    # ILP through `opt`, which is the shape of every "minimum deletion"
    # question.
    flip = -1 if p.get("sense") == "min" else 1
    value = exact.serialize(flip * rep["objective"])

    # The declared-sense numbers, RECOMPUTED from the system above rather than
    # read. A field nothing checks is a field that can be forged, and this one
    # is the number a reader of the JSON will quote.
    declared = p.get("declared") or {}
    if declared:
        want = {"objective": flip * rep["objective"]}
        if p.get("integral_objective") is not None:
            want["integral_objective"] = flip * exact.to_fraction(
                p["integral_objective"])
        off = sorted(k for k, v in want.items()
                     if k in declared
                     and exact.to_fraction(declared[k]) != v)
        checks.append((t("verify.lp.declared_sense"), not off,
                       t("verify.lp.declared_sense_detail",
                         sense=p.get("sense") or "max",
                         names=", ".join(off) or "-",
                         value=exact.serialize(want["objective"]))))
    detail = (t("verify.lp.exact.detail", value=value)
              if not p.get("integer")
              else t("verify.lp.ilp.detail",
                     value=(exact.serialize(
                         flip * exact.to_fraction(p["integral_objective"]))
                         if p.get("integral_objective") is not None else "-"),
                     bound=value))
    return VerifyReport(
        all(k[1] for k in checks), "lp_dual", True, checks=checks,
        warnings=warnings, detail=detail,
    )


def _verify_lp_dual_float(p) -> VerifyReport:
    A, b, c, y = p["A"], p["b"], p["c"], p["dual"]
    tol = 1e-6
    checks = []

    nonneg = all(v >= -tol for v in y)
    checks.append(
        (t("verify.lp.dual_nonneg"), nonneg,
         "min(y)={:.6g}".format(min(y) if y else 0))
    )

    m, ncols = len(A), len(c)
    feas, worst = True, 0.0
    for j in range(ncols):
        s = sum(A[i][j] * y[i] for i in range(m))
        if s < c[j] - tol:
            feas = False
            worst = max(worst, c[j] - s)
    checks.append(
        (t("verify.lp.dual_feasible"), feas, "max violation={:.3g}".format(worst))
    )

    bound = sum(b[i] * y[i] for i in range(m))
    tight = abs(bound - p["objective"]) <= 1e-4 * max(1.0, abs(p["objective"]))
    checks.append(
        (t("verify.lp.bound"), tight,
         "b.y={:.6g} vs obj={:.6g}".format(bound, p["objective"]))
    )

    # The declared-sense number, checked here too. A float certificate is
    # loose, not unchecked, and an unchecked field is a field that can be
    # forged whatever tier it sits in.
    declared = p.get("declared") or {}
    agrees = True
    if "objective" in declared:
        flip = -1 if p.get("sense") == "min" else 1
        want = flip * float(p["objective"])
        got = float(declared["objective"])
        agrees = abs(got - want) <= 1e-4 * max(1.0, abs(want))
        checks.append((t("verify.lp.declared_sense"), agrees,
                       t("verify.lp.declared_sense_detail",
                         sense=p.get("sense") or "max",
                         names="-" if agrees else "objective",
                         value="{:.6g}".format(want))))

    ok = nonneg and feas and tight and agrees
    return VerifyReport(
        ok, "lp_dual", True, checks=checks,
        warnings=[t("verify.lp.float.warning")],
        detail=t("verify.lp.float.detail"),
    )


def _verify_cegis(cert, limits) -> VerifyReport:
    import z3

    from .limits import Limits

    lim = limits or Limits()
    p = cert.payload
    checks = []

    decls: dict = {}
    impl_cons = z3.And(*z3.parse_smt2_string(p["smt2"]["impl_constraints"], decls=decls))
    behav = z3.And(*z3.parse_smt2_string(p["smt2"]["behavior"], decls=decls))
    corr = z3.And(*z3.parse_smt2_string(p["smt2"]["correctness"], decls=decls))

    fix = []
    for name, pair in p["implementation"].items():
        sort, val = pair
        fix.append(_const(z3, name, sort) == _value(z3, sort, val))

    s = z3.Solver()
    lim.apply_to(s)
    s.add(impl_cons, *fix)
    r1 = s.check()
    ok1 = r1 == z3.sat
    checks.append((t("verify.cegis.impl_ok"), ok1, str(r1)))

    s = z3.Solver()
    lim.apply_to(s)
    s.add(behav, z3.Not(corr), *fix)
    r2 = s.check()
    ok2 = r2 == z3.unsat
    checks.append((t("verify.cegis.no_ce"), ok2, str(r2)))

    return VerifyReport(
        ok1 and ok2, "cegis", False, checks=checks,
        detail=t("verify.cegis.detail", iterations=p["iterations"],
                 ces=len(p["counterexamples"])),
    )


def _verify_cnf_model(cert, limits) -> VerifyReport:
    from .cnf import CNF

    p = cert.payload
    cnf = CNF.from_dimacs(p["dimacs"])
    true = set(p["true_vars"])

    def lit_true(l):
        return (abs(l) in true) == (l > 0)

    bad = [c for c in cnf.clauses if not any(lit_true(l) for l in c)]
    ok = not bad
    return VerifyReport(
        ok, "cnf_model", True,
        checks=[(t("verify.cnf.satisfies", n=len(cnf.clauses)), ok,
                 t("verify.cnf.unsatisfied", n=len(bad)))],
        detail="" if ok else t("verify.cnf.first_failure", clause=bad[0]),
    )


def _verify_drat(cert, limits) -> VerifyReport:
    from . import drup
    from .cnf import CNF
    from .limits import Limits

    lim = limits or Limits()
    p = cert.payload
    cnf = CNF.from_dimacs(p["dimacs"])
    checks = [(
        t("verify.drat.formula", n=p["nclauses"]),
        len(cnf.clauses) == p["nclauses"],
        "read {}".format(len(cnf.clauses)),
    )]
    rep = drup.check(cnf.clauses, p["proof"],
                     timeout_s=max(1.0, lim.timeout_ms / 1000))
    checks.append((t("verify.drat.steps"), rep.ok, rep.detail))
    checks.append((t("verify.drat.empty"), rep.derived_empty, ""))
    if drup.drat_trim_available():
        ext = drup.check_with_drat_trim(
            p["dimacs"], p["proof"], timeout_s=max(1.0, lim.timeout_ms / 1000))
        checks.append((t("verify.drat.external"), ext.ok, ext.detail))

    ok = all(c[1] for c in checks)
    return VerifyReport(
        ok, "drat", True, checks=checks,
        detail=t("verify.drat.detail", steps=rep.steps, rup=rep.rup_steps,
                 rat=rep.rat_steps, **{"del": rep.deletions},
                 ms=rep.elapsed_ms),
    )


def _verify_shrink_graph(cert, limits) -> VerifyReport:
    from pathlib import Path

    from .engines.shrink import _reductions
    from .graphs import Graph, compile_filters
    from .spec import load_spec

    p = cert.payload
    checks = []

    src = Path(p["spec_path"] or "")
    if not p["spec_path"] or not src.is_file():
        return VerifyReport(False, "shrink_graph", True,
                            detail=t("verify.shrink.spec_missing",
                                     path=p["spec_path"] or "-"))
    got = hashlib.sha256(src.read_bytes()).hexdigest()
    checks.append((t("verify.shrink.spec_same"), got == p["spec_sha256"], got[:16]))

    spec = load_spec(src)
    fns = compile_filters(p["filters"])
    minimal = Graph.from_graph6(p["minimal"])

    def is_ce(g):
        if g.n == 0:
            return False
        if any(not f(g) for _, f in fns):
            return False
        try:
            return not spec.predicate(g)
        except Exception:  # noqa: BLE001
            return False

    checks.append((t("verify.shrink.still_ce"), is_ce(minimal),
                   "n={} m={}".format(minimal.n, minimal.m)))

    recomputed = list(_reductions(minimal))
    checks.append((t("verify.shrink.complete"),
                   len(recomputed) == len(p["blocked"]),
                   t("verify.shrink.computed", computed=len(recomputed),
                     declared=len(p["blocked"]))))
    survivors = [op for op, cand in recomputed if is_ce(cand)]
    checks.append((t("verify.shrink.none_survive"), not survivors,
                   t("verify.shrink.survivors", names=survivors[:5])))

    ok = all(c[1] for c in checks)
    return VerifyReport(ok, "shrink_graph", True, checks=checks,
                        detail=t("verify.shrink.detail"))


def _verify_mus(cert, limits) -> VerifyReport:
    from . import drup

    p = cert.payload
    checks = []

    orig = {tuple(sorted(c)) for c in p["original"]}
    subset = all(tuple(sorted(c)) in orig for c in p["mus"])
    checks.append((t("verify.mus.subset"), subset,
                   t("verify.mus.subset.detail", mus=len(p["mus"]),
                     total=len(p["original"]))))

    rep = drup.check([list(c) for c in p["mus"]], p["proof"],
                     timeout_s=60.0)
    checks.append((t("verify.mus.proof"), rep.ok and rep.derived_empty,
                   rep.detail))

    # minimalidad: un modelo por clausula, que satisface el MUS sin ella
    bad = []
    idx_by_pos = list(p["mus_indices"])
    for pos, gi in enumerate(idx_by_pos):
        w = set(p["witnesses"].get(str(gi), []))
        rest = [c for k, c in enumerate(p["mus"]) if k != pos]
        for c in rest:
            if not any((abs(l) in w) == (l > 0) for l in c):
                bad.append(gi)
                break
    checks.append((t("verify.mus.minimal"), not bad,
                   t("verify.mus.no_witness", n=len(bad))))

    ok = all(c[1] for c in checks)
    return VerifyReport(ok, "mus", True, checks=checks,
                        detail=t("verify.mus.detail"))


def _verify_bisect(cert, limits) -> VerifyReport:
    p = cert.payload
    checks, free = [], True

    for side, label in (("good_cert", t("verify.bisect.good", t=p["good_t"])),
                        ("bad_cert", t("verify.bisect.bad", t=p["bad_t"]))):
        sub = p.get(side)
        if sub is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        free = free and rep.solver_free
        checks.append((label + " ({})".format(sub["kind"]), rep.ok, rep.detail))

    width = abs(p["good_t"] - p["bad_t"])
    tight = width <= p["tol"] + 1e-12
    checks.append((t("verify.bisect.brackets"), tight,
                   t("verify.bisect.width", width=width, tol=p["tol"])))

    up = p["direction"] == "min_true"
    oriented = (p["good_t"] > p["bad_t"]) if up else (p["good_t"] < p["bad_t"])
    checks.append((t("verify.bisect.orientation", direction=p["direction"]),
                   oriented, t("verify.bisect.sides", good=p["good_t"],
                              bad=p["bad_t"])))

    ok = all(c[1] for c in checks)
    return VerifyReport(ok, "bisect", free, checks=checks,
                        detail=t("verify.bisect.detail"))


def _verify_family(g6, n, filters, want_hash) -> list:
    """Checks shared by graph_set and sweep."""
    from .graphs import FILTERS, Graph, is_isomorphic, wl_signature

    checks = []
    h = hashlib.sha256("\n".join(sorted(g6)).encode()).hexdigest()
    checks.append((t("verify.family.hash"), h == want_hash, h[:16]))

    graphs = [Graph.from_graph6(s) for s in g6]
    bad_n = [g for g in graphs if g.n != n]
    checks.append((t("verify.family.n", n=n), not bad_n,
                   t("verify.family.count", n=len(bad_n))))

    bad_f, unverifiable = [], []
    for name in filters:
        if name.startswith("fn:"):
            # A programmable filter lives in the spec, not in the catalogue:
            # it cannot be re-checked from the certificate alone.
            unverifiable.append(name)
            continue
        f = FILTERS.get(name)
        if f is None:
            bad_f.append("unknown filter: " + name)
            continue
        bad_f += [name + " fails" for g in graphs if not f(g)]
    detail = t("verify.family.failures", n=len(bad_f))
    if unverifiable:
        detail += "; " + t("verify.family.programmable",
                           names=", ".join(unverifiable))
    checks.append((t("verify.family.filters"), not bad_f, detail))

    buckets: dict = {}
    for g in graphs:
        buckets.setdefault(wl_signature(g), []).append(g)
    dup = 0
    for grp in buckets.values():
        for i in range(len(grp)):
            for j in range(i + 1, len(grp)):
                if is_isomorphic(grp[i], grp[j]):
                    dup += 1
    checks.append((t("verify.family.iso"), dup == 0,
                   t("verify.family.duplicates", n=dup)))
    return checks


def _verify_synth_proved(cert, limits) -> VerifyReport:
    p = cert.payload
    checks, free = [], True
    for key, label in (("synth", t("verify.synth.bounded")),
                       ("universal", t("verify.synth.universal"))):
        sub = p.get(key)
        if sub is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        free = free and rep.solver_free
        checks.append((label + " ({})".format(sub["kind"]), rep.ok, rep.detail))
    return VerifyReport(
        all(k[1] for k in checks), "synth_proved", free, checks=checks,
        detail=t("verify.synth.detail", candidate=p.get("candidate")),
    )


def _verify_farkas(cert, limits) -> VerifyReport:
    """Multiply, add, look. No solver, no search -- this is the good kind."""
    from fractions import Fraction

    from . import exact, linarith

    p = cert.payload
    rows = linarith.parse_rows(p["rows"])
    lams = [Fraction(x) for x in p["multipliers"]]
    checks = []

    checks.append((t("verify.farkas.nonneg"), all(l >= 0 for l in lams),
                   t("verify.farkas.count",
                     n=sum(1 for l in lams if l > 0), total=len(lams))))

    total = linarith.combination(rows, lams)
    leftover = {m: c for m, c in total.items()
                if m != linarith.CONST and c != 0}
    checks.append((t("verify.farkas.cancels"), not leftover,
                   t("verify.farkas.leftover",
                     names=", ".join(" ".join(m) for m in list(leftover)[:3]))))

    ok, const, strict = linarith.is_contradiction(rows, lams)
    checks.append((t("verify.farkas.closes"), ok,
                   t("verify.farkas.closing", const=exact.serialize(const),
                     rel="<" if strict else "<=")))
    checks.append((t("verify.farkas.declared"),
                   exact.to_fraction(p["constant"]) == const
                   and bool(p["strict"]) == bool(strict),
                   p["constant"]))

    warnings = []
    if p.get("vacuous"):
        warnings.append(t("verify.farkas.vacuous"))
    if p.get("nonlinear"):
        warnings.append(t("verify.farkas.derived",
                          n=len(rows) - p.get("base_rows", len(rows))))
    return VerifyReport(
        all(c[1] for c in checks), "farkas", True, checks=checks,
        warnings=warnings,
        detail=t("verify.farkas.detail", n=len(rows)),
    )


def _verify_shrink_domain(cert, limits) -> VerifyReport:
    from .spec import Outcome, load_spec

    p = cert.payload
    checks = []

    # `Path("")` is `.`, which exists and is a directory: without the first
    # test this reads a folder and dies with a permission error instead of
    # saying the certificate never recorded where its spec was.
    src = Path(p["spec_path"] or "")
    if not p["spec_path"] or not src.is_file():
        return VerifyReport(False, "shrink_domain", True,
                            detail=t("verify.shrink.spec_missing",
                                     path=p["spec_path"] or "-"))
    got = hashlib.sha256(src.read_bytes()).hexdigest()
    checks.append((t("verify.shrink.spec_same"), got == p["spec_sha256"],
                   got[:16]))

    spec = load_spec(src)
    # Resolve a named reducer the same way the engine did, or the replay
    # would walk a different descent than the one recorded.
    reduce = spec.reducer()
    if reduce is None:
        return VerifyReport(False, "shrink_domain", True, checks=checks,
                            detail=t("engine.shrink.no_reduce"))
    by_id = {spec.id_of(i): i for i in spec.enumerate()}
    start = by_id.get(p["original"])
    if start is None:
        checks.append((t("verify.shrink.replay"), False,
                       t("verify.shrink.item_missing", id=p["original"])))
        return VerifyReport(False, "shrink_domain", True, checks=checks)

    # Replay the recorded descent rather than redoing the search.
    item = start
    for step in p["trace"]:
        options = list(reduce(item))
        if step["index"] >= len(options):
            item = None
            break
        item = options[step["index"]]
        if spec.id_of(item) != step["to"]:
            item = None
            break
    replayed = item is not None and spec.id_of(item) == p["minimal"]
    checks.append((t("verify.shrink.replay"), replayed,
                   t("verify.shrink.replay_detail", steps=len(p["trace"]),
                     item=p["minimal"])))

    def is_ce(x):
        try:
            r = spec.predicate(x) if spec.predicate else True
        except Exception:  # noqa: BLE001
            return False
        ok = r.ok if isinstance(r, Outcome) else bool(r)
        return ok is False

    if replayed:
        checks.append((t("verify.shrink.still_ce_item"), is_ce(item),
                       p["minimal"]))
        survivors = [spec.id_of(c) for c in reduce(item) if is_ce(c)]
        checks.append((t("verify.shrink.none_survive"), not survivors,
                       t("verify.shrink.survivors", names=survivors[:5])))

    return VerifyReport(
        all(c[1] for c in checks), "shrink_domain", True, checks=checks,
        detail=t("verify.shrink.detail"),
    )


def _verify_core_matrix(cert, limits) -> VerifyReport:
    p = cert.payload
    checks, free = [], True

    # Each column is an ordinary core; verifying them is verifying the table.
    for goal, sub in p.get("cores", {}).items():
        rep = verify(Certificate.from_dict(sub), limits)
        free = free and rep.solver_free
        checks.append((t("verify.matrix.goal", goal=goal, kind=sub["kind"]),
                       rep.ok, rep.detail))

    # The table must say exactly what the cores say.
    bad = 0
    for goal, sub in p.get("cores", {}).items():
        used = set(sub["payload"]["names"]) - {"__goal__"}
        for h in p["hypotheses"]:
            if p["table"][h][goal] != (h in used):
                bad += 1
    checks.append((t("verify.matrix.agrees"), bad == 0,
                   t("verify.matrix.mismatch", n=bad)))

    warnings = []
    if p.get("inconclusive"):
        warnings.append(t("verify.matrix.inconclusive", n=len(p["inconclusive"])))

    return VerifyReport(
        all(c[1] for c in checks), "core_matrix", free, checks=checks,
        warnings=warnings,
        detail=t("verify.matrix.detail", goals=len(p["goals"]),
                 hyps=len(p["hypotheses"])),
    )


def _verify_sweep_range(cert, limits) -> VerifyReport:
    p = cert.payload
    checks, free, warnings = [], True, []

    sizes = p["sizes"]
    checks.append((t("verify.range.ordered"), sizes == sorted(sizes),
                   "n = {}".format(sizes)))

    for e in p["entries"]:
        sub = e.get("cert")
        label = t("verify.range.size", n=e["n"], verdict=e["verdict"])
        if sub is None:
            checks.append((label, False, t("verify.bisect.no_cert")))
            continue
        rep = verify(Certificate.from_dict(sub), limits)
        free = free and rep.solver_free
        checks.append((label, rep.ok, rep.detail))

    first = p.get("first_failure")
    below = [e for e in p["entries"]
             if first is not None and e["n"] < first and e["verdict"] == "refuted"]
    checks.append((t("verify.range.nothing_below"), not below,
                   "" if first is None else "first failure at n={}".format(first)))

    if p.get("stopped_early"):
        warnings.append(t("verify.range.stopped"))

    # Vacuity, recomputed from each size's family rather than read. Absent
    # from certificates before 0.17, which then say nothing about it.
    if "vacuous" in p:
        want = sorted(e["n"] for e in p["entries"] if e.get("cert")
                      and (e["cert"].get("payload") or {}).get("family_count") == 0)
        checks.append((t("verify.range.vacuous"),
                       sorted(p.get("vacuous") or []) == want,
                       ", ".join(map(str, want)) or "-"))
        if want:
            warnings.append(t("verify.range.vacuous_warning",
                              sizes=", ".join(map(str, want))))

    return VerifyReport(
        all(c[1] for c in checks), "sweep_range", free, checks=checks,
        warnings=warnings,
        detail=t("verify.range.detail", sizes=len(sizes),
                 first="n={}".format(first) if first is not None else "-"),
    )


def _verify_domain_sweep(cert, limits) -> VerifyReport:
    p = cert.payload
    ids = p["ids"]
    h = hashlib.sha256(chr(10).join(sorted(ids)).encode()).hexdigest()
    checks = [(t("verify.family.hash"), h == p["ids_sha256"], h[:16]),
              (t("verify.domain.unique"), len(set(ids)) == len(ids),
               t("verify.domain.duplicates", n=len(ids) - len(set(ids))))]
    checks += _verify_entries_and_stats(p, limits)
    if p.get("orbits"):
        from . import orbits as orb

        checks += orb.check(p)

    pchecks, pwarn, level = _predicate_level(cert, limits, "domain")
    if p.get("by_orbit"):
        pchecks, pwarn = _by_orbit_checks(p, pchecks, pwarn)
    checks += pchecks
    free = cert.solver_free and level is not REPRODUCIBLE

    return VerifyReport(
        all(c[1] for c in checks), "domain_sweep", free, checks=checks,
        method_key=_method(level), warnings=_sweep_warnings(p) + pwarn,
        detail=t("verify.sweep.level." + level) + " -- "
        + t("verify.domain.detail", n=p["count"]),
    )


def _verify_entries_and_stats(p, limits) -> list:
    """The stored certificates and the calibration. Shared by both sweep kinds.

    Note what is NOT here: any claim about evaluations that stored no
    certificate. That belongs to `_predicate_level`, because it is a warning
    and not a check -- there is nothing to tick.
    """
    checks = []
    entries = p.get("entries", [])
    with_cert = [e for e in entries if e.get("cert")]
    if with_cert:
        bad = [_entry_id(e) for e in with_cert
               if not verify(Certificate.from_dict(e["cert"]), limits).ok]
        checks.append(
            (t("verify.sweep.predicate"), not bad,
             t("verify.sweep.entries", certified=len(with_cert),
               total=p.get("evaluations", len(entries)),
               failing="" if not bad else t("verify.sweep.failing",
                                            names=", ".join(bad[:3]))))
        )
    vals = p.get("values") or []
    if vals and p.get("stats"):
        from . import exact

        recomputed = exact.stats([v["value"] for v in vals])
        declared = {k: exact.to_fraction(v) for k, v in p["stats"].items()}
        checks.append((t("verify.sweep.stats"),
                       all(recomputed[k] == declared[k] for k in declared),
                       t("verify.sweep.values", n=len(vals))))
    return checks


def _entry_id(e) -> str:
    """The item's id.

    `id` is the field. `g6` is what it used to be called, back when the only
    domain was graphs -- which is how a DomainSpec ended up labelling triples
    of sets as "graph6". Certificates issued before the rename are still read.
    """
    return e.get("id") or e.get("g6") or "?"


def _predicate_level(cert, limits, kind):
    """What this sweep establishes about the predicate, said out loud.

    Returns (checks, warnings, level). The warning fires on a PASSING sweep
    exactly as it does on a refuted one -- that symmetry is the point. A pass
    over eleven thousand uncertified booleans is the case where a green banner
    does the most damage, because there is no counterexample to go and look at.
    """
    p = cert.payload
    checks, warnings = [], []

    if p.get("no_predicate"):
        # A calibration run measures; it refutes nothing, so there is no
        # predicate to certify and saying "fully certified" would be as wrong
        # as saying "uncertified". The stats are checked exactly, elsewhere.
        return checks, warnings, NO_PREDICATE

    ok, detail = _replay(cert, limits, kind)
    if ok is None:
        warnings.append(t("verify.sweep.replay.skipped", reason=detail))
    else:
        checks.append((t("verify.sweep.replay"), ok, detail))

    level = sweep_strength(p, ok is True)
    evaluations = p.get("evaluations", 0)
    uncertified = max(0, evaluations - p.get("certified", 0))
    # When the replay DISAGREED, the failed check is the headline. Adding
    # "only the domain was checked" underneath would read as a lesser problem
    # than "this certificate no longer describes what the spec does".
    if uncertified and ok is not False:
        warnings.append(t("verify.sweep.uncertified." + level,
                          n=uncertified, total=evaluations))
    return checks, warnings, level


def _by_orbit_checks(p, checks, warnings):
    """What a --by-orbit run has to say, the same for both sweep kinds.

    The degenerate case is not a failure. When every orbit is a singleton --
    which is exactly what happens on a graph sweep quotiented by isomorphism,
    since the enumerator already did that -- nothing was inferred, there are
    no non-representatives to look at, and the invariance assumption was never
    used. That run IS a full sweep and says so.
    """
    spot = p.get("spot_checks") or []
    inferred = max(0, p.get("evaluations", 0) - p.get("evaluated", 0))
    if not inferred:
        warnings.insert(0, t("verify.orbits.nothing_inferred"))
        return checks, warnings

    checks.append((t("verify.orbits.spot"),
                   bool(spot) and all(s_.get("agreed") for s_ in spot),
                   t("verify.orbits.spot_n", n=len(spot))))
    warnings.insert(0, t("verify.orbits.assumed",
                         evaluated=p.get("evaluated", "?"), n=len(spot)))
    return checks, warnings


def _method(level) -> str:
    return "cli.verify.by_replay" if level == REPRODUCIBLE else ""


def _sweep_warnings(p) -> list:
    """Only what `_predicate_level` does not already say, and better.

    The old "N of M stored entries lack a certificate" warning is gone: it
    counted the stored counterexamples, so it was silent on a passing sweep
    and, on a refuted one, it said less than the level warning that replaced
    it. Two warnings about the same gap make readers skim both.
    """
    out = []
    c = p.get("counts", {})
    if c.get("errors") or c.get("inconclusive"):
        out.append(t("verify.sweep.unevaluated",
                     n=c.get("errors", 0) + c.get("inconclusive", 0)))
    if any(r.get("witnesses") for r in (p.get("orbits") or [])):
        # The witnesses show members of an orbit are the SAME object relabelled.
        # Nothing here shows two REPRESENTATIVES are different ones, and a
        # reader who takes the first for the second has over-read it.
        out.append(t("verify.orbits.one_way"))
    return out


def _verify_sweep(cert, limits) -> VerifyReport:
    p = cert.payload
    checks = _verify_family(p["family_graph6"], p["n"], p["filters"],
                            p["family_sha256"])
    checks += _verify_entries_and_stats(p, limits)
    if p.get("orbits"):
        from . import orbits as orb

        checks += orb.check(p)

    pchecks, pwarn, level = _predicate_level(cert, limits, "sweep")
    if p.get("by_orbit"):
        pchecks, pwarn = _by_orbit_checks(p, pchecks, pwarn)
    checks += pchecks

    # Replaying means running the spec's predicate, which is arbitrary Python
    # and may well call a solver. Claiming "verified without a solver" after
    # that would be the same overclaim in a different place.
    free = cert.solver_free and level is not REPRODUCIBLE

    return VerifyReport(
        all(k[1] for k in checks), "sweep", free, checks=checks,
        method_key=_method(level), warnings=_sweep_warnings(p) + pwarn,
        detail=t("verify.sweep.level." + level) + " -- "
        + t("verify.sweep.detail", n=p["family_count"]),
    )


def _verify_graph_set(cert, limits) -> VerifyReport:
    p = cert.payload
    g6 = p["graph6"]
    checks = _verify_family(g6, p["n"], p["filters"], p["sha256"])
    return VerifyReport(
        all(c[1] for c in checks), "graph_set", True, checks=checks,
        detail=t("verify.sweep.detail", n=len(g6)),
    )


# ---------------------------------------------------------------------------


def _const(z3, name, sort):
    return {"Int": z3.Int, "Real": z3.Real, "Bool": z3.Bool}[sort](name)


def _value(z3, sort, val):
    if sort == "Int":
        return z3.IntVal(val)
    if sort == "Real":
        return z3.RealVal(val)
    if sort == "Bool":
        return z3.BoolVal(val)
    raise ValueError("sort no soportado: " + str(sort))


#: Every certificate kind, and what re-checks it. A kind that is not here
#: verifies as unknown rather than as valid, which is the safe direction.
#:
#: Lifted out of `verify()` for two reasons. It was rebuilt on every call
#: -- forty-seven entries, per certificate, in a loop that `status` runs
#: over a whole directory -- and nothing outside could read it, so the
#: catalogue that keeps the documents honest had no source for the kinds
#: and a new kind meant editing a table nobody could see.
VERIFIERS = {
    "model": _verify_model,
    "unsat_core": _verify_unsat_core,
    "lp_dual": _verify_lp_dual,
    "cegis": _verify_cegis,
    "graph_set": _verify_graph_set,
    "cnf_model": _verify_cnf_model,
    "drat": _verify_drat,
    "shrink_graph": _verify_shrink_graph,
    "mus": _verify_mus,
    "bisect": _verify_bisect,
    "sweep": _verify_sweep,
    "domain_sweep": _verify_domain_sweep,
    "sweep_range": _verify_sweep_range,
    "core_matrix": _verify_core_matrix,
    "shrink_domain": _verify_shrink_domain,
    "farkas": _verify_farkas,
    "synth_proved": _verify_synth_proved,
    "proof": _verify_proof,
    "ball": _verify_ball,
    "induction": _verify_induction,
    "orbit_witnesses": _verify_orbit_witnesses,
    "ideal": _verify_ideal,
    "resultant": _verify_resultant,
    "first_entry": _verify_first_entry,
    "first_moment": _verify_first_moment,
    "symmetry_reduction": _verify_symmetry_reduction,
    "hypothesis_audit": _verify_hypothesis_audit,
    "integer_matrix": _verify_integer_matrix,
    "symmetric_inertia": _verify_symmetric_inertia,
    "variable_range": _verify_variable_range,
    "dependency_cycle": _verify_dependency_cycle,
    "lean_binding": _verify_lean_binding,
    "toric_cone": _verify_toric_cone,
    "affine_semigroup": _verify_affine_semigroup,
    "clique_lp": _verify_clique_lp,
    "capacity_profile": _verify_capacity_profile,
    "equitable_quotient": _verify_equitable_quotient,
    "linear_system": _verify_linear_system,
    "parametric_symmetry": _verify_parametric_symmetry,
    "ratio_bound": _verify_ratio_bound,
    "family_extremum": _verify_family_extremum,
    "integer_peak": _verify_integer_peak,
    "parametric_bound": _verify_parametric_bound,
    "exact_cover": _verify_exact_cover,
    "sos": _verify_sos,
    "number": _verify_number,
    "mixed_design": _verify_mixed_design,
    "gap": _verify_gap,
    "farkas_ray": _verify_farkas_ray,
    "branch_bound": _verify_branch_bound,
    "branch_frontier": _verify_branch_frontier,
    "asymptotic": _verify_asymptotic,
}
