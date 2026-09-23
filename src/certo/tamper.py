"""Forge a certificate on purpose, and see whether it is caught.

THE FAILURE THIS ANSWERS. Every test that feeds a verifier something the
PRODUCER built shares the producer's assumptions, so a contract misread in
both places passes twice. Two certificates shipped in 0.6.0 that `verify`
rejects, and 339 tests could not have caught either. The fix was to go the
other way: take a valid certificate, change one payload field, and require the
change to be noticed.

That battery has lived in certo's own test suite since. A user rebuilding it
around THEIR certificates asked for it as a tool -- "una batería automática
que modifique deliberadamente testigos, objetivos y capacidades, y exija su
rechazo" -- which it should have been all along. It is the same code, in the
package instead of beside it, so there is one implementation rather than two
that drift.

WHAT AN UNCAUGHT FIELD MEANS, and why this REPORTS rather than asserts. A
mutation that flips no check says one of two things:

    the field carries no claim -- and does not belong in a payload that
    claims to be checkable

    or it carries one and nothing is checking it

Both are worth knowing and only the reader can tell them apart, so nothing
here fails a run on that basis. For certo's own kinds the judgement has been
made already and is recorded in `DESCRIPTIVE` and `WEAKENING` below, by name
and with a reason, so excusing a field is a decision somebody took rather than
a rule that swallowed it.
"""
from __future__ import annotations

import json
from fractions import Fraction

#: Fields that carry NO CLAIM: names, counts, prose, and data the checked
#: content is derived from. Mutating one should change nothing, and each is
#: here because somebody decided it rather than because a rule swallowed it.
DESCRIPTIVE = {
    "title", "describe", "conclusion", "note", "spec_path", "spec_sha256",
    "engine", "names", "var_names", "dropped", "hypotheses", "goals",
    "filters", "mode", "id", "labelled", "spot_checks", "family_graph6",
    "values", "stats", "counts", "evaluations", "certified", "evaluated",
    "orbits", "sizes", "first_failure", "stopped_early", "inconclusive",
    "skeleton_from", "kinds", "level", "tight", "part_report", "sorts",
    "clash", "expect", "cancelled", "loads", "prec", "backend", "iterations",
    "candidate", "counterexamples", "steps", "trace", "blocked", "witnesses",
    "bridge", "bridges", "used", "unused", "lemmas", "base", "k0",
    "base_upto", "step_from", "question", "cores", "table", "claim",
    # `peak`: the name of the integer variable. It labels a column of the
    # objective and nothing else -- rename it in both places and every
    # coefficient, every check and the answer are identical.
    "variable",
    "order", "deg_f", "deg_g", "lead_f", "lead_g", "lead_f_constant",
    "lead_g_constant", "multiplicities", "max_size", "half_degree",
    "original_sense", "original_optimum", "discrete_gain", "conditional",
    # `sos` keeps three counters beside the content: the squares themselves
    # are `terms`, and `poly` is what they have to sum to. Both are checked.
    "squares", "basis_size", "basis",
    # A sweep whose predicate cannot be re-run says so in a warning, loudly,
    # and then nothing checks the outcomes -- which is the honest behaviour
    # and is why mutating them changes no check.
    "outcomes", "outcomes_sha256", "no_predicate", "by_orbit", "count",
    "family_count", "nvars",
    # `sos` records a denominator that `_verify_sos` never reads: the terms
    # carry their own coefficients and are expanded and compared directly.
    # Excused because it is genuinely inert, and flagged here because an inert
    # field in a payload that claims to be checkable is worth knowing about.
    "denominator",
    # Dropping the final empty clause from a DRAT proof is accepted, because
    # the prefix that remains still propagates to a conflict -- the formula is
    # still refuted. Truncating further IS caught, which is the property that
    # matters.
    "proof",
    # `affine_semigroup`: the grading is the REASON the searches terminate,
    # not a claim of its own, and its own check refuses one that is not valid.
    # Any grading that survives that check defines a search space containing
    # every representation of every point -- a larger `u` only widens it -- so
    # every absence in the payload stays proven under it. Swapping one valid
    # grading for another changes no answer.
    "grading",
    # And the sentence explaining that normality is never asserted. The claim
    # itself is `normal is None`, which its own check enforces; this is prose.
    "normal_why",
    # `capacity_profile`: whether the profile was searched for or handed over,
    # and how many programs the search solved. Provenance of the PROPOSAL --
    # the certificate says the same thing either way, because a discovered
    # profile is admitted by the same checks as a written one.
    "discovered", "solves",
}

#: Mutations that make the certificate claim LESS. Not catching these is
#: correct: an exact cover really is an at-least cover, and a design that
#: stops claiming global optimality is making a smaller true statement. A
#: forgery claims MORE; weakening is a reader's loss, not a lie.
WEAKENING = {
    "exact",            # exact cover -> at-least cover
    "cliques",          # stops asserting the parts are cliques
    "nonlinear",        # farkas: changes which tactic is claimed
    "globally_optimal",  # mixed: drops the optimality claim
    "integer",          # lp_dual: an ILP flag with no integral point warns
    "vacuous",          # dropping a warning flag does not create a claim
    "sense",            # reading a max as a min makes the bound weaker
    "target",           # a target is a question, not an assertion
    "relaxation",       # mixed: an optional side certificate
    "residual",         # mixed: checked when present; absence is not a claim
    "system",           # mixed: ditto, the full point is checked either way
    "parameters", "objective", "constraints", "variables", "eliminated",
    "equations",        # parametric/eliminate: restating the problem smaller
    "terms", "collected", "var",   # asymptotic: the Laurent data it reports
    "base_rows",        # farkas: the pre-product rows, kept for reading
    "rows",             # unsat_core: now tied to core_smt2, checked there
}


def mutate(value):
    """A different value of the same shape, so the failure is semantic.

    Shape-preserving on purpose: a payload that rejects a STRING where a
    number belongs has refused a type error, not a forgery, and would look
    like a check that works.
    """
    if isinstance(value, bool):
        return not value
    if isinstance(value, int):
        return value + 1
    if isinstance(value, str):
        try:
            return str(Fraction(value) + 1)
        except (ValueError, ZeroDivisionError):
            return value + "_x" if value else "x"
    if isinstance(value, list) and value:
        return value[:-1]
    if isinstance(value, dict) and value:
        # A NESTED CERTIFICATE. Mutating its first key changes the schema
        # number or the kind label, which is not an interesting forgery -- the
        # claim lives in the payload, so go in and change that instead.
        # Without this, a field holding a whole sub-certificate looks
        # unchecked when it is checked thoroughly.
        if ("payload" in value and isinstance(value["payload"], dict)
                and value["payload"]):
            return dict(value, payload=mutate(value["payload"]))
        k = next(iter(value))
        return {kk: (mutate(vv) if kk == k else vv)
                for kk, vv in value.items()}
    return None


def probe(cert, limits=None, skip=(), excuse=True) -> dict:
    """Mutate each payload field in turn and report which changes were caught.

    `excuse=False` probes every field including the ones certo's own kinds
    record as descriptive -- which is what you want when the certificate is
    not one of certo's, since those judgements were made about other payloads.
    """
    from .certificate import Certificate, verify

    base = json.loads(json.dumps(cert.to_dict()
                                 if hasattr(cert, "to_dict") else cert))
    original = verify(Certificate.from_dict(base), limits)

    out = {"kind": base.get("kind"), "original_ok": bool(original.ok),
           "caught": [], "uncaught": [], "excused": [], "unshaped": []}
    if not original.ok:
        # Probing a certificate that does not verify tells you nothing: every
        # mutation would be "caught" by the failure that was already there.
        out["detail"] = original.detail
        return out

    for field, value in sorted(base.get("payload", {}).items()):
        if field in skip or (excuse and (field in DESCRIPTIVE
                                         or field in WEAKENING)):
            out["excused"].append(field)
            continue
        changed = mutate(value)
        if changed is None or changed == value:
            # Nothing of the same shape to put there -- an empty list, a None.
            # Reported rather than silently dropped, because "not probed" and
            # "probed and caught" are different facts.
            out["unshaped"].append(field)
            continue
        d = json.loads(json.dumps(base))
        d["payload"][field] = changed
        try:
            caught = not verify(Certificate.from_dict(d), limits).ok
        except Exception:  # noqa: BLE001
            # A verifier that raises on a malformed payload has still refused
            # it, which is the behaviour that matters here.
            caught = True
        (out["caught"] if caught else out["uncaught"]).append(field)
    return out
