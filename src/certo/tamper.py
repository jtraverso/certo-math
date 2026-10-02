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
    # `columns`: how many rounds and columns the generation took. The claims
    # are the support, the dual and the pricing search; these say how long.
    "rounds", "generated",
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
    # parametric: dropping a variable from `free` claims the bound for the
    # program where it is >= 0 -- a restriction, so a weaker statement, and a
    # balanced column is non-negative anyway.
    "free",
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


# ---------------------------------------------------------------------------
# STRUCTURAL forgeries: the shapes one field at a time cannot reach
# ---------------------------------------------------------------------------
#
# An external audit of 0.20.0 found ten certificates `verify` accepted, and
# `probe` above could have found none of them. Each was COHERENT: an empty
# list the verifier walked over without complaint, a negative index, a valid
# sub-certificate about something else, two fields edited together so that
# they still agreed with each other. Mutating one field of an honest
# certificate produces none of those. These do:
#
#   empty     a list or dict emptied            (CM-02: `mus_indices: []`)
#   short     a list missing its last entry
#   dup       a list with its first entry twice
#   reversed  a list in the opposite order
#   negative  an integer in a list of integers set to -1        (CM-07)
#   beyond    ... or to one past the largest index it could be
#   dropkey   a dict missing its first key
#   swap      two sub-certificates of one kind exchanged         (CM-09)
#   coherent  one value rewritten EVERYWHERE it occurs in the payload, so
#             every field that repeats it still agrees            (CM-04/05)
#
# Not every surviving forgery is a hole -- reversing a list of names that is
# only displayed changes nothing -- so, like `probe`, this REPORTS. certo's own
# suite holds each kind to it, with every survivor that is benign excused by
# name and with a reason.

#: How many forgeries one certificate is put through, at most. A payload with
#: thousands of list entries would otherwise make thousands of certificates.
MAX_FORGERIES = 240


def _walk(node, path=()):
    """Every (path, value) under `node`, depth first, containers included."""
    yield path, node
    if isinstance(node, dict):
        for k in sorted(node, key=str):
            yield from _walk(node[k], path + (k,))
    elif isinstance(node, list):
        for i, v in enumerate(node):
            yield from _walk(v, path + (i,))


def _set(root, path, value):
    out = json.loads(json.dumps(root))
    node = out
    for k in path[:-1]:
        node = node[k]
    node[path[-1]] = value
    return out


def _label(path, op) -> str:
    return "{}:{}".format(".".join(str(p) for p in path), op)


def _is_cert(v) -> bool:
    return isinstance(v, dict) and "kind" in v and isinstance(v.get("payload"), dict)


def _number(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return Fraction(v)
    if isinstance(v, str):
        try:
            return Fraction(v)
        except (ValueError, ZeroDivisionError):
            return None
    return None


def forgeries(payload, limit=MAX_FORGERIES):
    """`(label, forged payload)` for every structural forgery of `payload`.
    Labels are `path:op`, with the path through the payload's keys and list
    positions; positions inside lists are generalised to `*` for excusing."""
    seen = set()
    out = []

    def add(path, op, value):
        lab = _label(path, op)
        if lab in seen or len(out) >= limit:
            return
        seen.add(lab)
        out.append((lab, _set(payload, path, value)))

    certs = {}
    for path, v in _walk(payload):
        if not path:
            continue
        if _is_cert(v):
            certs.setdefault(v["kind"], []).append((path, v))
        if isinstance(v, list) and v:
            add(path, "empty", [])
            add(path, "short", v[:-1])
            add(path, "dup", v + [v[0]])
            if len(v) > 1 and v[::-1] != v:
                add(path, "reversed", v[::-1])
            ints = [x for x in v if isinstance(x, int) and not isinstance(x, bool)]
            if ints and len(ints) == len(v):
                add(path, "negative", [-1] + v[1:])
                add(path, "beyond", [max(max(ints), len(v)) + 1] + v[1:])
        elif isinstance(v, dict) and v and not _is_cert(v):
            add(path, "empty", {})
            first = sorted(v, key=str)[0]
            add(path, "dropkey", {k: x for k, x in v.items() if k != first})

    for kind, found in certs.items():
        for (p1, c1), (p2, c2) in zip(found, found[1:]):
            if c1 != c2:
                out_payload = _set(_set(payload, p1, c2), p2, c1)
                lab = "{}<->{}:swap".format(".".join(map(str, p1)),
                                            ".".join(map(str, p2)))
                if lab not in seen and len(out) < limit:
                    seen.add(lab)
                    out.append((lab, out_payload))

    # COHERENT: a number that appears in two or more places, changed in all
    # of them at once. Compared as numbers, so "1" and 1 are the same value.
    places = {}
    for path, v in _walk(payload):
        n = _number(v)
        if n is not None and path:
            places.setdefault(n, []).append((path, v))
    for n, where in sorted(places.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        if len(where) < 2 or len(out) >= limit:
            continue
        forged = json.loads(json.dumps(payload))
        for path, v in where:
            new = n + 1
            if isinstance(v, int):
                new = int(new) if new.denominator == 1 else v + 1
            else:
                new = str(new)
            forged = _set(forged, path, new)
        out.append(("={}:coherent".format(n), forged))
    return out


def _general(label) -> str:
    """A label with list positions replaced by `*`, for excusing a family."""
    head, _, op = label.rpartition(":")
    parts = ["*" if p.isdigit() else p for p in head.split(".")]
    return "{}:{}".format(".".join(parts), op)


def probe_structural(cert, limits=None, excuse=(), limit=MAX_FORGERIES) -> dict:
    """Put a certificate through every structural forgery. `excuse` names
    forgeries -- by label, or by its general form with `*` for positions --
    that are benign and may pass. Returns `{original_ok, caught, survived,
    excused}`, lists of labels."""
    from .certificate import Certificate, verify

    base = json.loads(json.dumps(cert.to_dict()
                                 if hasattr(cert, "to_dict") else cert))
    original = verify(Certificate.from_dict(base), limits)
    out = {"kind": base.get("kind"), "original_ok": bool(original.ok),
           "caught": [], "survived": [], "excused": []}
    if not original.ok:
        return out
    excuse = set(excuse)
    for label, forged in forgeries(base.get("payload") or {}, limit):
        if label in excuse or _general(label) in excuse:
            out["excused"].append(label)
            continue
        d = dict(base, payload=forged)
        try:
            caught = not verify(Certificate.from_dict(d), limits).ok
        except Exception:  # noqa: BLE001 -- a refusal by raising is a refusal
            caught = True
        (out["caught"] if caught else out["survived"]).append(label)
    return out
