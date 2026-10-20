"""What a result IS, in one word a program can read.

`unsat` closes a theorem in `prove`, a finite case in `sweep`, the absence of
a candidate in `synth` and infeasibility in `opt`; `proved` is said by a
covering, a construction and an optimum. The messages already told these
apart -- in prose. A consumer that reused `unsat` as "success" across
commands was reading a theorem and a covering as the same thing.

`outcome(res)` names the state from the result's verdict, command,
certificate and typed metadata -- nothing is parsed from text -- as
`{"state", "conclusive", "basis"}`:

    THEOREM_PROVED            the claim holds under the hypotheses
    UNIVERSAL_WITH_IMPORTED_THEOREM  ... resting on cited lemmas or bridges
    COUNTEREXAMPLE            a point where the hypotheses hold and the claim fails
    HYPOTHESES_VERIFIED       a model of the hypotheses: the regime is inhabited
    PARAMETER_SYNTHESIZED     a candidate that works on the bounded domain
    PARAMETER_OPTIMUM         ... and nothing better within the template
    SYNTHESIS_PROVED_UNIVERSAL  the candidate, proved for the general statement
    NO_PARAMETER              no candidate in the template on the domain
    FINITE_DOMAIN_COVERED     every case of a finite domain checked
    CONTINUOUS_OPTIMUM        an exact LP optimum
    INTEGER_OPTIMUM           an integer optimum, certified
    BOUND_ONLY                a certified bound, the optimum not closed
    FEASIBLE_POINT            a point meeting every constraint; nothing optimised
    INFEASIBLE                the constraints cannot hold together
    TARGET_MET                a required count reached (assign, cover, exists)
    PHYSICAL_WITNESS_VERIFIED a physical object rebuilt and checked (no
                              resource or edge used twice)
    CONSTRUCTION_VERIFIED     every contract of a construction re-derived
    ALGEBRAIC_CONDITION_DERIVED  a resultant: necessary for a common root
    REFUTED                   the claim is false, with its witness
    SATISFIABLE               an object exists, and is exhibited
    INCONCLUSIVE              no answer -- of any kind
"""
from __future__ import annotations

STATES = (
    "THEOREM_PROVED", "UNIVERSAL_WITH_IMPORTED_THEOREM", "COUNTEREXAMPLE",
    "HYPOTHESES_VERIFIED", "PARAMETER_SYNTHESIZED", "PARAMETER_OPTIMUM",
    "SYNTHESIS_PROVED_UNIVERSAL", "NO_PARAMETER", "FINITE_DOMAIN_COVERED",
    "CONTINUOUS_OPTIMUM", "INTEGER_OPTIMUM", "BOUND_ONLY", "FEASIBLE_POINT",
    "INFEASIBLE", "TARGET_MET", "PHYSICAL_WITNESS_VERIFIED",
    "CONSTRUCTION_VERIFIED", "ALGEBRAIC_CONDITION_DERIVED", "REFUTED",
    "SATISFIABLE", "INCONCLUSIVE",
)


def _state(res):
    v = getattr(res.verdict, "value", str(res.verdict))
    cmd = res.command
    cert = res.certificate
    kind = getattr(cert, "kind", None)
    meta = res.meta or {}
    if v == "inconclusive":
        return "INCONCLUSIVE", "no answer: " + str(getattr(res.status, "value", res.status))
    if kind == "construction":
        return "CONSTRUCTION_VERIFIED", "every contract re-derived from the data"
    if cmd == "synth":
        if kind == "synth_proved":
            return "SYNTHESIS_PROVED_UNIVERSAL", "found bounded, proved general"
        if kind == "synth_optimum":
            return "PARAMETER_OPTIMUM", "optimal within the template and domain"
        if kind == "cegis":
            return "PARAMETER_SYNTHESIZED", "works on the bounded domain only"
        if kind == "cegis_none" or v == "unsatisfiable":
            return "NO_PARAMETER", "no candidate in the template on the domain"
    if cmd in ("opt", "mixed", "farkas") or kind in ("lp_dual", "farkas_ray"):
        scope = meta.get("scope")
        if v == "unsatisfiable" or scope == "infeasible":
            return "INFEASIBLE", "a Farkas ray"
        if scope == "feasible":
            return "FEASIBLE_POINT", "objective zero: nothing optimised"
        if scope == "bound":
            return "BOUND_ONLY", "the relaxation bounds the integer optimum"
        if scope == "optimum":
            if meta.get("integer_solution"):
                return "INTEGER_OPTIMUM", "an integral point meeting the certified bound"
            return "CONTINUOUS_OPTIMUM", "primal and dual, exact"
        if cmd == "mixed" and meta.get("optimality_certified"):
            return "INTEGER_OPTIMUM", "branch and bound closed"
    if cmd == "eliminate" or kind == "resultant":
        # a resultant is DERIVED: a necessary condition on the remaining
        # variables, not a theorem and not a point
        return "ALGEBRAIC_CONDITION_DERIVED", "a resultant: necessary for a common root"
    if cmd in ("sweep", "cases") and v == "proved":
        return "FINITE_DOMAIN_COVERED", "every case of the finite domain checked"
    if cmd == "check" and v == "satisfiable":
        return "HYPOTHESES_VERIFIED", "a model of the hypotheses: the regime is inhabited"
    if cmd == "assign" and v == "proved":
        if meta.get("physical"):
            return "PHYSICAL_WITNESS_VERIFIED", "no resource twice on a receiver; the target met"
        return "TARGET_MET", "the required number placed"
    if cmd in ("cover", "exists") and v == "proved" and meta.get("target") is not None:
        return "TARGET_MET", "the required count reached"
    if cmd == "compose" and v == "proved":
        if meta.get("cited") or meta.get("bridges"):
            return "UNIVERSAL_WITH_IMPORTED_THEOREM", "rests on cited lemmas or bridges"
        return "THEOREM_PROVED", "every lemma linked"
    if v == "proved":
        return "THEOREM_PROVED", "the claim holds under the hypotheses"
    if v == "refuted":
        if kind == "model":
            return "COUNTEREXAMPLE", "hypotheses hold, the claim fails, at this point"
        return "REFUTED", "the claim is false, with its witness"
    if v == "unsatisfiable":
        return "INFEASIBLE", "no object satisfies the constraints"
    return "SATISFIABLE", "an object exists, and is exhibited"


def outcome(res) -> dict:
    state, basis = _state(res)
    return {"state": state, "conclusive": state != "INCONCLUSIVE", "basis": basis}
