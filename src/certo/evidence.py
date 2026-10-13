"""What KIND of evidence a certificate is, said beside every result.

Two reports asked for the same thing in different words. One kept a
feasible bound, an LP optimum, a relaxation bound and a written universal
proof apart by hand, section after section, because a summary line read
them all as "certified". The other kept an algebraic identity, a sign on a
box, a universal step and a composition apart across forty sessions. Each
one is true and they are not interchangeable: a cover you have is an upper
bound, not the cover number; an LP optimum of a relaxation bounds the
integer optimum, it is not it.

`evidence_of(cert)` names the class from the kind and, where it decides, the
payload -- an ideal certificate of `1` is a refutation, not an identity; a
proof whose hypotheses contradict each other holds vacuously. The class is a
reading of what the certificate establishes, not a verdict about it.
"""
from __future__ import annotations

from .i18n import t

#: kind -> class, before the payload is consulted
CLASS = {
    "unsat_core": "universal", "drat": "universal",
    "propositional_refutation": "universal", "induction": "universal",
    "synth_proved": "universal", "cegis_none": "universal",
    "farkas": "inconsistency", "farkas_ray": "inconsistency",
    "mus": "inconsistency",
    "ideal": "identity", "resultant": "identity",
    "polynomial_nonneg": "sign", "sos": "sign", "parametric_atlas": "sign",
    "parametric_bound": "sign", "ratio_bound": "sign", "ball": "sign",
    "variable_range": "sign",
    "model": "counterexample", "cnf_model": "witness",
    "exact_cover": "feasible", "mixed_design": "feasible",
    "assignment": "feasible",
    "lp_dual": "lp_optimum", "clique_lp": "lp_optimum",
    "capacity_profile": "lp_optimum",
    "sat_optimum": "optimum", "recurrence_table": "optimum",
    "branch_bound": "optimum", "integer_peak": "optimum",
    "family_extremum": "optimum", "pinned_value": "optimum",
    "gap": "relaxation", "branch_frontier": "relaxation",
    "sweep": "finite", "sweep_range": "finite", "domain_sweep": "finite",
    "graph_set": "finite", "orbit_witnesses": "finite",
    "shrink_graph": "finite", "shrink_domain": "finite",
    "first_entry": "finite", "bisect": "finite",
    "cegis": "synthesis",
    "proof": "composition", "core_matrix": "composition",
    "lean_binding": "composition",
    "repair_refusal": "refusal",
    "hypothesis_audit": "audit",
}

CLASSES = ("universal", "inconsistency", "identity", "sign", "counterexample",
           "witness", "feasible", "lp_optimum", "optimum", "relaxation",
           "finite", "synthesis", "composition", "refusal", "audit",
           "computation")


def evidence_class(cert) -> str:
    """The class key -- one of `CLASSES`; `computation` where nothing more
    specific applies."""
    from .certificate import Certificate

    if isinstance(cert, dict):
        cert = Certificate.from_dict(cert)
    p = cert.payload or {}
    kind = cert.kind
    if kind == "ideal" and p.get("inconsistent"):
        return "inconsistency"
    if kind == "polynomial_nonneg" and p.get("holds") is False:
        return "counterexample"
    if kind == "unsat_core" and p.get("vacuous"):
        return "inconsistency"
    if kind == "lp_dual" and p.get("integral_objective") is not None \
            and str(p.get("integral_objective")) == str(p.get("objective")):
        # an integral point attains the dual bound: the INTEGER optimum
        return "optimum"
    return CLASS.get(kind, "computation")


def evidence_of(cert) -> dict | None:
    """`{"class", "text"}` for a certificate, or None without one."""
    if cert is None:
        return None
    key = evidence_class(cert)
    return {"class": key, "text": t("evidence." + key)}
