"""An LP answer, typed: optimum, feasible point, bound or infeasibility.

Four certificates of `opt` look alike in a JSON dump and are not alike: an
exact optimum (primal AND dual), a feasible point of a zero objective (a
primal, nothing optimised), a relaxation bound of an integer program, and a
Farkas ray (no primal at all). Consumers read `dual` from a ray, expected a
`primal` from an infeasibility certificate, and asked `proved` of an optimum
-- each a reported integration error, each the same missing distinction.

`lp_view(result_or_certificate)` names which one it is and hands back only
the fields that one has, as Fractions keyed by name:

    kind        "optimum" | "feasible" | "bound" | "float_candidate"
                | "infeasible" | None (no LP certificate)
    objective   the optimum in the DECLARED sense (None for a ray)
    primal      {variable: value}            (None for a ray)
    dual        {row: multiplier}            (None for a ray, a point)
    ray         {row: multiplier}            (only for "infeasible")

Nothing here checks anything: `verify` does. This only reads.
"""
from __future__ import annotations

from collections import namedtuple

#: `LPSpec.as_leq_system()`: max c.x, A x <= b, x >= 0 -- and the fourth
#: field names the ROWS (constraints), not the variables, which is how a
#: user's auditor got it backwards. Still a tuple: `A, b, c, names = ...`.
LeqSystem = namedtuple("LeqSystem", ["A", "b", "c", "row_names"])


def lp_view(obj) -> dict:
    from .certificate import Certificate, lp_claim_scope
    from .exact import to_fraction

    cert = getattr(obj, "certificate", obj)
    if isinstance(cert, dict):
        cert = Certificate.from_dict(cert)
    empty = {"kind": None, "objective": None, "primal": None, "dual": None,
             "ray": None}
    if cert is None or not hasattr(cert, "kind"):
        return empty
    p = cert.payload or {}
    if cert.kind == "farkas_ray":
        names = list(p.get("names") or [])
        y = [to_fraction(v) for v in p.get("y") or []]
        return dict(empty, kind="infeasible",
                    ray={names[i] if i < len(names) else "row{}".format(i): v
                         for i, v in enumerate(y)})
    if cert.kind != "lp_dual":
        return empty
    kind = p.get("claim_scope") or lp_claim_scope(p)
    var_names = list(p.get("var_names") or [])
    rows = list(p.get("names") or [])
    primal = {v: to_fraction(x) for v, x in zip(var_names, p.get("primal") or [])}
    dual = {r: to_fraction(y) for r, y in zip(rows, p.get("dual") or [])}
    declared = (p.get("declared") or {}).get("objective")
    if declared is None and p.get("objective") is not None:
        declared = p["objective"]
        if p.get("sense") == "min":
            declared = -to_fraction(declared)
    return dict(empty, kind=kind,
                objective=None if declared is None else to_fraction(declared),
                primal=primal or None,
                dual=None if kind == "feasible" else (dual or None))
