"""Does this certificate prove MY claim? One answer, from its parts.

`verify` says whether a certificate is valid on its own terms. Whether it
proves what a consumer needs takes four more questions, and session after
session each consumer answered them by hand -- and got one wrong:

  - is it about MY obligation?          (`same_obligation`)
  - is it the KIND of evidence I need?  a valid counterexample is not a
                                        proof, an LP optimum is not `proved`
  - was it re-derived COMPLETELY?       no solver, nothing assumed
  - what is its SCOPE?                  a box, a finite case, a relaxation

`view(...)` puts them in one dict, with `proves_claim`:

    True    valid, about the obligation given, of an expected class, and
            complete when that was asked
    False   one of those fails -- `reasons` says which
    None    valid, but no obligation was given (or its kind cannot be
            compared): valid on its own terms only, which is not "yes"
"""
from __future__ import annotations

from .i18n import t


def view(cert, report, valid, same=None, expect=None, complete=False) -> dict:
    """`valid`: the report's verdict BEFORE the obligation was added to it;
    `same`: `same_obligation`'s answer, or None when none was given."""
    from .evidence import evidence_class
    from .scope import scope_of

    ev = evidence_class(cert)
    reasons = []
    if not valid:
        reasons.append(t("claim.unfinished") if getattr(report, "timed_out", False)
                       else t("claim.invalid"))
    if same is None:
        ob = "not_given"
    elif same.get("same") is None:
        ob = "not_covered"
    elif same["same"]:
        ob = "same"
    else:
        ob = "differs"
        reasons.append(t("claim.differs", why="; ".join(same.get("differences") or [])[:300]))
    wanted = list(expect or [])
    if wanted and ev not in wanted:
        reasons.append(t("claim.evidence", got=ev, want=", ".join(wanted),
                         text=t("evidence." + ev)))
    degree = getattr(report, "degree", None)
    if complete and degree != "complete":
        reasons.append(t("claim.not_complete", degree=degree,
                         solver=t("claim.solver") if not cert.solver_free else ""))
    if reasons:
        proves = False
    elif ob in ("not_given", "not_covered"):
        proves = None
    else:
        proves = True
    return {"proves_claim": proves, "valid": bool(valid),
            "timed_out": bool(getattr(report, "timed_out", False)),
            "obligation": ob, "evidence": ev, "expected": wanted or None,
            "degree": degree, "solver_free": bool(cert.solver_free),
            "scope": scope_of(cert), "reasons": reasons}


def line(v) -> str:
    """The one line `verify` prints."""
    if v["proves_claim"] is True:
        return t("claim.yes", evidence=v["evidence"], degree=v["degree"])
    if v["proves_claim"] is None:
        return t("claim.unasked" if v["obligation"] == "not_given" else "claim.uncomparable",
                 evidence=v["evidence"])
    return t("claim.no", reasons="; ".join(v["reasons"]))


def check_expect(expect) -> list:
    """`--expect a,b` as a list of evidence classes; an unknown one raises."""
    from .evidence import CLASSES

    if not expect:
        return []
    if isinstance(expect, str):
        expect = [x for x in expect.split(",")]
    out = [x.strip() for x in expect if x and x.strip()]
    bad = [x for x in out if x not in CLASSES]
    if bad:
        raise ValueError(t("claim.unknown_class", names=", ".join(bad),
                           known=", ".join(CLASSES)))
    return out
