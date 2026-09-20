"""What a certificate assumed, against what the Lean lemma actually gives.

The ledger knows which specs ran. Nothing connected a certificate to the
declaration that is supposed to justify it, and the gap is expensive in a
specific way: a user certified `delta <= eps_C**3 * d**12 / 100` ASSUMING the
fine counting bound, and found on writing the Lean that the packaged
`patCount_K4_le` uses density `<= 1` and gives a bound that is useless. Nothing
warned them. They saw it because they went and read the statement, three
modules later.

WHAT THIS CHECKS. You name the certificate, the declaration, the hypothesis it
is meant to discharge, and what the declaration actually PROVIDES. certo finds
the hypothesis in the spec the certificate came from -- the path and hash
travel in every certificate -- and asks whether what you say the lemma gives
is strong enough for it:

    provides  =>  hypothesis

If it is not, the binding is REFUTED and says so at bind time, which is the
whole point: at bind time you are looking at the statement, and three modules
later you are not.

IT IS STILL A BRIDGE, and labelled one. Nobody here reads Mathlib: that
`provides` is a faithful rendering of the declaration is your claim, exactly
as a `compose` bridge is. What moves is WHEN it bites and whether `status` can
count it.

A SPEC THAT HAS MOVED is reported rather than guessed at. The certificate
carries the hash of the file it was made from; if that file changed, the
hypothesis read out of it today may not be the one that was certified, and a
binding checked against the wrong statement would be worse than none.
"""
from __future__ import annotations

import hashlib
import json
import pathlib

from .i18n import t as _t


class NotBindable(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


def _digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _provenance(cert: dict) -> dict:
    """Where the certificate says it came from: `spec_path` and `spec_sha256`."""
    prov = cert.get("provenance") or {}
    if not prov.get("spec_path"):
        return {}
    return {"path": prov["spec_path"], "sha256": prov.get("spec_sha256")}


def hypothesis_of(spec, name):
    """The named hypothesis, as the formula the spec actually declared."""
    for hname, formula in spec.assumptions:
        if hname == name:
            return formula
    raise NotBindable(_t("bind.no_hypothesis", name=name,
                         known=", ".join(n for n, _f in spec.assumptions)[:80]
                         or "-"))


def certify(spec, limits=None, root=".") -> dict:
    """Read the certificate, find the hypothesis, and check the entailment."""
    from .certificate import entails
    from .spec import load_spec

    cert_path = pathlib.Path(root) / str(getattr(spec, "certificate", ""))
    if not cert_path.exists():
        raise NotBindable(_t("bind.no_certificate", path=str(cert_path)))
    cert = json.loads(cert_path.read_text(encoding="utf-8"))

    prov = _provenance(cert)
    spec_path = prov.get("path")
    if not spec_path:
        raise NotBindable(_t("bind.no_provenance", path=str(cert_path)))

    source = pathlib.Path(spec_path)
    if not source.exists():
        source = pathlib.Path(root) / spec_path
    if not source.exists():
        raise NotBindable(_t("bind.spec_gone", path=spec_path))

    stale = bool(prov.get("sha256")) and _digest(source) != prov["sha256"]

    origin = load_spec(str(source))
    name = str(getattr(spec, "discharges", "") or "")
    needed = hypothesis_of(origin, name)

    provided = getattr(spec, "provides", None)
    if provided is None:
        raise NotBindable(_t("bind.no_provides"))

    covers = entails(provided, [needed], limits)

    return {
        "certificate": str(getattr(spec, "certificate", "")),
        "certificate_kind": cert.get("kind"),
        # THE CERTIFICATE ITSELF, not a path to it. A binding says "this is
        # what THAT certificate assumed", and the path was the only thing
        # tying the two -- so a binding naming a file that does not exist, of
        # a kind it never was, verified exactly like an honest one. Embedded,
        # the link is re-checkable without a disk: the source has to verify on
        # its own terms and its provenance has to be the one recorded below.
        #
        # Optional, which the frozen schema allows: a binding written before
        # this verifies as it always did, with one check fewer.
        "source": cert,
        "declaration": str(getattr(spec, "declaration", "") or ""),
        "discharges": name,
        "needed_smt2": _smt2(needed),
        "provides_smt2": _smt2(provided),
        "covers": bool(covers),
        "spec": {"path": str(source), "stale": stale,
                 "sha256_now": _digest(source),
                 "sha256_then": prov.get("sha256")},
        "title": getattr(spec, "title", ""),
    }


def _smt2(formula) -> str:
    import z3

    s = z3.Solver()
    s.add(formula)
    return s.to_smt2()


def check(payload, limits=None) -> dict:
    """Redo the entailment from the formulas the payload carries.

    The statements are re-parsed rather than believed, so a payload edited to
    say `covers` when it does not is caught the same way a forged dual is.
    """
    import z3

    from .certificate import entails

    needed = z3.And(*z3.parse_smt2_string(payload["needed_smt2"]))
    provided = z3.And(*z3.parse_smt2_string(payload["provides_smt2"]))
    got = entails(provided, [needed], limits)
    return {"covers": bool(got), "agrees": bool(got) == bool(payload["covers"])}
