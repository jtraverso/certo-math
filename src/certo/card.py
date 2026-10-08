"""What a result IS: the card that travels with a certificate.

The most repeated request across this round of reports, in one sentence of
one of them: with dozens of certificates passing, it is easy to mistake
volume for progress. A PASS proves what its certificate states -- usually an
implication whose hypotheses are somebody else's problem, or a finite case --
and the run that produced it knew more than the certificate said:

  * the ROLE of the result in a larger argument: a consumer (an implication
    that uses hypotheses), an existence (an object exhibited), a refutation,
    or a finite check;
  * the LINK of the chain it belongs to ("Tuza split, step 3");
  * what it is PENDING on: the dependencies that are not established yet --
    "CP7", "the physical realisation" -- as opposed to `cite`, which names a
    published result.

A spec declares them; they are carried in the certificate as the optional
payload field `card` (so they count in its digest); and every reader -- the
`verify` card, `status`, `--oneline`, the MCP -- shows them, labelled as
DECLARED: nothing here is checked, and saying so is the point.

    s = Spec()
    ...
    s.role("consumer").link("Tuza split, step 3").pending("CP7")

or, for any spec object, `certo.card.declare(spec, role=..., link=...,
pending=[...])`. A JSON spec takes a top-level `"card": {...}`.

The card a reader sees adds what the certificate and its verification say:
the conclusion, the scope, the hypotheses used and cited, the degree, and the
provenance -- producing and verifying versions, interpreter, package path,
schema and hashes -- the same from the CLI, the API, the MCP and a pack.
"""
from __future__ import annotations

import os
import sys

from .i18n import t

ROLES = ("consumer", "existence", "refutation", "finite_check")

_ATTR = "_certo_card"

#: What each loaded spec declared, by resolved path. Written by `load_spec`,
#: read where the certificate is stamped -- the spec object itself is gone by
#: then, but its path is not.
_BY_PATH: dict = {}


def declare(spec, role=None, link=None, pending=None):
    """Declare a spec's role, link and pending dependencies; returns it."""
    card = dict(getattr(spec, _ATTR, None) or {})
    if role is not None:
        if role not in ROLES:
            raise ValueError(t("card.bad_role", role=role, known=", ".join(ROLES)))
        card["role"] = role
    if link is not None:
        card["link"] = str(link)
    if pending:
        items = [pending] if isinstance(pending, str) else list(pending)
        have = list(card.get("pending") or [])
        card["pending"] = have + [str(p) for p in items if str(p) not in have]
    try:
        object.__setattr__(spec, _ATTR, card)
    except (AttributeError, TypeError):
        pass
    return spec


def declared(spec) -> dict | None:
    card = getattr(spec, _ATTR, None)
    return dict(card) if card else None


# --- the methods every spec class gets --------------------------------------


def _role(self, role):
    return declare(self, role=role)


def _link(self, link):
    return declare(self, link=link)


def _pending(self, *items):
    return declare(self, pending=list(items))


def install(*classes):
    """`spec.role(...)`, `spec.link(...)`, `spec.pending(...)` on each class
    that does not already use those names."""
    for cls in classes:
        for name, fn in (("role", _role), ("link", _link), ("pending", _pending)):
            if name not in cls.__dict__ and not any(
                    name in getattr(b, "__dataclass_fields__", {}) for b in cls.__mro__):
                setattr(cls, name, fn)


# --- from the spec to the certificate ---------------------------------------


def _key(path):
    """The path as `load_spec` resolves it: on Windows that expands a short
    name (`JTRAVE~1`), which `abspath` does not."""
    from pathlib import Path

    try:
        return str(Path(str(path)).resolve())
    except Exception:  # noqa: BLE001
        return None


def remember(path, spec):
    """Called by `load_spec`."""
    key = _key(path)
    if key is None:
        return
    card = declared(spec)
    if card:
        _BY_PATH[key] = card
    else:
        _BY_PATH.pop(key, None)


def attach(cert, spec_path=None, spec=None):
    """Put the declared card in the certificate's payload, once."""
    if cert is None or "card" in (cert.payload or {}):
        return cert
    card = declared(spec) if spec is not None else None
    if card is None and spec_path:
        card = _BY_PATH.get(_key(spec_path))
    if card:
        cert.payload["card"] = dict(card)
    return cert


# --- what a reader sees ------------------------------------------------------


def card_of(cert, report=None) -> dict:
    """The full card: declared, derived and verified, as data."""
    from . import __version__
    from .certificate import SCHEMA_VERSION, Certificate
    from .scope import scope_of

    if isinstance(cert, dict):
        cert = Certificate.from_dict(cert)
    p = cert.payload or {}
    decl = dict(p.get("card") or {})
    prov = cert.provenance or {}
    cited = dict(p.get("citations") or {})
    used = [n for n in (p.get("names") or []) if n != "__goal__"]
    out = {
        "kind": cert.kind,
        "conclusion": (report.detail if report is not None else cert.note) or "",
        "scope": scope_of(cert),
        "hypotheses_used": used,
        "cited": cited,
        "pending": list(decl.get("pending") or []),
        "role": decl.get("role"),
        "link": decl.get("link"),
        "declared": bool(decl),
        "degree": report.degree if report is not None else None,
        "provenance": {
            "digest": cert.digest(),
            "schema": cert.schema,
            "schema_known": SCHEMA_VERSION,
            "produced_by": prov.get("certo_version"),
            "verified_by": __version__,
            "spec_path": prov.get("spec_path"),
            "spec_sha256": prov.get("spec_sha256"),
            "python": sys.version.split()[0],
            "interpreter": sys.executable,
            "package": os.path.dirname(os.path.abspath(__file__)),
        },
    }
    out["external"] = ([{"sort": "cited", "name": n, "source": s}
                        for n, s in sorted(cited.items())]
                       + [{"sort": "pending", "name": n} for n in out["pending"]])
    return out


def lines(card) -> list:
    """The card as text, a few lines, for `verify`."""
    out = [t("card.header", kind=card["kind"], degree=card["degree"] or "-")]
    if card["role"] or card["link"]:
        out.append(t("card.role", role=card["role"] or "-",
                     link=card["link"] or "-"))
    if card["scope"]:
        out.append(t("card.scope", scope="; ".join(card["scope"])))
    if card["hypotheses_used"]:
        out.append(t("card.hypotheses", n=len(card["hypotheses_used"]),
                     cited=len(card["cited"])))
    if card["pending"]:
        out.append(t("card.pending", names="; ".join(card["pending"])))
    pv = card["provenance"]
    out.append(t("card.provenance", produced=pv["produced_by"] or "?",
                 verified=pv["verified_by"], digest=pv["digest"],
                 schema=pv["schema"]))
    if card["declared"]:
        out.append(t("card.declared"))
    return out
