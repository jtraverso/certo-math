"""What a result is ABOUT, beside the result.

A success line read alone overstates: "PROVED" for a bound that holds on a box,
an optimum over a restricted family of columns, a cover that is not shown
minimum, a proof that rests on two bridges. All of that was already in the
certificate -- `region`, `max_size`, `partial`, `assumed`, the warnings -- and
not where the success is read. `scope_of` reads it back out as a few short
phrases, the CLI prints them under the verdict and the JSON and MCP carry them
as `scope`, so the restriction travels with the claim it restricts.

Only what the payload says is reported, never guessed: a kind this does not
know gets no scope line, which means "not summarised here", not "unrestricted".
"""
from __future__ import annotations

from .i18n import t


def _box(box) -> str:
    out = []
    for name, ends in (box or {}).items():
        lo, hi = (list(ends) + [None, None])[:2]
        out.append("{} in [{}, +inf)".format(name, lo) if hi is None
                   else "{} in [{}, {}]".format(name, lo, hi))
    return ", ".join(out)


def _floors(params) -> str:
    if isinstance(params, dict):
        return ", ".join("{} >= {}".format(k, v) for k, v in params.items())
    return ", ".join(map(str, params or []))


def _parametric(p):
    out = [t("scope.box", box=_box(p["box"])) if p.get("box")
           else t("scope.floors", floors=_floors(p.get("parameters")))]
    if p.get("region"):
        out.append(t("scope.region", names=", ".join(sorted(p["region"]))))
    return out


def _nonneg(p):
    out = [t("scope.box", box=_box(p.get("box")))]
    if p.get("region"):
        out.append(t("scope.region", names=", ".join(sorted(p["region"]))))
    return out


def _atlas(p):
    out = []
    if p.get("region"):
        out.append(t("scope.region", names=", ".join(sorted(p["region"]))))
    if p.get("cited"):
        out.append(t("scope.cited_boxes", n=len(p["cited"])))
    return out


def _cliques(p):
    lo, hi = p.get("min_size"), p.get("max_size")
    if hi is not None:
        return [t("scope.clique_family", lo=lo or 1, hi=hi)]
    return [t("scope.clique_all", lo=lo or 1)]


def _lp(p):
    if p.get("integer") and not p.get("rounded"):
        return [t("scope.relaxation")]
    return []


def _sweep(p):
    n = p.get("n")
    filters = p.get("filters") or []
    return [t("scope.finite_graphs", n=n,
              filters="; ".join(map(str, filters)) or "-")]


def _domain(p):
    return [t("scope.finite_items", n=len(p.get("ids") or []))]


def _range(p):
    sizes = [e.get("n") for e in p.get("entries") or [] if e.get("n") is not None]
    if not sizes:
        return []
    return [t("scope.finite_sizes", lo=min(sizes), hi=max(sizes),
              stopped=t("scope.stopped") if p.get("stopped_early") else "")]


def _cover(p):
    out = [t("scope.cover_not_minimum")]
    if p.get("repair"):
        steps = p["repair"] if isinstance(p["repair"], list) else [p["repair"]]
        out.append(t("scope.cover_repair",
                     n=sum(len(s.get("withdraw") or []) for s in steps)))
    return out


def _proof(p):
    out = []
    lemmas = p.get("lemmas") or []
    cited = [l["name"] for l in lemmas if l.get("cited")]
    bridges = [n for n in (p.get("bridges") or []) if n not in cited]
    if bridges:
        out.append(t("scope.bridges", n=len(bridges), names=", ".join(bridges[:4])))
    if cited:
        out.append(t("scope.cited", n=len(cited), names=", ".join(cited[:4])))
    return out


def _bisect(p):
    return [t("scope.monotone")]


SCOPES = {
    "parametric_bound": _parametric, "polynomial_nonneg": _nonneg,
    "parametric_atlas": _atlas, "clique_lp": _cliques,
    "clique_lp_farkas": _cliques, "lp_dual": _lp, "sweep": _sweep,
    "domain_sweep": _domain, "sweep_range": _range, "exact_cover": _cover,
    "proof": _proof, "bisect": _bisect,
}


def scope_of(cert) -> list:
    """Short phrases saying what the certificate's claim is restricted to;
    `[]` for a kind not summarised here. Never raises: a scope line that
    cannot be read is omitted, not guessed."""
    if cert is None:
        return []
    d = cert.to_dict() if hasattr(cert, "to_dict") else cert
    fn = SCOPES.get(d.get("kind"))
    if fn is None:
        return []
    try:
        return [s for s in fn(d.get("payload") or {}) if s]
    except (KeyError, TypeError, ValueError, AttributeError):
        return []
