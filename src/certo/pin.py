"""A value pinned from both sides: `cp(G) = X`, proved.

A user had `cp <= X` from a cover, `cp >= X` from an LP rounded by hand, and
a sentence joining them. Each half verified; the sentence did not, and it is
where a different graph -- or a relaxation of a different problem -- slips
in. This joins the halves the way the audit of 0.20.0 taught: both are
re-verified, and both are shown to be about THE SAME GRAPH and THE SAME
QUANTITY, from the payload, before their numbers are compared.

The quantity is the clique partition number `cp_r(G)`: the fewest cliques,
each of order at most `r` (or any order), whose edge sets partition E(G).

  UPPER   an `exact_cover` certificate with `cliques`: X parts that are
          cliques, of order <= r, partitioning exactly E(G).  cp_r <= X.

  LOWER   a `clique_lp` certificate: the LP over every clique of order
          2..>= r with each edge covered once (or at least once), counting
          cliques -- its certified optimum L bounds every partition, so
          cp_r >= ceil(L). Built from the SAME edge list, which is the tie.

          Or an `lp_dual` with `rounded` (`opt --round`) over a program of
          the user's own. certo cannot see that program is a relaxation of
          cp_r(G); the certificate then says so, names the assumption, and
          is RELATIVE to it.

When ceil(L) = X the value is pinned. Otherwise the certificate is the range
it proves, `ceil(L) <= cp_r <= X`, and says the gap.
"""
from __future__ import annotations

import math
from fractions import Fraction

from .i18n import t


class NotAPin(ValueError):
    """The two halves cannot be read as bounds on one quantity."""


def _edges(pairs) -> list:
    """Edges as sorted pairs of labels, so `[0, 1]` and `["1", "0"]` agree."""
    out = sorted({tuple(sorted((str(u), str(v)))) for u, v in pairs})
    if any(u == v for u, v in out):
        raise NotAPin(t("pin.loop"))
    return out


def upper_bound(cert, max_size):
    """`(X, edges)` from an exact cover by cliques of order <= max_size."""
    p = cert["payload"]
    if cert.get("kind") != "exact_cover" or not p.get("cliques") \
            or p.get("exact") is False:
        raise NotAPin(t("pin.upper_kind", kind=cert.get("kind")))
    own = p.get("max_size")
    if max_size is not None and (own is None or int(own) > int(max_size)):
        raise NotAPin(t("pin.upper_order", own=own, want=max_size))
    if p.get("multiplicities"):
        raise NotAPin(t("pin.upper_multiplicities"))
    return len(p["parts"]), _edges(p["universe"])


def lower_bound(cert, max_size):
    """`(ceil(L), edges or None, assumed)` from the lower half."""
    p = cert["payload"]
    if cert.get("kind") == "clique_lp":
        w = p.get("weight") or {}
        ok = (p.get("problem") in ("partition", "cover")
              and Fraction(w.get("edges", 0)) == 0
              and Fraction(w.get("vertices", 0)) == 0
              and Fraction(w.get("constant", 0)) == 1
              and all(Fraction(r) == 1 for r in p.get("rhs") or [])
              and int(p.get("min_size", 2)) <= 2
              and "farkas" not in p)
        if not ok:
            raise NotAPin(t("pin.lower_shape"))
        # Fewer columns make the LP LARGER, so its bound would not hold for
        # pieces it left out: the LP must allow every order the quantity does.
        own = p.get("max_size")
        if own is not None and (max_size is None or int(own) < int(max_size)):
            raise NotAPin(t("pin.lower_order", own=own, want=max_size))
        L = Fraction(p["objective"])
        return math.ceil(L), _edges(p["edges"]), None
    if cert.get("kind") == "lp_dual":
        r = p.get("rounded")
        if r is None or p.get("sense") != "min":
            raise NotAPin(t("pin.lower_lp"))
        return int(Fraction(r["bound"])), None, True
    raise NotAPin(t("pin.lower_kind", kind=cert.get("kind")))


def check(payload, limits=None) -> list:
    """`(label, ok, detail)` for every claim of a `pinned_value` payload."""
    from .certificate import Certificate, verify

    out = []
    r = payload.get("max_size")
    graph = _edges(payload["edges"])
    up, lo = payload["upper"], payload["lower"]
    rep_u = verify(Certificate.from_dict(up), limits)
    rep_l = verify(Certificate.from_dict(lo), limits)
    out.append(("upper", rep_u.ok, rep_u.detail))
    out.append(("lower", rep_l.ok, rep_l.detail))
    X, e_up = upper_bound(up, r)
    L, e_lo, assumed = lower_bound(lo, r)
    out.append(("same_graph", e_up == graph and (e_lo is None or e_lo == graph)
                and payload.get("quantity") == "clique_partition",
                str(len(graph))))
    # An assumption is stated exactly when one is needed: for a clique LP
    # there is none, and a stated one would read the result as relative.
    stated = bool(str(payload.get("assumption") or "").strip())
    out.append(("assumption", stated == bool(assumed),
                payload.get("assumption") or "-"))
    b = payload["bounds"]
    out.append(("bounds", int(b["lower"]) == L and int(b["upper"]) == X and L <= X,
                "{} <= cp <= {}".format(L, X)))
    out.append(("pinned", bool(payload.get("pinned")) == (L == X), str(L == X)))
    return out
