"""A parameter domain covered by boxes, and ONE statement from N certificates.

A parametric bound is proved box by box -- a user ran two thousand of them,
in three coordinate charts, and audited the covering with scripts of their
own: exact tiling, gaps, boundaries. Every box was certified; the sentence
"so the bound holds on the whole domain" was not, and it is where a missing
sliver hides.

    AtlasSpec(domain={"p": (0, 1), "q": (0, 1)},
              region=[("below", p - q)],          # the set is the box AND g >= 0
              claim=T,                             # the one statement
              pieces=["box1.json", "box2.json", ...])

What is checked, and nothing here is believed:

  1. every piece verifies, as the certificate it is;
  2. every piece is about THE SAME program -- objective, constraints, sense,
     free variables -- and claims the SAME bound in the same direction;
  3. a piece's own region, if it has one, is among the domain's conditions,
     so the piece holds wherever the domain does;
  4. the pieces COVER the domain: split it at the pieces' edges until every
     cell lies inside one piece, or lies outside the region -- shown by a
     condition whose Bernstein coefficients are all negative there. A cell
     that is neither is named, with its coordinates. That is the sliver.

Closed boxes, exactly: a cell inside a closed piece is covered point by
point, and a condition negative on a closed cell excludes every point of it.

`cited` boxes are covered by an external result instead of a certificate,
with its source. The statement then holds RELATIVE to them, and every
verification says so -- the same standing as a cited lemma in `compose`.

NOT here, and said: charts. A domain covered in several coordinate systems
needs the change of coordinates to be part of what is checked, and that is
the next step, not this one.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from .i18n import t

#: Cells the covering may open before it gives up. Exceeding it is reported,
#: never rounded to "covered".
MAX_CELLS = 2_000_000
#: How many times a cell outside every piece may be halved to show a region
#: condition negative on it.
EXCLUDE_DEPTH = 8


class NotAnAtlas(ValueError):
    """The input is not an atlas this can read; the reason is the message."""


class CoverBudget(Exception):
    """The covering ran out of cells; nothing was established."""


# --- boxes ---------------------------------------------------------------------


def _box(raw, ring):
    """`{name: (lo, hi)}` with Fractions; `hi` may be None for a ray."""
    out = {}
    for n in ring:
        if n not in raw:
            raise NotAnAtlas(t("atlas.box_missing", name=n))
        lo, hi = raw[n]
        out[n] = (Fraction(lo), None if hi is None else Fraction(hi))
    return out


def _text(box):
    return {n: [str(lo), None if hi is None else str(hi)]
            for n, (lo, hi) in box.items()}


def _overlaps(b, cell):
    """Positive-measure overlap: a shared face is not coverage."""
    for n, (lo, hi) in cell.items():
        blo, bhi = b[n]
        if not (blo < hi and (bhi is None or lo < bhi)):
            return False
    return True


def _contains(b, cell):
    for n, (lo, hi) in cell.items():
        blo, bhi = b[n]
        if lo < blo or (bhi is not None and hi > bhi):
            return False
    return True


def _cut(cell, boxes):
    """An edge of an overlapping piece strictly inside the cell, or None --
    the first in a fixed order, so the covering is the same every time."""
    for b in boxes:
        for n in cell:
            lo, hi = cell[n]
            for v in b[n]:
                if v is not None and lo < v < hi:
                    return n, v
    return None


def _split(cell, n, v):
    left, right = dict(cell), dict(cell)
    left[n] = (cell[n][0], v)
    right[n] = (v, cell[n][1])
    return left, right


def _excluded(cell, conditions, depth):
    """Is some region condition NEGATIVE on the whole closed cell? By its
    Bernstein coefficients, all < 0, halving up to `depth` times."""
    from . import bernstein

    for _name, g in conditions:
        if _negative(g, cell, depth, bernstein):
            return True
    return False


def _negative(g, cell, depth, bernstein):
    coeffs = bernstein.coefficients(g, cell)
    if coeffs and all(v < 0 for v in coeffs.values()):
        return True
    if depth <= 0 or any(v >= 0 for c, v in coeffs.items()
                         if all(x in (0, d) for x, d in
                                zip(c, bernstein.degrees_of(g)))):
        return False                    # a corner at >= 0: it is not negative
    name = max(cell, key=lambda k: (cell[k][1] - cell[k][0], k))
    left, right = bernstein.halves(cell, name)
    return (_negative(g, left, depth - 1, bernstein)
            and _negative(g, right, depth - 1, bernstein))


def cover(domain, boxes, conditions, max_cells=MAX_CELLS, keep=8):
    """Split `domain` at the pieces' edges. Returns `{cells, covered,
    excluded, uncovered: [cell, ...] (up to `keep`), gaps: n}`."""
    stats = {"cells": 0, "covered": 0, "excluded": 0, "gaps": 0,
             "uncovered": []}
    stack = [(domain, list(boxes))]
    while stack:
        cell, near = stack.pop()
        stats["cells"] += 1
        if stats["cells"] > max_cells:
            raise CoverBudget("cells")
        near = [b for b in near if _overlaps(b, cell)]
        if any(_contains(b, cell) for b in near):
            stats["covered"] += 1
            continue
        where = _cut(cell, near)
        if where is not None:
            left, right = _split(cell, *where)
            stack.append((right, near))
            stack.append((left, near))
            continue
        if conditions and _excluded(cell, conditions, EXCLUDE_DEPTH):
            stats["excluded"] += 1
            continue
        stats["gaps"] += 1
        if len(stats["uncovered"]) < keep:
            stats["uncovered"].append(_text(cell))
    return stats


# --- pieces -------------------------------------------------------------------


def program_of(p) -> dict:
    """What makes two parametric certificates about the same program."""
    return {"parameters": list(p["parameters"]), "objective": p["objective"],
            "constraints": p["constraints"], "sense": p.get("sense", "max"),
            "free": sorted(p.get("free") or [])}


def piece_box(p, ring):
    """A piece's box: its `box`, or the ray `p >= floor` of a shift-test
    certificate, which covers everything above its floors."""
    if p.get("box"):
        return _box(p["box"], ring)
    return {n: (Fraction(p["parameters"][n]), None) for n in ring}


def load(entry):
    """`(certificate, record)` for one piece: a Certificate, a dict, or a
    path. A path is recorded as a REFERENCE with its digest, so an atlas of
    two thousand boxes does not have to carry them all; anything else is
    embedded."""
    from .certificate import Certificate

    if isinstance(entry, Certificate):
        return entry, {"cert": entry.to_dict()}
    if isinstance(entry, dict):
        c = Certificate.from_dict(entry)
        return c, {"cert": c.to_dict()}
    from . import store

    head, member = store.split_ref(entry)
    ref = str(Path(head).resolve()) + ("" if member is None else "#" + member)
    try:
        c = Certificate.from_dict(store.read_json(ref))
    except Exception as e:  # noqa: BLE001 -- unreadable, for whatever reason
        raise NotAnAtlas(t("atlas.unreadable", path=str(entry), detail=str(e)))
    return c, {"path": ref, "digest": c.digest()}


def resolve(record):
    """The certificate a payload's piece names: embedded, or at its path --
    as recorded, then relative to the working directory -- and only if the
    digest still matches. Returns `(certificate or None, reason)`."""
    from .certificate import Certificate

    if record.get("cert") is not None:
        return Certificate.from_dict(record["cert"]), ""
    from . import store

    raw = record.get("path") or ""
    head, member = store.split_ref(raw)
    local = str(Path.cwd() / Path(head).name) + ("" if member is None
                                                  else "#" + member)
    for cand in (raw, local):
        if store.exists(cand):
            try:
                c = Certificate.from_dict(store.read_json(cand))
            except Exception:  # noqa: BLE001
                return None, t("atlas.unreadable", path=str(cand), detail="json")
            if c.digest() != record.get("digest"):
                return None, t("atlas.digest_moved", path=str(cand))
            return c, ""
    return None, t("atlas.piece_missing", path=raw)


def check_pieces(payload, certs, limits=None) -> list:
    """`(label, ok, detail)` for the per-piece claims, from resolved certs."""
    from .certificate import verify
    from .polynomials import Poly

    ring = tuple(payload["parameters"])
    want = payload["program"]
    claim = payload["claim"]
    region = payload.get("region") or {}
    out = []
    bad_verify, other_program, other_claim, other_region, not_param = \
        [], [], [], [], []
    for k, c in enumerate(certs):
        if c is None:
            bad_verify.append(str(k))
            continue
        if c.kind != "parametric_bound":
            not_param.append(str(k))
            continue
        p = c.payload
        if not verify(c, limits).ok:
            bad_verify.append(str(k))
        if program_of(p) != want:
            other_program.append(str(k))
        pc = p.get("claim") or {}
        if not (pc.get("holds") is True and pc.get("target") == claim["target"]
                and pc.get("relation") == claim["relation"]):
            other_claim.append(str(k))
        own = p.get("region") or {}
        mine = {Poly.parse(ring, g) for g in region.values()}
        if any(Poly.parse(ring, g) not in mine for g in own.values()):
            other_region.append(str(k))
    out.append(("kind", not not_param, ", ".join(not_param[:4]) or "-"))
    out.append(("verified", not bad_verify, ", ".join(bad_verify[:4]) or "-"))
    out.append(("program", not other_program, ", ".join(other_program[:4]) or "-"))
    out.append(("claim", not other_claim, ", ".join(other_claim[:4]) or "-"))
    out.append(("region", not other_region, ", ".join(other_region[:4]) or "-"))
    return out


def conditions_of(payload):
    from .polynomials import Poly

    ring = tuple(payload["parameters"])
    return [(n, Poly.parse(ring, g))
            for n, g in sorted((payload.get("region") or {}).items())]


def boxes_of(payload, certs):
    ring = tuple(payload["parameters"])
    boxes = [piece_box(c.payload, ring) for c in certs if c is not None]
    boxes += [_box(c["box"], ring) for c in payload.get("cited") or []]
    return boxes
