"""Data that crosses a language boundary, and a number that says it arrived.

`matrix` certifies the matrix it is given, exactly and without a solver. What
it cannot do is notice that the matrix is not the one your proof is about --
and the usual way for that to happen is not exotic. Somebody types the
coordinates into Python from a Lean file, or from a paper, and one entry is
wrong. The certificate is then perfect and about the wrong object.

A user put it in one line: *you can perfectly certify the wrong matrix.*

WHAT CLOSES IT is not a stronger certificate. It is a number both sides
compute SEPARATELY from their own copy of the data, and compare:

    h = 0
    h = (h * B + rows) mod p
    h = (h * B + cols) mod p
    for each row, in order:
        for each entry, in order:
            h = (h * B + (entry mod p)) mod p

    with p = 2^61 - 1 and B = 1000003, and `mod` meaning the NON-NEGATIVE
    residue: 0 <= x mod p < p, so -1 reduces to p - 1.

That last clause is not pedantry, and it was missing. "entry mod p" is
unambiguous as a residue class and ambiguous as a NUMBER, which is what both
sides have to agree on: Python's `%` returns the non-negative residue, and a
language whose `%` truncates toward zero returns -1 where this wants p - 1.
The two sides then compute different numbers over identical data and the
disagreement looks like a data error. Lean's `Int.emod` matches this; `Int.mod`
does not. A user crossing into Lean with negative entries hit exactly this and
had to pin the convention themselves.

Horner, nothing else. It is order-sensitive, so a transposed or permuted
matrix is a different number; it is arithmetic, so Lean closes the comparison
with `decide` and a referee closes it with a pocket calculator and patience;
and it needs no library on either side. That last property is the point. A
digest somebody has to install something to reproduce is a digest nobody
reproduces.

WHAT IT IS NOT is cryptographic. It catches a typo, a transposition, a wrong
sign, a missing row -- the things that actually happen when data is retyped.
It is not a defence against somebody constructing a collision on purpose, and
nothing in this file pretends otherwise. If the threat is an adversary rather
than a keyboard, hash the bytes with sha256, which the certificate's own
provenance already does for the spec.

THE DIRECTION OF TRUST. certo does not ask to be believed here. It prints the
number it computed over the data it certified; the other side computes the
same number over the data it holds. Agreement means the two objects are the
same, established by each side independently -- which is the only form of
agreement worth having across a boundary neither side can see over.
"""
from __future__ import annotations

import json
from pathlib import Path

from .i18n import t as _t

#: A Mersenne prime: reduction is a shift and an add, so a reimplementation in
#: a proof assistant or a shell script stays short and stays exact.
PRIME = (1 << 61) - 1

#: Odd, larger than any entry anybody writes by hand, and small enough that
#: `h * B` never needs more than the prime's width plus a few bits.
BASE = 1_000_003


class NotInterchangeable(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


def fingerprint(matrix) -> int:
    """The number both sides compute. See the module docstring for the rule."""
    rows = len(matrix)
    cols = len(matrix[0]) if rows else 0
    h = 0
    h = (h * BASE + rows) % PRIME
    h = (h * BASE + cols) % PRIME
    for row in matrix:
        if len(row) != cols:
            raise NotInterchangeable(_t("interchange.ragged"))
        for entry in row:
            h = (h * BASE + (int(entry) % PRIME)) % PRIME
    return h


def describe() -> dict:
    """Everything needed to recompute it, in the certificate itself.

    The constants travel. A number whose recipe lives only in this file's
    documentation is a number the other side has to take on faith, and taking
    things on faith across the boundary is the whole problem.
    """
    return {"algorithm": "horner", "prime": str(PRIME), "base": str(BASE),
            "order": "rows, then columns, after the two dimensions",
            # The constant that was NOT travelling. Without it the recipe is
            # complete for non-negative data and ambiguous for the rest.
            "residue": "non-negative: 0 <= x mod p < p, so -1 reduces to p - 1"}


# --- the file format -------------------------------------------------------


def dump(matrix, path=None, *, name="", note="") -> dict:
    """Canonical JSON: sorted keys, no floats, the fingerprint alongside.

    Canonical because two programs writing the same data must produce the same
    bytes -- otherwise a diff is noise and a hash of the file is useless.
    """
    rows = [[int(v) for v in row] for row in matrix]
    data = {
        "certo_interchange": 1,
        "name": name,
        "note": note,
        "rows": len(rows),
        "cols": len(rows[0]) if rows else 0,
        "entries": rows,
        "fingerprint": str(fingerprint(rows)),
        "fingerprint_recipe": describe(),
    }
    if path is not None:
        Path(path).write_text(
            json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False)
            + "\n", encoding="utf-8")
    return data


def load(path) -> dict:
    """Read a data file, and REFUSE it when its own fingerprint disagrees.

    A file carries the number it claims; recomputing it here costs nothing and
    catches the case that matters -- a file edited after it was written, which
    is exactly what happens when somebody fixes "just one entry" by hand.
    """
    p = Path(path)
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        raise NotInterchangeable(
            _t("interchange.unreadable", path=str(p),
               why="{}: {}".format(type(e).__name__, e))) from None

    if not isinstance(data, dict) or "entries" not in data:
        raise NotInterchangeable(_t("interchange.not_ours", path=str(p)))

    rows = data["entries"]
    if not isinstance(rows, list) or not all(isinstance(r, list) for r in rows):
        raise NotInterchangeable(_t("interchange.not_a_matrix", path=str(p)))
    for i, row in enumerate(rows):
        for v in row:
            if isinstance(v, bool) or not isinstance(v, int):
                raise NotInterchangeable(
                    _t("interchange.not_integer", path=str(p), row=i))

    got = fingerprint(rows)
    claimed = data.get("fingerprint")
    if claimed is not None and str(claimed) != str(got):
        raise NotInterchangeable(
            _t("interchange.fingerprint_differs", path=str(p),
               claimed=str(claimed), got=str(got)))

    for key, want in (("rows", len(rows)),
                      ("cols", len(rows[0]) if rows else 0)):
        if key in data and int(data[key]) != want:
            raise NotInterchangeable(
                _t("interchange.shape_differs", path=str(p), key=key,
                   claimed=data[key], got=want))

    data["entries"] = rows
    data["fingerprint"] = str(got)
    return data
