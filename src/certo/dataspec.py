"""Specs built from JSON, with no code executed.

`load_spec` compiles and runs the `.py` it is handed. That is inherent to the
DSL, it is documented, and for a person editing their own file it is the same
trust an editor already has. For an AGENT it is the thinnest part of the
surface: a model that writes a spec writes a program, and the tool that runs it
cannot tell the difference between a linear program and anything else Python
can do.

Most of the corpus does not need it. An LP, a packing, an integer matrix, a
CNF, a cone, a dependency chain -- these are DATA. So a spec may be a `.json`
file instead, and this module builds the dataclass from it without compiling
anything.

WHAT THIS GUARANTEES, exactly: no code from the file is executed. Nothing more.

WHAT IT DOES NOT GUARANTEE, and the distinction is the whole reason this is
not simply called "safe" in the prose: that the spec MEANS what you think. A
JSON `LPSpec` can still encode the wrong program, name the wrong resource, or
carry a constraint that says something other than the argument needs -- and
`lint`, the scope warnings and `verify`'s re-derivation are what work on that
problem. A mode that made people stop reading their own spec would trade a
small risk for a larger one.

A KEY STARTING WITH `_` IS A COMMENT, because JSON has none and a spec
format with no way to document itself is worse for whoever reads it next. No
spec field begins with one, so this cannot swallow a typo in a real name.

UNKNOWN KEYS ARE REFUSED rather than ignored. A typo in a field name that is
silently dropped is how a constraint goes missing, and this project has already
paid for that once: a coefficient on an undeclared variable turned a certified
1/3 into a certified 10.
"""
from __future__ import annotations

import json
import pathlib
from fractions import Fraction

from .i18n import t as _t


class NotData(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


#: The spec types whose whole content is data. Anything carrying a z3 formula
#: or a callable is absent on purpose: there is no way to write one in JSON,
#: and pretending otherwise would mean inventing an expression language --
#: which is the thing this project decided not to build.
BUILDABLE = (
    "LPSpec", "PackingSpec", "HypergraphSpec", "MatrixSpec", "LinearSystemSpec", "ConeSpec",
    "CycleSpec", "CoverSpec", "CNFSpec", "NumberSpec", "EquitableQuotientSpec",
)


def _exact(value):
    """Numbers arrive exact or not at all."""
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        # A float in JSON is a float in the certificate, and `verify` would
        # call it not citable. Refusing here says why, once, instead of at the
        # end of a run.
        raise NotData(_t("dataspec.float", value=value))
    if isinstance(value, str):
        try:
            return Fraction(value)
        except ValueError:
            return value
    if isinstance(value, list):
        return [_exact(v) for v in value]
    if isinstance(value, dict):
        return {k: _exact(v) for k, v in value.items()}
    return value


def build(kind: str, data: dict):
    """A dataclass of the named type, from plain data, or a refusal."""
    import dataclasses

    from . import spec as specmod

    if kind not in BUILDABLE:
        raise NotData(_t("dataspec.not_buildable", kind=kind,
                         known=", ".join(BUILDABLE)))
    cls = getattr(specmod, kind, None)
    if cls is None:
        raise NotData(_t("dataspec.unknown_type", kind=kind))

    fields = {f.name for f in dataclasses.fields(cls)}
    # JSON has no comments, and every `.py` example here carries a docstring
    # explaining what it is for. A key starting with `_` is that docstring:
    # no spec field begins with one, so the exception cannot swallow a typo in
    # a real field name -- which is the thing the strictness is for.
    given = {k for k in data if not k.startswith("_")}
    unknown = sorted(given - fields - {"type"})
    if unknown:
        raise NotData(_t("dataspec.unknown_fields", names=", ".join(unknown),
                         kind=kind, known=", ".join(sorted(fields))))

    kwargs = {k: _exact(v) for k, v in data.items()
              if k != "type" and not k.startswith("_")}
    try:
        return cls(**kwargs)
    except TypeError as exc:
        raise NotData(_t("dataspec.bad_fields", kind=kind, why=str(exc)))


def load(path, expected=None):
    """Read a `.json` spec. Nothing in the file is executed."""
    p = pathlib.Path(path).resolve()
    if not p.exists():
        raise FileNotFoundError(_t("spec.not_found", path=p))
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise NotData(_t("dataspec.bad_json", path=p.name, why=str(exc)))

    if not isinstance(data, dict) or "type" not in data:
        raise NotData(_t("dataspec.no_type",
                         known=", ".join(BUILDABLE)))

    obj = build(str(data["type"]), {k: v for k, v in data.items() if k != "card"})
    if isinstance(data.get("card"), dict):
        from . import card as _card

        c = data["card"]
        _card.declare(obj, role=c.get("role"), link=c.get("link"),
                      pending=c.get("pending"))
    if expected is not None and not isinstance(obj, expected):
        raise TypeError(_t("spec.wrong_type", got=type(obj).__name__,
                           want=expected.__name__))
    return obj
