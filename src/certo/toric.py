"""Local toric data: the numbers two geometric theorems consume.

Two implications sit at the end of a route this project has been feeding:

    a regular unimodular cone of height one  =>  smooth chart, SNC fibre
    discrepancy zero and multiplicity one    =>  crepant, reduced fibre

Neither is proved here, and neither should be. They are theorems about
varieties, they belong in a proof assistant, and certo's part is the arrow
before them: find and certify the finite, explicit data they consume. What
this module does is stop that data being ASSUMED.

WHAT IT REPLACES. An audit of the second implication, written by a user
against certo 0.9, reads in full:

    height, discrepancy, multiplicity = Ints(...)
    assume("height_one",            height == 1)
    assume("discrepancy_formula",   discrepancy == height - 1)
    assume("multiplicity_formula",  multiplicity == height)
    claim(And(discrepancy == 0, multiplicity == 1))

Three integers and two formulas taken as hypotheses. The implication is then
checked and the audit is honest about what it checked -- but the formulas are
exactly the step where a cone becomes a number, and nothing was computing them
from a cone. Here they are computed.

THE FOUR QUANTITIES, and each is arithmetic:

  PRIMITIVE          a ray generator is primitive when its coordinates have
                     gcd one IN THE DECLARED LATTICE. Not in whichever
                     lattice the coordinates happen to look natural in --
                     see below, because this is where the real instance bites.

  MULTIPLICITY       for a simplicial cone of full dimension, the absolute
                     determinant of the matrix of its ray generators. One
                     means regular, which is what "smooth chart" reads.

  HEIGHT             a functional `u` with `<u, v> = 1` for every generator.
                     It exists or it does not, it is unique when the cone is
                     full-dimensional, and finding it is an exact linear
                     solve. "Height one" is the statement that it exists.

  DISCREPANCY        of a ray `w` in the cone: `<u, w> - 1`. Zero is crepant.
                     A subdivision's new rays are exactly the ones to ask
                     about, and the barycentre is the usual one.

THE LATTICE IS DECLARED, NEVER GUESSED, and this is not pedantry. A real cell
from the route above has generators `(4,0,0,0)`, `(2,2,0,0)`, `(2,0,2,0)`,
`(1,1,1,1)`: multiplicity 16, height functional `(1/4,1/4,1/4,1/4)`, every
discrepancy zero. Read in `Z^4` those generators are NOT primitive -- their
gcds are 4, 2, 2, 1 -- so "height one" and "multiplicity" are statements about
a different lattice than the coordinates suggest. Getting that wrong does not
produce an error; it produces a different number, confidently. So the lattice
is an input, its default is stated, and non-primitive generators are reported
rather than silently normalised.

WHAT IS NOT CLAIMED. That multiplicity one implies a smooth chart. That
discrepancy zero implies a crepant modification. That the fibre is SNC or
reduced. Those are the theorems, they are why the proof assistant is there,
and a certificate that quietly asserted them would be the exact substitution
this project exists to refuse.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd

from .i18n import t as _t


class NotToric(ValueError):
    """Raised with what was wrong: a bare failure helps nobody."""


def _vector(values, name):
    out = []
    for v in values:
        if isinstance(v, bool) or not isinstance(v, int):
            num = getattr(v, "numerator", None)
            if num is None or getattr(v, "denominator", 0) != 1:
                raise NotToric(_t("toric.not_integer", name=name))
            v = num
        out.append(int(v))
    if not out:
        raise NotToric(_t("toric.empty_ray", name=name))
    return out


def rays_of(spec) -> dict:
    """The generators, as named integer vectors of one common dimension."""
    raw = dict(spec.rays)
    if not raw:
        raise NotToric(_t("toric.no_rays"))
    out, dim = {}, None
    for name, coords in raw.items():
        v = _vector(coords, str(name))
        if dim is None:
            dim = len(v)
        elif len(v) != dim:
            raise NotToric(_t("toric.mixed_dimension", name=str(name),
                              got=len(v), want=dim))
        out[str(name)] = v
    return out


def content(v) -> int:
    """The gcd of the coordinates: one means primitive."""
    g = 0
    for c in v:
        g = gcd(g, abs(int(c)))
    return g


def in_lattice(v, basis):
    """`v` written in the declared lattice's basis, or None if it is not in it.

    The lattice is given by a basis as ROWS. A vector is in the lattice when
    the linear system has an integer solution, which is the Smith question --
    so this is `solve` over Z, arriving by a different door.
    """
    from . import linsolve

    if basis is None:
        return [Fraction(c) for c in v]
    columns = [[Fraction(row[j]) for row in basis] for j in range(len(v))]
    out = linsolve.solve_integer(columns, [Fraction(c) for c in v])
    if out["status"] == linsolve.NONE:
        return None
    return out["solution"]


def multiplicity(rays, names=None, basis=None, rows=None) -> dict:
    """The index of the sublattice the generators span, IN THE DECLARED
    LATTICE.

    It is `|det|` of the generator matrix -- but of the generators written in
    the lattice's own coordinates, which is the whole point. The first version
    of this took the determinant in ambient coordinates and reported 16 for a
    cone that is regular in its own lattice: a confidently wrong number of
    exactly the kind this module exists to stop. Read in `Z^4` and read in the
    lattice the generators are primitive in, the same cone gives 16 and 1.

    Defined for a simplicial cone of full dimension. Anything else is refused
    rather than answered with a determinant of the wrong shape -- a number
    that looks like a multiplicity and is not one is worse than no number.

    `rows` are those coordinates when the caller already has them. They were
    being computed three times for one cone -- here, again per generator for
    primitivity, and a third time by the verifier -- and thrown away each
    time, which is why `toric_cone` did not carry the matrix a user then had
    to reconstruct by hand. The rows come in, and `certify` keeps them.
    """
    from . import lattice as latt

    order = list(names or sorted(rays))
    if rows is None:
        rows = []
        for n in order:
            coords = in_lattice(rays[n], basis)
            if coords is None:
                raise NotToric(_t("toric.outside_lattice", name=n))
            rows.append([Fraction(c) for c in coords])
    elif any(r is None for r in rows):
        outside = [n for n, r in zip(order, rows) if r is None]
        raise NotToric(_t("toric.outside_lattice", name=outside[0]))

    n, m = len(rows), len(rows[0])
    if n != m:
        raise NotToric(_t("toric.not_simplicial", rays=n, dim=m))
    if any(c.denominator != 1 for row in rows for c in row):
        raise NotToric(_t("toric.not_integral_in_lattice"))

    out = latt.analyse([[int(c) for c in row] for row in rows], "det")
    if out["rank"] < n:
        raise NotToric(_t("toric.dependent", rank=out["rank"], rays=n))
    return {"value": abs(out["det"]), "det": out["det"], "order": order,
            "rank": out["rank"], "in_lattice": basis is not None}


def height_functional(rays, names=None):
    """The `u` with `<u, v> = 1` for every generator, exactly, or None.

    Its EXISTENCE is what "height one" says. Its entries need not be integral:
    in the lattice the coordinates are written in they usually are not, and
    that is a statement about the lattice rather than a failure.
    """
    from . import linsolve

    order = list(names or sorted(rays))
    A = [[Fraction(c) for c in rays[n]] for n in order]
    out = linsolve.solve_rational(A, [Fraction(1)] * len(order))
    if out["status"] == linsolve.NONE:
        return None
    return {"u": out["solution"], "unique": out["status"] == linsolve.UNIQUE,
            "kernel": out["kernel"], "order": order}


def pairing(u, v) -> Fraction:
    return sum((Fraction(a) * Fraction(b) for a, b in zip(u, v)), Fraction(0))


def certify(spec) -> dict:
    """Every quantity, and what each one is a statement about."""
    rays = rays_of(spec)
    basis = getattr(spec, "lattice", None)
    order = list(getattr(spec, "order", None) or sorted(rays))
    unknown = [n for n in order if n not in rays]
    if unknown:
        raise NotToric(_t("toric.unknown_ray", names=", ".join(unknown[:3])))

    primitive, outside, relative = {}, [], []
    for name in order:
        coords = in_lattice(rays[name], basis)
        relative.append(None if coords is None
                        else [Fraction(c) for c in coords])
        if coords is None:
            outside.append(name)
            primitive[name] = None
            continue
        primitive[name] = content([Fraction(c).numerator for c in coords])

    # The height question is meaningful whether or not the cone is simplicial,
    # so it is asked first and a missing multiplicity is recorded rather than
    # raised. Refusing the whole certificate because one of four quantities is
    # undefined loses the other three.
    height = height_functional(rays, order)
    try:
        mult = multiplicity(rays, order, basis, rows=relative)
        mult_why = None
    except NotToric as exc:
        mult, mult_why = None, str(exc)

    heights, discrepancies = {}, {}
    if height is not None:
        u = [Fraction(v) for v in height["u"]]
        for name in order:
            h = pairing(u, rays[name])
            heights[name] = str(h)
            discrepancies[name] = str(h - 1)

    extra = {}
    for name, coords in sorted(dict(getattr(spec, "subdivision", {}) or {}).items()):
        v = _vector(coords, str(name))
        if len(v) != len(rays[order[0]]):
            raise NotToric(_t("toric.mixed_dimension", name=str(name),
                              got=len(v), want=len(rays[order[0]])))
        entry = {"coords": v, "content": content(v)}
        if height is not None:
            h = pairing([Fraction(x) for x in height["u"]], v)
            entry["height"] = str(h)
            entry["discrepancy"] = str(h - 1)
        extra[str(name)] = entry

    return {
        "rays": {n: rays[n] for n in order},
        "order": order,
        "dimension": len(rays[order[0]]),
        "lattice": ([list(map(int, row)) for row in basis]
                    if basis is not None else None),
        "primitive": {n: (None if primitive[n] is None else int(primitive[n]))
                      for n in order},
        "outside_lattice": outside,
        "multiplicity": None if mult is None else str(mult["value"]),
        "determinant": None if mult is None else str(mult["det"]),
        "multiplicity_why_not": mult_why,
        "multiplicity_in": "declared lattice" if basis is not None
                           else "the ambient Z^{}".format(len(rays[order[0]])),
        # THE GENERATORS IN THE LATTICE'S OWN COORDINATES -- the matrix whose
        # determinant the multiplicity IS. It was computed here, again inside
        # `multiplicity`, and a third time by the verifier, and discarded
        # every time; a user needing it for a change of basis had to rebuild
        # it from the rays and the basis by hand. Optional, which the frozen
        # schema allows, and `verify` recomputes it rather than reading it.
        "relative": None if any(r is None for r in relative) else {
            "matrix": [[str(c) for c in row] for row in relative],
            "orientation": "one row per generator, in the order of `order`; "
                           "one column per vector of `lattice`, itself rows. "
                           "M = R * L, where R is this matrix and L the basis.",
        },
        "regular": None if mult is None else mult["value"] == 1,
        "height_one": height is not None,
        "height_functional": (None if height is None
                              else [str(v) for v in height["u"]]),
        "height_unique": None if height is None else height["unique"],
        "heights": heights,
        "discrepancies": discrepancies,
        # A generator's discrepancy is zero BY CONSTRUCTION whenever a height
        # functional exists -- that is what `<u, v> = 1` says. Reporting the
        # cone "crepant" on that basis said nothing and sounded like something:
        # the A1 singularity came back crepant with no subdivision at all. The
        # question is about the rays a subdivision ADDS, so it is None when
        # none were named.
        "crepant": (None if not extra or height is None else
                    all(Fraction(e["discrepancy"]) == 0
                        for e in extra.values() if "discrepancy" in e)),
        "generators_at_height_one": bool(discrepancies) and all(
            Fraction(v) == 0 for v in discrepancies.values()),
        "subdivision": extra,
        "title": getattr(spec, "title", ""),
    }
