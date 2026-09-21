"""Packings and hypergraphs: items competing for shared resources.

The same shape keeps reappearing -- cliques competing for edges, blocks
competing for points, anything competing for anything -- and rebuilding the LP
by hand each time is both tedious and a place for mistakes to hide.

    PackingSpec(items=[("T012", {"e01","e02","e12"}, 2), ...], capacities=1)

`to_lp()` hands back an `LPSpec`, so everything the exact machinery already
does comes for free: rational coefficients in, exact dual out, a certificate
that verifies without a solver.

THE DUAL IS THE LOAD CERTIFICATE. Constraint names are resource names, so
`y_r` reads directly as "the load carried by resource r" -- which is usually
the object you actually wanted, not the primal.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from itertools import combinations

from .exact import to_fraction
from .status import Verdict


@dataclass
class PackingSpec:
    """items: (name, resources, gain[, kind]). capacities: dict or a scalar.

    `kind` is free-form and only used to split the optimum by type:
    `restricted({"K3"})` gives the best you can do with triangles alone,
    which is what tells you whether mixing actually buys anything.
    """

    items: list
    capacities: object = 1              # dict resource -> cap, or one number
    sense: str = "max"
    integer: object = False             # True, or a set of item kinds
    title: str = ""
    # Named regions with bounds: [(name, {item: weight}, sense, bound)].
    # A resource cap says "this pair is used once"; a LOAD says something
    # about a region of the design -- "the within-A load stays under N_A" --
    # and the difference is that a load is part of the argument rather than
    # part of the encoding. They become rows like any other, so the dual
    # prices them, and the certificate records what the solution does to each.
    loads: list = field(default_factory=list)
    _kinds: dict = field(default_factory=dict, repr=False)

    def __post_init__(self):
        norm = []
        for it in self.items:
            name, resources, gain = it[0], list(it[1]), it[2]
            kind = it[3] if len(it) > 3 else ""
            if not resources:
                raise ValueError("item {} uses no resource".format(name))
            norm.append((str(name), resources, to_fraction(gain), str(kind)))
        names = [i[0] for i in norm]
        if len(set(names)) != len(names):
            raise ValueError("duplicate item names in the packing")

        known = set(names)
        seen = set()
        for entry in self.loads:
            if len(entry) != 4:
                raise ValueError(
                    "a load is (name, {item: weight}, sense, bound), got "
                    "{} fields".format(len(entry)))
            lname, weights, sense, _bound = entry
            if sense not in ("<=", ">=", "=="):
                raise ValueError("load {}: sense must be <=, >= or ==, not "
                                 "{}".format(lname, sense))
            if str(lname) in seen:
                raise ValueError("duplicate load name: {}".format(lname))
            seen.add(str(lname))
            unknown = sorted(str(k) for k in weights if str(k) not in known)
            if unknown:
                # A weight on an item that is not there is silent otherwise:
                # the row is simply weaker than intended.
                raise ValueError("load {} weights items that are not in the "
                                 "packing: {}".format(lname,
                                                      ", ".join(unknown[:5])))
        self.items = norm
        self._kinds = {i[0]: i[3] for i in norm}

    # -- structure ---------------------------------------------------------

    @property
    def resources(self) -> list:
        seen, out = set(), []
        for _, res, _, _ in self.items:
            for r in res:
                if r not in seen:
                    seen.add(r)
                    out.append(str(r))
        return out

    @property
    def kinds(self) -> list:
        return sorted({k for k in self._kinds.values() if k})

    def capacity_of(self, resource):
        if isinstance(self.capacities, dict):
            return to_fraction(self.capacities.get(resource, 1))
        return to_fraction(self.capacities)

    def restricted(self, kinds) -> "PackingSpec":
        """Only items of these kinds. This is the 'optimum by type'."""
        keep = {str(k) for k in kinds}
        return PackingSpec(
            items=[(n, r, g, k) for n, r, g, k in self.items if k in keep],
            capacities=self.capacities, sense=self.sense,
            integer=self.integer,
            title="{} [{}]".format(self.title, ", ".join(sorted(keep))),
        )

    # -- to the LP ---------------------------------------------------------

    def discrete_kinds(self) -> set:
        """Which item kinds are whole-or-nothing.

        `integer=True` means all of them; `integer={"K3"}` means triangles are
        placed whole while everything else may be fractional. A packing where
        the structural items are discrete and the rest is a fractional relaxation
        is the common shape, and forcing all-or-nothing changes the problem.
        """
        if self.integer is True:
            return {k for _, _, _, k in self.items}
        if not self.integer:
            return set()
        return set(self.integer)

    def to_lp(self):
        """An LPSpec. Constraint names are resource names, so the dual reads
        as a load per resource."""
        from .spec import LPSpec

        discrete = self.discrete_kinds()
        lp = LPSpec(sense=self.sense, integer=False,
                    title=self.title or "packing")
        for name, res, _, kind in self.items:
            # A discrete item cannot be taken more times than its tightest
            # resource allows, and saying so explicitly is what gives branch
            # and bound a finite tree to exhibit. With capacities of 1 -- the
            # usual case -- this makes the item binary, which it always was.
            hi = None
            if kind in discrete:
                caps = [to_fraction(self.capacity_of(str(r))) for r in res]
                hi = int(min(caps)) if caps else None
            lp.variable(name, hi=hi,
                        kind="integer" if kind in discrete else "continuous")
        lp.objective({name: gain for name, _, gain, _ in self.items})

        by_resource: dict = {}
        for name, res, _, _ in self.items:
            for r in res:
                by_resource.setdefault(str(r), []).append(name)
        for r in self.resources:
            lp.constraint({n: 1 for n in by_resource[r]}, "<=",
                          self.capacity_of(r), name=r)

        # Loads go in last and keep their own names, so the dual reads as a
        # price per REGION next to the price per resource.
        taken = set(self.resources)
        for lname, weights, sense, bound in self.loads:
            key = str(lname)
            if key in taken:
                raise ValueError("load {} collides with a resource name"
                                 .format(key))
            lp.constraint({str(k): v for k, v in weights.items()},
                          sense, bound, name=key)
            lp.load_names.append(key)
        return lp


    @classmethod
    def lists(cls, family, gains=None, title=""):
        """The `(list, pair)` packing: the shape 51 of 131 research scripts share.

        A "list" is a set -- a neighbourhood, a palette, a block. Taking the
        pair {a,b} from list j is an item; each pair may be taken once in
        total, and each (list, element) incidence once. That is all of it, and
        rebuilding it by hand every time is fifteen lines and a place for a
        constraint to go missing.

        `family` is a `SetFamily`, or anything iterable of iterables. Passing a
        SetFamily is worth it: `canonicalize="auto"` then quotients the
        counterexamples by relabelling for free.

        `gains` maps a pair's size to its worth; the default is 1 each, which
        is the counting version.
        """
        from itertools import combinations

        blocks = (family.blocks if hasattr(family, "blocks")
                  else [tuple(sorted(set(b))) for b in family])
        gains = gains or {}
        items = []
        for j, block in enumerate(blocks):
            for a, b in combinations(sorted(block), 2):
                items.append((
                    "t{}_{}_{}".format(j, a, b),
                    ["e{}_{}".format(a, b),        # the pair, once globally
                     "d{}_{}".format(j, a),        # (list j, element a)
                     "d{}_{}".format(j, b)],
                    gains.get(2, 1),
                    "pair",
                ))
        return cls(items=items, capacities=1, sense="max",
                   title=title or "lists packing")

    # -- convenience for graphs -------------------------------------------

    @classmethod
    def cliques_in_graph(cls, g, gains: dict, capacities=1,
                         title: str = "") -> "PackingSpec":
        """Pack cliques of the given sizes, with edges as the resources.

            PackingSpec.cliques_in_graph(g, {3: 2, 4: 5})

        `gains` maps clique size to its worth. Sizes and weights stay explicit
        because "edges minus one" is one convention among several.
        """
        items = []
        for size in sorted(gains):
            for s in combinations(range(g.n), size):
                if all(g.has_edge(a, b) for a, b in combinations(s, 2)):
                    res = ["e{}_{}".format(a, b) for a, b in combinations(s, 2)]
                    # SEPARATED, because concatenation is not injective on
                    # integer labels: `(1, 112)` and `(11, 12)` are both
                    # ascending and both spell `1112`. It survives to n = 111
                    # and then fails as "duplicate item names in the packing",
                    # which sends the reader hunting through their own code
                    # for a repeat they did not write.
                    items.append(("K{}_{}".format(size, "_".join(map(str, s))),
                                  res, gains[size], "K{}".format(size)))
        return cls(items=items, capacities=capacities,
                   title=title or "clique packing on n={}".format(g.n))


def loads_from_dual(cert) -> dict:
    """Read a packing dual back as {resource: load}.

    The dual of a packing is not a by-product: it is the load assignment that
    proves the bound, and it is usually what you want to quote.
    """
    p = cert.payload if hasattr(cert, "payload") else cert.get("payload", {})
    names, dual = p.get("names", []), p.get("dual", [])
    return {n: v for n, v in zip(names, dual) if str(v) not in ("0", "0.0")}


def gap(spec, limits=None, target=None):
    """The integrality gap, with BOTH sides certified.

    `nu` against `mu*` is the question a packing is usually asked, and it used
    to be two runs someone subtracted afterwards -- two artefacts, two chances
    to line up the wrong pair. Here they travel together: the fractional
    optimum with its exact dual, the integral optimum with a feasible point,
    and the difference as one exact rational.

    Nothing new is proved. What is added is that the two numbers are about the
    same packing, which two files in a folder cannot say.
    """
    from . import exact
    from .certificate import gap_certificate
    from .engines import lp, mixed

    # BOTH HALVES ARE BUILT HERE, and that symmetry is the fix for a defect
    # that reported the strongest possible conclusion in this domain -- a
    # gap of zero -- from a flag combination.
    #
    # The integral half was already constructed explicitly. The fractional
    # half was inherited from the spec, so a `PackingSpec(integer=True)` gave
    # `mu` = the INTEGER optimum, compared against itself: `gap 0` where the
    # gap is 3/2, on a run of seven orders that all came back zero. `--gap`
    # asks for the relaxation against the integer optimum whatever the spec
    # says it is, so it builds the relaxation.
    relaxed = PackingSpec(items=spec.items, capacities=spec.capacities,
                          sense=spec.sense, integer=False, title=spec.title,
                          loads=spec.loads)
    overrode = bool(spec.integer)
    frac = lp.opt(relaxed.to_lp(), limits)
    if frac.verdict is not Verdict.SATISFIABLE or not frac.meta.get("exact"):
        return None, frac

    whole = PackingSpec(items=spec.items, capacities=spec.capacities,
                        sense=spec.sense, integer=True, title=spec.title)
    integral = mixed.mixed(whole.to_lp(), limits)
    if integral.verdict not in (Verdict.SATISFIABLE, Verdict.REFUTED):
        return None, integral

    mu = exact.to_fraction(frac.meta["objective"])
    nu = exact.to_fraction(integral.meta["achieved"])
    cert = gap_certificate(
        fractional=frac.certificate.to_dict(),
        integral=integral.certificate.to_dict(),
        mu=exact.serialize(mu), nu=exact.serialize(nu),
        gap=exact.serialize(mu - nu),
        tight=[r for r, v in loads_from_dual(frac.certificate).items()
               if exact.to_fraction(v) > 0],
        level=integral.meta.get("level", "feasible"),
        title=spec.title,
    )
    # NOT "level": `emit` reserves that key for a sweep's predicate level, and
    # two different meanings under one name is how a display ends up saying
    # something nobody meant.
    return cert, {"mu": exact.serialize(mu), "nu": exact.serialize(nu),
                  "gap": exact.serialize(mu - nu),
                  # The same key `opt` uses for the same number, so one script
                  # reads both. It was only reachable at
                  # `certificate.payload.fractional.payload.objective`, which
                  # is not a path anybody deduces without the source.
                  "objective": exact.serialize(mu),
                  # Said rather than done silently: the spec declared itself
                  # integer and the fractional half ignored that, because that
                  # is what a gap IS.
                  "relaxed_for_gap": overrode,
                  "integral_level": integral.meta.get("level"),
                  "tight": len(cert.payload["tight"]),
                  # `--target` used to be dropped on this path: the flag was
                  # accepted, the number never compared, and the verdict came
                  # back SATISFIABLE either way. A flag that is silently
                  # ignored is worse than one that is refused.
                  #
                  # It compares against `nu`, the integer value ACHIEVED,
                  # because that is what a packing target asks about. So
                  # `reached` true means a point was exhibited; false means
                  # not by what was found -- which is only a refutation when
                  # the integer optimum is global, and the caller is told
                  # which of the two it has.
                  "target": None if target is None else exact.serialize(
                      exact.to_fraction(target)),
                  "reached": (None if target is None
                              else nu >= exact.to_fraction(target)),
                  "deficit": (None if target is None else exact.serialize(
                      max(exact.to_fraction(target) - nu,
                          exact.to_fraction(0))))}
