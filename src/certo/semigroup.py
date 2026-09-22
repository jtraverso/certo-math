"""Affine semigroups, as a CHECKER.

    S = N*a_1 + ... + N*a_k   inside a declared lattice

WHAT THIS IS FOR. A route through toric geometry asks, over and over, whether
a monoid is normal, whether a proposed set of generators is the minimal one,
and whether a particular lattice point is in the semigroup or merely in the
cone over it. Those are the finite, explicit questions underneath a geometric
statement, and until now certo could say nothing about any of them: `cone`
answers questions about the RATIONAL cone, and the gap between the cone and
the semigroup is precisely where normality lives.

THE DIVISION OF LABOUR, which is the whole design. Computing a Hilbert basis
is genuinely hard -- Normaliz exists for a reason -- and CHECKING one is
arithmetic. So nothing here computes a minimal generating set. What it does is
take the objects as INPUT and verify the finite claims about them, the same
way `parametric` takes a dual and `cover` takes a partition.

WHY EVERY SEARCH HERE TERMINATES. A pointed affine semigroup carries a
GRADING: a linear functional `u` with `<u, a_i> >= 1` for every generator. If
one exists, then any representation

    v = c_1 a_1 + ... + c_k a_k,   c_i non-negative integers

satisfies `sum c_i <u, a_i> = <u, v>`, so `sum c_i <= <u, v>` and the search
for a representation is over a FINITE set whose size is computed, not guessed.
That is what turns "v is not in S" from a conjecture into a certificate: the
bound travels with the answer and a verifier recomputes it.

If no such functional exists the semigroup is not pointed, the search is not
finite, and this says so rather than looking for a while and reporting
nothing. Not pointed is a real answer about the object, not a failure.

WHAT IS CERTIFIED, and each of these is arithmetic to check:

  POINTED           a functional `u` with `<u, a_i> >= 1` for all i. Its
                    existence is the statement; the vector is the proof.

  IN THE CONE       non-negative RATIONAL coefficients, by Caratheodory over
                    subsets of independent generators. When the point is
                    outside, a separating functional `y` with `<y, a_i> <= 0`
                    and `<y, v> > 0` -- one vector, checked by k+1 dot
                    products, instead of "I tried everything".

  IN THE GROUP      integer coefficients, possibly negative, via Hermite
                    normal form. Exact and always decidable.

  IN THE SEMIGROUP  non-negative INTEGER coefficients, or the graded bound
                    that makes their absence a proof.

  NOT NORMAL        the three above combined on one witness `v`: in the cone,
                    in the group, not in the semigroup. Every part checkable,
                    and together they are a complete refutation of normality.

WHAT IS REFUSED, and deliberately. That S IS normal. Establishing it means
deciding membership for every lattice point of the cone, which is the problem
Normaliz solves and is not arithmetic. A witness refutes normality; nothing
here ever asserts it. The command returns `out_of_theory` when asked, which
is an honest "not mine" rather than a silence -- and it is recorded, so that
the next person ranking this work can count how often it was wanted.
"""
from __future__ import annotations

import itertools
from fractions import Fraction

from .i18n import t as _t

#: How many generator subsets Caratheodory and the facet search may look at
#: before giving up. Exceeding it is reported, never rounded off.
MAX_SUBSETS = 20_000

#: How many partial representations the graded search may expand.
MAX_NODES = 200_000


class NotASemigroup(ValueError):
    """The input is not an affine semigroup this can read."""


def _vector(values, name):
    try:
        out = [int(v) for v in values]
    except (TypeError, ValueError):
        raise NotASemigroup(_t("semigroup.not_integer", name=name)) from None
    if not out:
        raise NotASemigroup(_t("semigroup.empty_generator", name=name))
    return out


def generators_of(spec) -> dict:
    raw = dict(getattr(spec, "generators", None) or {})
    if not raw:
        raise NotASemigroup(_t("semigroup.no_generators"))
    out = {}
    for name, coords in raw.items():
        out[str(name)] = _vector(coords, str(name))
    dims = {len(v) for v in out.values()}
    if len(dims) != 1:
        raise NotASemigroup(_t("semigroup.mixed_dimension", got=sorted(dims)))
    return out


# --- linear algebra over the rationals, exactly -----------------------------


def _solve(rows, rhs):
    """One solution of `M z = rhs` in Fractions, or None. Free vars get 0."""
    from .exact import solve_exact
    try:
        return solve_exact(rows, rhs)
    except Exception:  # noqa: BLE001
        return None


def _rank(vectors) -> int:
    """Rank over Q, by elimination."""
    M = [[Fraction(v) for v in row] for row in vectors]
    r, cols = 0, (len(M[0]) if M else 0)
    for c in range(cols):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = Fraction(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return r


def dot(u, v) -> Fraction:
    return sum((Fraction(a) * Fraction(b) for a, b in zip(u, v)), Fraction(0))


# --- pointedness: the functional that makes everything else finite ---------


def positive_functional(gens):
    """A `u` with `<u, a> >= 1` for every generator, or None.

    Found by trying the sums of independent subsets rather than by running an
    LP. It is not complete in general and does not pretend to be: what comes
    back is either a functional, which is a PROOF the semigroup is pointed, or
    None, which is "no grading found" and not "no grading exists". The two are
    reported as different things, because a search that failed and a search
    that succeeded at proving a negative are different facts.
    """
    A = list(gens)
    if not A:
        return None
    d = len(A[0])

    # The sum of the generators is the obvious candidate and works whenever
    # the cone is pointed and reasonably behaved; the coordinate functionals
    # catch the common orthant-shaped cases.
    cands = [[sum(a[j] for a in A) for j in range(d)]]
    for j in range(d):
        e = [0] * d
        e[j] = 1
        cands.append(e)
        cands.append([-x for x in e])
    cands.append([1] * d)

    # And the normals to spanning subsets, which is what a facet-defining
    # functional looks like when the cone is not full-dimensional.
    seen = 0
    for combo in itertools.combinations(range(len(A)), min(d - 1, len(A))):
        seen += 1
        if seen > MAX_SUBSETS:
            break
        n = _normal_to([A[i] for i in combo], d)
        if n is not None:
            cands.append(n)
            cands.append([-x for x in n])

    # THE GRADING IS CHOSEN, NOT TAKEN. Every valid functional proves the
    # semigroup pointed equally well, but `<u, v>` is the bound on the search
    # for a representation, so a functional with small pairings costs less
    # than one with large ones -- on the first real example, 1 against 11 for
    # the same question. Cheap to pick: they have all been computed anyway.
    best = None
    for u in cands:
        if not any(u):
            continue
        vals = [dot(u, a) for a in A]
        if all(v > 0 for v in vals):
            # Scale to integers with every pairing at least 1.
            lcm = 1
            for v in vals:
                lcm = lcm * v.denominator // _gcd(lcm, v.denominator)
            scaled = [Fraction(x) * lcm for x in u]
            m = min(dot(scaled, a) for a in A)
            if m <= 0:
                continue
            mult = Fraction(1, 1) if m >= 1 else Fraction(1) / m
            out = [Fraction(x) * mult for x in scaled]
            if all(dot(out, a) >= 1 for a in A):
                cand = [int(x) if Fraction(x).denominator == 1 else x
                        for x in out]
                cost = max(dot(cand, a) for a in A)
                if best is None or cost < best[0]:
                    best = (cost, cand)
    return None if best is None else best[1]


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def _normal_to(vectors, d):
    """A non-zero integer vector orthogonal to all of them, or None."""
    if not vectors:
        return None
    rows = [[Fraction(x) for x in v] for v in vectors]
    # Solve rows . n = 0 by elimination, taking one free direction.
    M = [list(r) for r in rows]
    piv_col, r = {}, 0
    for c in range(d):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = Fraction(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv_col[c] = r
        r += 1
    free = [c for c in range(d) if c not in piv_col]
    if not free:
        return None
    f = free[0]
    n = [Fraction(0)] * d
    n[f] = Fraction(1)
    for c, row in piv_col.items():
        n[c] = -M[row][f]
    den = 1
    for x in n:
        den = den * x.denominator // _gcd(den, x.denominator)
    out = [int(x * den) for x in n]
    g = 0
    for x in out:
        g = _gcd(g, x)
    return [x // g for x in out] if g else None


# --- the rational cone ------------------------------------------------------


def in_cone(gens, v):
    """Non-negative rational coefficients for `v`, by Caratheodory.

    Every point of a cone is a non-negative combination of at most `rank`
    LINEARLY INDEPENDENT generators, so the search is over subsets of that
    size rather than over all of them, and each candidate is one exact solve.
    """
    A = list(gens)
    d = len(v)
    rank = _rank(A) if A else 0
    seen = 0
    for size in range(1, min(rank, len(A)) + 1):
        for combo in itertools.combinations(range(len(A)), size):
            seen += 1
            if seen > MAX_SUBSETS:
                return {"exhausted": False, "looked_at": seen}
            sub = [A[i] for i in combo]
            if _rank(sub) != size:
                continue
            rows = [[Fraction(sub[j][i]) for j in range(size)] for i in range(d)]
            sol = _solve(rows, [Fraction(x) for x in v])
            if sol is None or len(sol) != size:
                continue
            if any(c < 0 for c in sol):
                continue
            # An exact solve of an overdetermined system can return something
            # that is not a solution; the check is one multiplication.
            if any(sum((sol[j] * Fraction(sub[j][i]) for j in range(size)),
                       Fraction(0)) != Fraction(v[i]) for i in range(d)):
                continue
            coeffs = [Fraction(0)] * len(A)
            for j, i in enumerate(combo):
                coeffs[i] = sol[j]
            return {"coefficients": coeffs, "support": list(combo),
                    "exhausted": True, "looked_at": seen}
    return {"coefficients": None, "exhausted": True, "looked_at": seen}


def separating(gens, v):
    """A `y` with `<y, a_i> <= 0` for all generators and `<y, v> > 0`.

    The reason a negative answer about the cone is worth as much as a positive
    one: one vector, checked by k+1 dot products, rather than a claim that a
    search was exhaustive.
    """
    A = list(gens)
    if not A:
        return None
    d = len(v)
    cands = []
    for j in range(d):
        e = [0] * d
        e[j] = 1
        cands.append(e)
        cands.append([-x for x in e])
    seen = 0
    for size in range(1, min(d, len(A)) + 1):
        for combo in itertools.combinations(range(len(A)), size):
            seen += 1
            if seen > MAX_SUBSETS:
                break
            n = _normal_to([A[i] for i in combo], d)
            if n is not None:
                cands.append(n)
                cands.append([-x for x in n])
    for y in cands:
        if not any(y):
            continue
        if all(dot(y, a) <= 0 for a in A) and dot(y, v) > 0:
            return [int(x) for x in y]
    return None


# --- the group --------------------------------------------------------------


def in_group(gens, v):
    """Integer coefficients, possibly negative, or None. Exact, via Hermite."""
    from . import lattice

    A = [list(map(int, a)) for a in gens]
    try:
        h = lattice.hermite(A)
    except Exception:  # noqa: BLE001
        return None
    H, U = h["h"], h["u"]           # H = U . A, U unimodular

    # Reduce v against the rows of H. Solvable over Z exactly when every
    # pivot divides the running remainder at its column.
    rem = [Fraction(x) for x in v]
    coeff_h = [0] * len(H)
    for r, c in enumerate(h["pivots"]):
        if rem[c] == 0:
            continue
        q = rem[c] / Fraction(H[r][c])
        if q.denominator != 1:
            return None
        q = int(q)
        coeff_h[r] = q
        rem = [a - q * Fraction(b) for a, b in zip(rem, H[r])]
    if any(x != 0 for x in rem):
        return None
    # v = sum coeff_h[r] H[r] = sum coeff_h[r] (U.A)[r], so the coefficients
    # against the ORIGINAL generators are coeff_h . U.
    out = [sum(coeff_h[r] * int(U[r][j]) for r in range(len(H)))
           for j in range(len(A))]
    if any(sum(out[j] * A[j][i] for j in range(len(A))) != v[i]
           for i in range(len(v))):
        return None
    return out


# --- the semigroup itself ---------------------------------------------------


def in_semigroup(gens, v, u, max_nodes=MAX_NODES):
    """Non-negative INTEGER coefficients, using the grading to stay finite.

    Returns one of:
      {"coefficients": [...], "degree": D}          it is in S, here is how
      {"coefficients": None, "bound": N, ...}       it is NOT, and N bounds
                                                    every representation that
                                                    was ruled out
      {"gave_up": True, ...}                        the budget ran out first

    The third is not the second. A search that stopped early has established
    nothing, and saying so is the difference between this and a tool that
    reports "no" when it means "not found".
    """
    A = [list(map(int, a)) for a in gens]
    if u is None:
        return {"coefficients": None, "gave_up": True, "why": "ungraded"}

    deg_v = dot(u, v)
    degs = [dot(u, a) for a in A]
    if any(dd <= 0 for dd in degs):
        return {"coefficients": None, "gave_up": True, "why": "ungraded"}
    # A fractional degree is a proof of absence ONLY when every generator's
    # degree is a whole number: `sum c_i deg(a_i) = deg(v)` with integer `c_i`
    # then forces `deg(v)` integral. The scaling in `positive_functional` does
    # make them integral, and this checks it rather than remembering it --
    # because if that ever stops being true, the failure is a wrong "not in
    # the semigroup", which is the one kind of wrong answer that matters here.
    integral = all(Fraction(dd).denominator == 1 for dd in degs)
    if deg_v < 0 or (integral and deg_v.denominator != 1):
        return {"coefficients": None, "bound": 0, "degree": str(deg_v),
                "exhausted": True}
    if not integral and deg_v.denominator != 1:
        return {"coefficients": None, "gave_up": True, "why": "ungraded"}

    bound = int(deg_v)              # sum of coefficients cannot exceed this
    target = tuple(int(x) for x in v)
    dim = len(target)

    # Breadth over partial sums, keyed by the point reached. The grading keeps
    # the frontier finite: nothing with degree above `deg_v` can be extended
    # into `v`, because every generator adds at least one to the degree.
    start = tuple([0] * dim)
    # ZERO IS IN EVERY SEMIGROUP, by the empty combination. The first version
    # of this only compared a point to the target AFTER taking a step, so the
    # origin came back "not in S" -- and then, being in the cone and in the
    # group, it certified every semigroup non-normal from its own zero. A
    # wrong `unsat` is the one failure this project cannot have, and it was
    # sitting in the base case.
    if start == target:
        return {"coefficients": [0] * len(A), "degree": str(deg_v),
                "nodes": 0}

    seen = {start: []}
    frontier = [start]
    nodes = 0
    while frontier:
        nxt = []
        for point in frontier:
            for j, a in enumerate(A):
                nodes += 1
                if nodes > max_nodes:
                    return {"coefficients": None, "gave_up": True,
                            "why": "budget", "nodes": nodes,
                            "bound": bound}
                cand = tuple(p + x for p, x in zip(point, a))
                if dot(u, cand) > deg_v:
                    continue
                if cand in seen:
                    continue
                path = seen[point] + [j]
                seen[cand] = path
                if cand == target:
                    coeffs = [0] * len(A)
                    for j2 in path:
                        coeffs[j2] += 1
                    return {"coefficients": coeffs, "degree": str(deg_v),
                            "nodes": nodes}
                nxt.append(cand)
        frontier = nxt
    return {"coefficients": None, "bound": bound, "degree": str(deg_v),
            "exhausted": True, "nodes": nodes}


# --- a proposed minimal generating set --------------------------------------


def irreducible_in(gens, h, u, max_nodes=MAX_NODES):
    """Is `h` a sum of two NON-ZERO elements of S?

    The characterisation that makes this finite and cheap: `h` is reducible
    exactly when some generator `a` has `h - a` in S and `h - a` non-zero.
    Any decomposition `h = s + s'` with both non-zero has `s` containing at
    least one generator, and removing it leaves `h - a` in S; the converse is
    immediate. So `k` membership questions, each of degree strictly BELOW
    `<u, h>`, decide it -- the same grading, one rung down.

    Returns {"irreducible": bool, "witness": ...}. A reducible element comes
    back with the decomposition that reduces it, because "not irreducible" is
    a claim and a claim needs something attached.
    """
    A = [list(map(int, a)) for a in gens]
    for i, a in enumerate(A):
        rest = [x - y for x, y in zip(h, a)]
        if not any(rest):
            continue                     # h = a exactly: that is not a split
        got = in_semigroup(A, rest, u, max_nodes)
        if got.get("gave_up"):
            return {"irreducible": None, "why": got.get("why", "budget")}
        if got.get("coefficients") is not None:
            return {"irreducible": False, "minus": i, "rest": rest,
                    "rest_coefficients": got["coefficients"]}
    return {"irreducible": True}


def check_hilbert(gens, proposed, u, max_nodes=MAX_NODES,
                  gen_names=None) -> dict:
    """Is `proposed` the minimal generating set of `S = N.gens`?

    THIS ONE IS DECIDED, NOT MERELY REFUTED, which is worth saying next to
    normality, where the opposite holds. For a POINTED affine semigroup the
    minimal generating set is unique and is exactly the set of irreducible
    non-zero elements. So three bounded questions settle it:

      1. every `h` is IN S                    -- coefficients
      2. every `h` is IRREDUCIBLE in S        -- k membership tests, one rung
                                                 down in the grading
      3. every generator is in `N.H`          -- so `<H> = S`

    Given 1 and 2, `H` is contained in the irreducibles; given 3, every
    irreducible must be in `H`, since an irreducible cannot be written from
    anything else. The two inclusions are the equality, and each half is
    arithmetic.

    Without a grading none of the three searches terminates, and this returns
    `decided: False` rather than looking for a while.
    """
    A = [list(map(int, a)) for a in gens]
    H = [list(map(int, h)) for _, h in proposed]
    names = [n for n, _ in proposed]
    gen_names = list(gen_names or ["g{}".format(i) for i in range(len(A))])

    if u is None:
        return {"decided": False, "why": "ungraded", "elements": {},
                "is_minimal_generating_set": None}

    elements, trouble = {}, []
    for name, h in zip(names, H):
        entry = {"element": h}
        if not any(h):
            # Zero is in every semigroup and is reducible by nobody; it is
            # also in no minimal generating set. Naming it is an error in the
            # proposal, not a subtlety.
            entry.update({"in_semigroup": True, "irreducible": False,
                          "why": "zero"})
            elements[name] = entry
            trouble.append(name)
            continue
        got = in_semigroup(A, h, u, max_nodes)
        entry["in_semigroup"] = (None if got.get("gave_up")
                                 else got.get("coefficients") is not None)
        entry["coefficients"] = got.get("coefficients")
        if entry["in_semigroup"] is True:
            irr = irreducible_in(A, h, u, max_nodes)
            entry["irreducible"] = irr.get("irreducible")
            if irr.get("irreducible") is False:
                entry["reduces_as"] = {
                    "generator": irr["minus"], "rest": irr["rest"],
                    "rest_coefficients": irr["rest_coefficients"]}
        else:
            entry["irreducible"] = None
        if entry["in_semigroup"] is not True or entry["irreducible"] is not True:
            trouble.append(name)
        elements[name] = entry

    # 3. does H generate S? Every generator must be reachable from H alone.
    #
    # UNREACHABLE AND UNDECIDED ARE NOT THE SAME THING, and the first version
    # of this counted them together: a zero in the proposed set breaks the
    # grading, every search below it gives up, and "could not tell" was
    # reported as "does not generate". That is the substitution this whole
    # module exists to refuse, one level down.
    generates, unreachable, undecided = {}, [], []
    for i, a in enumerate(A):
        got = in_semigroup(H, a, u, max_nodes) if H else {
            "coefficients": None, "exhausted": True}
        if got.get("gave_up"):
            generates[gen_names[i]] = None
            undecided.append(gen_names[i])
            continue
        ok = got.get("coefficients") is not None
        generates[gen_names[i]] = ok
        if not ok:
            unreachable.append(gen_names[i])

    decided = (all(e.get("in_semigroup") is not None
                   and e.get("irreducible") is not None
                   for e in elements.values())
               and not undecided)
    return {
        "decided": decided,
        "elements": elements,
        "generates": None if undecided else not unreachable,
        "unreachable_generators": sorted(unreachable),
        "undecided_generators": sorted(undecided),
        "is_minimal_generating_set": (
            None if not decided else (not trouble and not unreachable)),
        "why_not": sorted(set(trouble) | set(unreachable)),
    }


# --- the whole answer -------------------------------------------------------


def certify(spec, max_nodes=MAX_NODES) -> dict:
    """Every finite question about this semigroup, and what each answer is."""
    gens = generators_of(spec)
    order = list(getattr(spec, "order", None) or sorted(gens))
    unknown = [n for n in order if n not in gens]
    if unknown:
        raise NotASemigroup(_t("semigroup.unknown_generator",
                               names=", ".join(unknown[:3])))
    A = [gens[n] for n in order]
    d = len(A[0])

    u = positive_functional(A)
    graded = u is not None

    # Is any generator redundant? A generator in the semigroup generated by
    # the others is not part of the minimal system, which is the first thing
    # anybody proposing a Hilbert basis needs told.
    redundant = {}
    if graded:
        for i, name in enumerate(order):
            others = [a for j, a in enumerate(A) if j != i]
            if not others:
                continue
            got = in_semigroup(others, A[i], u, max_nodes)
            if got.get("coefficients") is not None:
                names = [n for j, n in enumerate(order) if j != i]
                redundant[name] = {
                    "as": {names[j]: c
                           for j, c in enumerate(got["coefficients"]) if c},
                }

    points = {}
    for name, coords in sorted(dict(getattr(spec, "points", {}) or {}).items()):
        v = _vector(coords, str(name))
        if len(v) != d:
            raise NotASemigroup(_t("semigroup.point_dimension",
                                   name=str(name), got=len(v), want=d))
        cone = in_cone(A, v)
        grp = in_group(A, v)
        sg = in_semigroup(A, v, u, max_nodes) if graded else {
            "coefficients": None, "gave_up": True, "why": "ungraded"}
        entry = {
            "point": v,
            "in_cone": (None if not cone.get("exhausted")
                        else cone.get("coefficients") is not None),
            "cone_coefficients": (None if cone.get("coefficients") is None else
                                  [str(c) for c in cone["coefficients"]]),
            "separating": None,
            "in_group": grp is not None,
            "group_coefficients": grp,
            "in_semigroup": (None if sg.get("gave_up")
                             else sg.get("coefficients") is not None),
            "semigroup_coefficients": sg.get("coefficients"),
            "degree": sg.get("degree"),
            "search_bound": sg.get("bound"),
            "why_unknown": sg.get("why"),
        }
        if entry["in_cone"] is False:
            entry["separating"] = separating(A, v)
        # The three-part refutation of normality, only when all three parts
        # are actually established.
        entry["refutes_normality"] = bool(
            entry["in_cone"] and entry["in_group"]
            and entry["in_semigroup"] is False)
        points[str(name)] = entry

    # A PROPOSED minimal generating set, checked rather than computed. Unlike
    # normality this is DECIDED: for a pointed semigroup the minimal
    # generating set is unique and is the set of irreducibles, so the two
    # inclusions are both finite questions.
    proposed = getattr(spec, "hilbert", None)
    hilbert = None
    if proposed is not None:
        if isinstance(proposed, dict):
            pairs = [(str(n), _vector(v, str(n)))
                     for n, v in sorted(proposed.items())]
        else:
            pairs = [("h{}".format(i), _vector(v, "h{}".format(i)))
                     for i, v in enumerate(proposed)]
        for name, vec in pairs:
            if len(vec) != d:
                raise NotASemigroup(_t("semigroup.point_dimension",
                                       name=name, got=len(vec), want=d))
        hilbert = check_hilbert(A, pairs, u, max_nodes, gen_names=order)

    witnesses = sorted(n for n, e in points.items() if e["refutes_normality"])
    return {
        "hilbert": hilbert,
        "generators": {n: gens[n] for n in order},
        "order": order,
        "dimension": d,
        "rank": _rank(A),
        "lattice": None,
        "pointed": graded,
        "grading": None if u is None else [str(Fraction(x)) for x in u],
        "degrees": (None if u is None else
                    {n: str(dot(u, gens[n])) for n in order}),
        "minimal": (None if not graded else not redundant),
        "redundant": redundant,
        "points": points,
        "not_normal": bool(witnesses),
        "normality_witnesses": witnesses,
        # Said in the payload rather than only in the prose, because a reader
        # of the certificate alone has to know that the absence of a witness
        # is not evidence of normality.
        "normal": None,
        "normal_why": _t("semigroup.normal_not_decided"),
        "title": getattr(spec, "title", ""),
    }
