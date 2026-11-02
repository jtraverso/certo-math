"""A parametric LP is FEASIBLE everywhere on a domain: a family of bases.

One primal `x(p)` rarely serves a whole parameter domain: the optimal basis
changes, and with it the formula. What a user has is a FAMILY -- on each
region a basis B, its solution `w_B(t) = B(t)^-1 d(t)` (rational in t), and
the regions meeting along frontiers where some `w_j` reaches 0. Every session
that reached this point rebuilt the family by hand and checked it outside
certo. This module checks it:

  * each piece's formula, from the basis (Cramer's rule with Bareiss'
    fraction-free elimination: `w = N / D`, one common denominator) or
    given outright as rational functions;
  * `A(t) N(t) = D(t) d(t)` on the tight rows, as a POLYNOMIAL IDENTITY;
  * `D` of one sign on the piece's box (Bernstein, strictly), and with it
    oriented, `N_j >= 0` and every inequality row's slack >= 0 on the
    piece's region (Bernstein, with the region's multipliers);
  * the pieces COVER the domain: they are the leaves of a tree whose nodes
    cut a box at a rational point or cut a region along a frontier `g`,
    one side `g >= 0` and the other `-g >= 0` -- so covering is the tree's
    shape, checked by walking it, and nothing about the frontier has to be
    solved. Points ON a frontier belong to both sides, as they should.

Feasibility is a statement with a witness on every piece; `claim=T` adds the
objective at that witness against T (a lower bound for a maximisation, an
upper bound for a minimisation), piece by piece.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t
from .polynomials import Poly, as_poly, divide, rational_function


class NotAFamily(ValueError):
    """Raised with the reason a family cannot be read or does not cover."""


# --- solving a basis exactly ------------------------------------------------


def _exact_div(f: Poly, g: Poly) -> Poly:
    if not f.terms:
        return f
    (q,), r, _ = divide(f, [g])
    if r.terms:
        raise NotAFamily("internal: a Bareiss division was not exact")
    return q


def bareiss_det(M) -> Poly:
    """The determinant of a square matrix of polynomials, fraction-free:
    every division in Bareiss' recurrence is exact."""
    n = len(M)
    if n == 0:
        raise NotAFamily("an empty basis")
    ring = M[0][0].vars
    A = [list(row) for row in M]
    sign, prev = 1, Poly.const(ring, 1)
    for k in range(n - 1):
        if not A[k][k].terms:
            swap = next((i for i in range(k + 1, n) if A[i][k].terms), None)
            if swap is None:
                return Poly(ring)
            A[k], A[swap] = A[swap], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = _exact_div(A[i][j] * A[k][k] - A[i][k] * A[k][j], prev)
        prev = A[k][k]
    d = A[n - 1][n - 1]
    return d if sign == 1 else d.scaled(-1)


def basis_solution(ring, rows, basis, P):
    """`(D, {var: N})` for a basis: the tight rows (every `==` row and every
    inequality row not named in `basis`) solved for the basic variables, the
    rest at zero. A row named in `basis` has its slack basic."""
    basic = [b for b in basis if b not in {r[0] for r in rows}]
    tight = [r for r in rows if r[2] == "==" or r[0] not in basis]
    if len(tight) != len(basic):
        raise NotAFamily(t("pfamily.basis_square", rows=len(tight), cols=len(basic)))
    A = [[P(row.get(v, 0)) for v in basic] for _n, row, _s, _rhs in tight]
    b = [P(rhs) for _n, _row, _s, rhs in tight]
    D = bareiss_det(A)
    if not D.terms:
        raise NotAFamily(t("pfamily.singular", basis=", ".join(map(str, basis))))
    N = {}
    for j, v in enumerate(basic):
        Aj = [row[:j] + [b[i]] + row[j + 1:] for i, row in enumerate(A)]
        N[v] = bareiss_det(Aj)
    return D, N


def primal_solution(ring, primal):
    """`(D, {var: N})` from formulas: rational functions over one common
    denominator (the product of the distinct ones)."""
    parts = {}
    for v, e in primal.items():
        if isinstance(e, (Poly, int, Fraction)):
            parts[v] = (as_poly(ring, e), Poly.const(ring, 1))
        elif isinstance(e, tuple) and len(e) == 2:
            parts[v] = (as_poly(ring, e[0]), as_poly(ring, e[1]))
        else:
            parts[v] = rational_function(e, ring)
    dens = []
    for _n, d in parts.values():
        if d.degree > 0 and all(d != x for x in dens):
            dens.append(d)
    D = Poly.const(ring, 1)
    for d in dens:
        D = D * d
    N = {}
    for v, (n, d) in parts.items():
        if d.degree == 0:
            c = next(iter(d.terms.values()))
            N[v] = (n * D).scaled(1 / Fraction(c))
        else:
            rest = Poly.const(ring, 1)
            for x in dens:
                if x != d:
                    rest = rest * x
            N[v] = n * rest
    return D, N


# --- the cover -----------------------------------------------------------------


def _normal(g: Poly):
    """`(key, sign)`: g up to a POSITIVE factor, and the sign that relates it
    to its normal form -- so g and -g share a key with opposite signs."""
    if not g.terms:
        raise NotAFamily("a frontier condition is zero")
    _e, c = g.lead()
    h = g.scaled(1 / abs(Fraction(c)))
    key = repr(sorted((tuple(e), str(v)) for e, v in h.terms.items()))
    neg = repr(sorted((tuple(e), str(-v)) for e, v in h.terms.items()))
    return (key, 1, h) if key <= neg else (neg, -1, h.scaled(-1))


def cover_tree(box, pieces):
    """The pieces as leaves of a tree of box cuts and frontier cuts.

    `pieces`: `[(box, [frontier polys])]`. The boxes must tile `box`
    (`bernstein.forest_tree`); the pieces sharing a box must be split by
    frontiers, each one appearing as `g` in some and `-g` in the others."""
    from . import bernstein

    groups = {}
    for i, (b, conds) in enumerate(pieces):
        key = tuple(sorted((n, lo, hi) for n, (lo, hi) in b.items()))
        groups.setdefault(key, (b, []))[1].append((i, conds))
    try:
        boxes = bernstein.forest_tree(box, [(b, ("group", key))
                                            for key, (b, _items) in groups.items()])
    except bernstein.NotAWitness as e:
        raise NotAFamily(str(e)) from None

    def split(items):
        if len(items) == 1 and not items[0][1]:
            return {"piece": items[0][0]}
        if len(items) == 1:
            raise NotAFamily(t("pfamily.uncovered", i=items[0][0]))
        normals = [{k: s for k, s, _h in (_normal(g) for g in conds)}
                   for _i, conds in items]
        common = set(normals[0])
        for nm in normals[1:]:
            common &= set(nm)
        for key in sorted(common):
            pos = [it for it, nm in zip(items, normals) if nm[key] == 1]
            neg = [it for it, nm in zip(items, normals) if nm[key] == -1]
            if not pos or not neg:
                continue
            h = next(hh for kk, _s, hh in (_normal(g) for g in items[0][1])
                     if kk == key)

            def strip(it):
                return (it[0], [g for g in it[1] if _normal(g)[0] != key])

            return {"frontier": h.serialize(),
                    "pos": split([strip(it) for it in pos]),
                    "neg": split([strip(it) for it in neg])}
        raise NotAFamily(t("pfamily.no_frontier",
                           pieces=", ".join(str(i) for i, _c in items)))

    def walk(node):
        if isinstance(node, list):
            return [node[0], walk(node[1]), walk(node[2])] + list(node[3:])
        if isinstance(node, tuple) and node[0] == "group":
            return split(groups[node[1]][1])
        raise NotAFamily("internal: an unexpected cover node")

    return walk(boxes)


def leaves(box, cover, ring, max_depth=64):
    """`[(piece index, box, [(name, frontier poly)])]` -- what the cover says
    each piece must hold on. Raises on a malformed tree."""
    from . import bernstein

    out = []

    def rec(node, b, fr, depth):
        if depth > max_depth:
            raise NotAFamily("the cover is deeper than {}".format(max_depth))
        if isinstance(node, list) and len(node) in (3, 4):
            name = node[0]
            if name not in b:
                raise NotAFamily("a cut on an unknown parameter: {}".format(name))
            at = None
            if len(node) == 4:
                at = Fraction(node[3])
                if not b[name][0] < at < b[name][1]:
                    raise NotAFamily("a cut outside its interval: {}".format(at))
            left, right = bernstein.halves(b, name, at)
            rec(node[1], left, fr, depth + 1)
            rec(node[2], right, fr, depth + 1)
        elif isinstance(node, dict) and "frontier" in node:
            g = Poly.parse(ring, node["frontier"])
            if not g.terms:
                raise NotAFamily("a frontier condition is zero")
            n = "frontier_{}".format(len(fr))
            rec(node["pos"], b, fr + [(n, g)], depth + 1)
            rec(node["neg"], b, fr + [(n, g.scaled(-1))], depth + 1)
        elif isinstance(node, dict) and isinstance(node.get("piece"), int):
            out.append((node["piece"], b, fr))
        else:
            raise NotAFamily("a malformed cover node")

    rec(cover, dict(box), [], 0)
    return out


# --- one piece -------------------------------------------------------------------


def piece_polys(rows, objective, free, D, N, P, sense, claim):
    """What must be >= 0 on the piece (`{label: poly}`, before orientation),
    and the rows that must vanish identically (`{name: poly}`)."""
    ring = D.vars
    zero = Poly(ring)
    want, ident = {}, {}
    for v, n in sorted(N.items()):
        if v not in free:
            want["var:" + v] = n
    for name, row, sense_r, rhs in rows:
        lhs = zero
        for v, coef in row.items():
            if v in N and N[v].terms:
                lhs = lhs + P(coef) * N[v]
        rest = P(rhs) * D
        if sense_r == "==":
            ident[str(name)] = lhs - rest
        elif sense_r == "<=":
            want["row:" + str(name)] = rest - lhs
        else:
            want["row:" + str(name)] = lhs - rest
    if claim is not None:
        val = zero
        for v, c in objective.items():
            if v in N and N[v].terms:
                val = val + P(c) * N[v]
        T = P(claim) * D
        # A feasible point bounds a max from below and a min from above.
        want["claim"] = (val - T) if sense == "max" else (T - val)
    return want, ident


# --- the whole family: built, and checked again ------------------------------


def _rows_of(spec):
    return [(str(n), {str(v): c for v, c in row.items()}, sense, rhs)
            for n, row, sense, rhs in spec.constraints]


def certify_family(spec) -> dict:
    """Build every piece and its checks. Returns what a certificate carries,
    with `ok` and, when not ok, `failed`: [(piece, label, diagnosis)]."""
    from . import bernstein
    from .parametric import _box_of

    ring = tuple(spec.parameters)

    def P(x):
        return as_poly(ring, x)

    box = _box_of(spec, ring)
    if box is None:
        raise NotAFamily(t("pfamily.needs_box"))
    depth = int(getattr(spec, "subdivide", 0) or 0)
    sense = getattr(spec, "sense", "max")
    free = {str(v) for v in (getattr(spec, "free", None) or [])}
    rows = _rows_of(spec)
    names = {r[0] for r in rows}
    variables = sorted({v for _n, row, _s, _r in rows for v in row}
                       | {str(v) for v in spec.objective})
    domain = [(str(n), P(g)) for n, g in (getattr(spec, "region", None) or [])]
    dom_keys = {_normal(g)[0] for _n, g in domain}
    claim = getattr(spec, "claim", None)
    objective = {str(v): c for v, c in spec.objective.items()}

    raw = []
    for i, pc in enumerate(spec.pieces):
        if not isinstance(pc, dict):
            raise NotAFamily(t("pfamily.piece_shape", i=i))
        try:
            pb = bernstein.parse_box(pc.get("box") or dict(spec.box), ring)
        except bernstein.NotABox as e:
            raise NotAFamily(str(e)) from None
        conds = [P(g) for _n, g in (pc.get("region") or [])]
        conds = [g for g in conds if _normal(g)[0] not in dom_keys]
        if pc.get("basis") is not None:
            basis = [str(b) for b in pc["basis"]]
            unknown = [b for b in basis if b not in variables and b not in names]
            if unknown:
                raise NotAFamily(t("pfamily.basis_unknown", i=i,
                                   names=", ".join(unknown[:4])))
            D, N = basis_solution(ring, rows, basis, P)
        elif pc.get("primal") is not None:
            basis = None
            D, N = primal_solution(ring, {str(v): e for v, e in pc["primal"].items()})
            stray = [v for v in N if v not in variables]
            if stray:
                raise NotAFamily(t("pfamily.basis_unknown", i=i,
                                   names=", ".join(stray[:4])))
        else:
            raise NotAFamily(t("pfamily.piece_shape", i=i))
        raw.append({"box": pb, "conds": conds, "basis": basis, "D": D, "N": N})

    cover = cover_tree(box, [(r["box"], r["conds"]) for r in raw])
    pieces, failed = [None] * len(raw), []
    for i, b, fr in leaves(box, cover, ring):
        r = raw[i]
        conds = domain + fr
        terms = bernstein.region_terms(conds) if conds else []
        D, N = r["D"], r["N"]
        o, (okd, dtree) = 1, bernstein.positive(D, b, depth)
        if not okd:
            o, (okd, dtree) = -1, bernstein.positive(D.scaled(-1), b, depth)
        entry = {"box": {n: [str(lo), str(hi)] for n, (lo, hi) in b.items()},
                 "basis": r["basis"], "denominator": D.serialize(),
                 "orientation": o, "denominator_tree": dtree,
                 "numerators": {v: n.serialize() for v, n in sorted(N.items())},
                 "trees": {}}
        pieces[i] = entry
        if not okd:
            failed.append((i, "denominator", None))
            continue
        want, ident = piece_polys(rows, objective, free, D, N, P, sense, claim)
        for name, poly in ident.items():
            if poly.terms:
                failed.append((i, "row:" + name, None))
        for label, poly in want.items():
            q = poly.scaled(o)
            ok, tree = (bernstein.nonneg_region(q, b, terms, depth)
                        if terms else bernstein.nonneg(q, b, depth))
            if ok:
                if tree is not None:
                    entry["trees"][label] = tree
            else:
                failed.append((i, label, bernstein.diagnose(q, b)))
    return {"ok": not failed, "failed": failed, "cover": cover, "pieces": pieces,
            "box": {n: [str(lo), str(hi)] for n, (lo, hi) in box.items()},
            "variables": variables, "sense": sense, "free": sorted(free),
            "region": {n: g.serialize() for n, g in domain},
            "claim": None if claim is None else P(claim).serialize(),
            "constraints": [[n, {v: P(c).serialize() for v, c in row.items()},
                             s, P(rhs).serialize()] for n, row, s, rhs in rows],
            "objective": {v: P(c).serialize() for v, c in objective.items()}}


def check_family(p, max_depth=64) -> list:
    """Re-derive a `parametric_family` certificate: `[(check, ok, detail)]`.
    Nothing it carries is believed: the formulas are re-multiplied, every
    sign re-derived from the tree shapes, and the cover walked."""
    from . import bernstein

    ring = tuple(p["parameters"])

    def P(x):
        return Poly.parse(ring, x)

    checks = []
    box = {n: (Fraction(lo), Fraction(hi)) for n, (lo, hi) in p["box"].items()}
    if set(box) != set(ring) or any(not lo < hi for lo, hi in box.values()):
        return [(t("verify.pfamily.box"), False, str(p["box"]))]
    rows = [(str(r[0]), dict(r[1]), r[2], r[3]) for r in p["constraints"]]
    if any(s not in ("<=", ">=", "==") for _n, _r, s, _h in rows) or \
            p.get("sense") not in ("max", "min"):
        return [(t("verify.pfamily.rows"), False, "sense")]
    objective = dict(p["objective"])
    free = set(p.get("free") or [])
    variables = {v for _n, row, _s, _r in rows for v in row} | set(objective)
    domain = [(str(n), P(g)) for n, g in sorted((p.get("region") or {}).items())]
    claim = p.get("claim")
    try:
        lv = leaves(box, p["cover"], ring, max_depth)
    except (NotAFamily, KeyError, TypeError, ValueError, ZeroDivisionError) as e:
        return [(t("verify.pfamily.cover"), False, str(e)[:160])]
    used = sorted(i for i, _b, _f in lv)
    pieces = p["pieces"]
    checks.append((t("verify.pfamily.cover"),
                   used == list(range(len(pieces))),
                   t("verify.pfamily.cover_detail", leaves=len(lv),
                     pieces=len(pieces))))
    for i, b, fr in lv:
        if not 0 <= i < len(pieces):
            continue
        pc = pieces[i]
        label = t("verify.pfamily.piece", i=i)
        try:
            pb = {n: (Fraction(lo), Fraction(hi)) for n, (lo, hi) in pc["box"].items()}
            D = P(pc["denominator"])
            N = {v: P(x) for v, x in pc["numerators"].items()}
            o = pc["orientation"]
            if o not in (1, -1) or pb != b or set(N) - variables:
                checks.append((label, False, t("verify.pfamily.piece_shape")))
                continue
            if not bernstein.check_positive(D.scaled(o), b, pc.get("denominator_tree")):
                checks.append((label, False, t("verify.pfamily.denominator")))
                continue
            want, ident = piece_polys(rows, objective, free, D, N, P,
                                      p["sense"], claim)
            bad = ["row:" + n for n, poly in ident.items() if poly.terms]
            basis = pc.get("basis")
            if basis is not None:
                # THE BASIS IS A CLAIM: every name once, a column or a row;
                # a column outside it is zero, a row outside it is tight.
                rnames = {r[0] for r in rows}
                if (len(set(basis)) != len(basis)
                        or any(b not in variables and b not in rnames for b in basis)
                        or any(N[v].terms for v in N if v not in basis)):
                    bad.append("basis")
                else:
                    bad += ["tight:" + lbl[4:] for lbl, poly in want.items()
                            if lbl.startswith("row:") and lbl[4:] not in basis
                            and poly.terms]
            conds = domain + fr
            terms = dict(bernstein.region_terms(conds)) if conds else None
            trees = pc.get("trees") or {}
            bad += [lbl for lbl, poly in want.items()
                    if not bernstein.check(poly.scaled(o), b, trees.get(lbl),
                                           max_depth, terms)]
            checks.append((label, not bad, ", ".join(bad[:4]) or
                           t("verify.pfamily.piece_ok", vars=len(N),
                             frontiers=len(fr))))
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as e:
            checks.append((label, False, "{}: {}".format(type(e).__name__, e)[:160]))
    return checks
