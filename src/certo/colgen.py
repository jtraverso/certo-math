"""An LP over EVERY clique of a graph, without listing them: column
generation with a certified pricing oracle.

    packing     max  sum_Q w(Q) x_Q   s.t.  sum_{Q containing e} x_Q <= r_e
    cover       min  sum_Q w(Q) x_Q   s.t.  sum_{Q containing e} x_Q >= r_e
    partition   min  sum_Q w(Q) x_Q   s.t.  sum_{Q containing e} x_Q  = r_e

over x >= 0, one column per clique Q with |Q| >= min_size, one row per edge e,
and a weight linear in the clique's counts:

    w(Q) = alpha |E(Q)| + beta |Q| + gamma

`alpha = 1, gamma = -1` on the packing is "edges covered, minus one per
clique"; `gamma = 1` on the partition counts cliques, and is the fractional
clique partition number of the edges.

WHY IT NEEDS A CERTIFICATE OF ITS OWN. `opt` certifies an LP whose columns it
was given. Here the columns are implicit -- a graph on thirty vertices can have
thousands of cliques, a denser one millions -- and the LP that gets solved has
only the few that were generated. What makes its optimum the optimum of the
whole program is a statement about every column that was NOT generated:

    reduced(Q) = c_Q - sum_{e in Q} z_e  <=  0     for every clique Q

with `c_Q = w(Q)` for a maximisation and `-w(Q)` for a minimisation, and `z`
the exact dual of the edge rows. With that, weak duality closes it: for any
feasible x,

    sum_Q c_Q x_Q  <=  sum_Q x_Q sum_{e in Q} z_e  =  sum_e z_e load_e  <=  sum_e z_e r_e

-- the last step using the sign of each `z_e` against the sense of its row --
and the right-hand side is attained by the generated solution.

THE ORACLE, AND WHY IT IS A CHECK AND NOT A CLAIM. "No clique has positive
reduced cost" is decided by an exact search over the cliques, in a fixed order,
pruned by a bound that is valid for every extension of a partial clique:

    reduced(R + S)  <=  reduced(R) + sum_{v in P} max(0, gain_R(v))
                                   + sum_{v<w in P, vw an edge} max(0, p_vw)

where `P` is the candidates that extend `R`, `p_uv = sgn alpha - z_uv` is what
an edge contributes, and `gain_R(v)` what adding `v` contributes on top of
`R`. A pruned subtree provably holds no clique above the threshold, so the
search is complete. The verifier runs the same search, with the certificate's
`z`, and gets the same answer or rejects -- there is no oracle to trust, only
one to rerun. On a chordal graph the cliques number at most `2^w n` for
clique number `w`, and in practice the bound prunes most of that.

BOUNDED SIZE. `max_size` limits the family from above -- only edges and
triangles, say -- and the pricing search simply stops growing a clique at
that size. The bound stays valid: it is over every extension, and dropping
extensions only lowers the maximum.

INFEASIBLE, WITH A CERTIFICATE. A `partition` whose smallest clique has three
vertices need not be feasible at all. Phase one decides it with the same
machinery: an artificial column per edge, cost 1, every clique cost 0, and
columns generated until none prices in. If that optimum is positive, its dual
`y` has `sum_{e in Q} y_e <= 0` for EVERY allowed clique -- the pricing search
says so, over the whole family -- and `r.y > 0`, which is Farkas's lemma: no
`x >= 0` partitions the edges. The verifier reruns the search with that `y`.
When the optimum is zero, the columns phase one generated start the real
program, which is then feasible.

A `cover` edge that lies in no allowed clique makes the program infeasible,
and that is reported with the edge.
"""
from __future__ import annotations

from fractions import Fraction

from .i18n import t as _t

#: Nodes the pricing search may open before it gives up. Exceeding it is
#: reported, never rounded to "no violated column".
MAX_NODES = 5_000_000

PROBLEMS = {"packing": ("max", "<="), "cover": ("min", ">="),
            "partition": ("min", "==")}


class NotACliqueLP(ValueError):
    """The input is not a clique LP this can read."""


class PricingBudget(Exception):
    """The pricing search ran out of nodes; nothing was established."""


# --- the graph ---------------------------------------------------------------


class Graph:
    """Vertices in a fixed order, edges as index pairs, adjacency as sets.

    The order is the one the search runs in, so it is part of what makes the
    producer's search and the verifier's the same search.
    """

    def __init__(self, vertices, edges):
        self.labels = [str(v) for v in vertices]
        if len(set(self.labels)) != len(self.labels):
            raise NotACliqueLP(_t("colgen.duplicate_vertex"))
        index = {v: i for i, v in enumerate(self.labels)}
        self.adj = [set() for _ in self.labels]
        self.edges = []
        seen = set()
        for e in edges:
            try:
                u, v = e
            except (TypeError, ValueError):
                raise NotACliqueLP(_t("colgen.bad_edge", edge=e)) from None
            u, v = str(u), str(v)
            if u not in index or v not in index:
                raise NotACliqueLP(_t("colgen.unknown_vertex", edge=e))
            i, j = sorted((index[u], index[v]))
            if i == j:
                raise NotACliqueLP(_t("colgen.loop", edge=e))
            if (i, j) in seen:
                continue
            seen.add((i, j))
            self.edges.append((i, j))
            self.adj[i].add(j)
            self.adj[j].add(i)
        self.edges.sort()
        self.edge_index = {e: k for k, e in enumerate(self.edges)}

    def name(self, k) -> str:
        i, j = self.edges[k]
        return "{}-{}".format(self.labels[i], self.labels[j])

    def is_clique(self, Q) -> bool:
        return all(b in self.adj[a] for x, a in enumerate(Q) for b in Q[x + 1:])

    def clique_edges(self, Q):
        Q = sorted(Q)
        return [self.edge_index[(a, b)] for x, a in enumerate(Q)
                for b in Q[x + 1:]]


def graph_of(spec) -> Graph:
    edges = list(getattr(spec, "edges", None) or [])
    vertices = getattr(spec, "vertices", None)
    if vertices is None:
        seen = []
        for e in edges:
            for v in e:
                if str(v) not in seen:
                    seen.append(str(v))
        vertices = sorted(seen, key=_natural)
    return Graph(vertices, edges)


def _natural(s):
    """Integers as integers: `10` after `9`, as a person reads them."""
    try:
        return (0, int(s), "")
    except ValueError:
        return (1, 0, s)


def maximal_cliques(g: Graph, max_nodes=MAX_NODES):
    """Bron-Kerbosch with pivoting; each clique a sorted list of indices."""
    out, nodes = [], [0]

    def rec(R, P, X):
        nodes[0] += 1
        if nodes[0] > max_nodes:
            raise PricingBudget("maximal cliques")
        if not P and not X:
            out.append(sorted(R))
            return
        pivot = max(P | X, key=lambda u: len(g.adj[u] & P))
        for v in sorted(P - g.adj[pivot]):
            rec(R | {v}, P & g.adj[v], X & g.adj[v])
            P = P - {v}
            X = X | {v}

    rec(set(), set(range(len(g.labels))), set())
    return sorted(out)


# --- weights and the pricing search -------------------------------------------


def weight(Q, g: Graph, alpha, beta, gamma) -> Fraction:
    k = len(Q)
    return alpha * (k * (k - 1) // 2) + beta * k + gamma


def price(g: Graph, z, sgn, alpha, beta, gamma, min_size, threshold=0,
          collect=0, max_nodes=MAX_NODES, max_size=None) -> dict:
    """The largest reduced cost over every clique of size >= `min_size`.

    `z` is the exact dual, one entry per edge in `g.edges` order. Returns
    `{"best": value or None, "argmax": clique or None, "nodes": n,
    "found": [(value, clique), ...]}` where `found` holds up to `collect`
    cliques with reduced cost above `threshold`, the largest first.

    Subtrees whose bound is at most `threshold` are pruned, so `best` is exact
    whenever it is above `threshold`, and "nothing above it" is exact always.
    Deterministic: vertices in index order, candidates in index order.
    """
    n = len(g.labels)
    p = {}
    for k, (i, j) in enumerate(g.edges):
        w = sgn * alpha - z[k]
        p[(i, j)] = p[(j, i)] = w
    q = sgn * beta
    const = sgn * gamma
    best = [None, None]
    found = []
    nodes = [0]

    def consider(value, R):
        if best[0] is None or value > best[0]:
            best[0], best[1] = value, list(R)
        if collect and value > threshold:
            found.append((value, list(R)))

    # R grows by adding candidates with a larger index than any in R, so each
    # clique is visited exactly once.
    def rec(R, value, P, gain):
        nodes[0] += 1
        if nodes[0] > max_nodes:
            raise PricingBudget("pricing")
        if len(R) >= min_size:
            consider(value, R)
        if not P or (max_size is not None and len(R) >= max_size):
            return
        bound = value + sum(max(Fraction(0), gain[v]) for v in P)
        for a_i, a in enumerate(P):
            for b in P[a_i + 1:]:
                if b in g.adj[a]:
                    w = p[(a, b)]
                    if w > 0:
                        bound += w
        if bound <= threshold:
            return
        for idx, v in enumerate(P):
            rest = [u for u in P[idx + 1:] if u in g.adj[v]]
            new_gain = {u: gain[u] + p[(u, v)] for u in rest}
            rec(R + [v], value + gain[v], rest, new_gain)

    start = list(range(n))
    rec([], const, start, {v: q for v in start})
    found.sort(key=lambda x: (-x[0], x[1]))
    return {"best": best[0], "argmax": best[1], "nodes": nodes[0],
            "found": found[:collect] if collect else []}


# --- the generation loop -------------------------------------------------------


def _params(spec):
    problem = getattr(spec, "problem", "packing")
    if problem not in PROBLEMS:
        raise NotACliqueLP(_t("colgen.bad_problem", got=problem,
                              want=", ".join(PROBLEMS)))
    w = dict(getattr(spec, "weight", None) or {"constant": 1})
    unknown = set(w) - {"edges", "vertices", "constant"}
    if unknown:
        raise NotACliqueLP(_t("colgen.bad_weight", got=", ".join(sorted(unknown))))
    alpha = Fraction(w.get("edges", 0))
    beta = Fraction(w.get("vertices", 0))
    gamma = Fraction(w.get("constant", 0))
    m = int(getattr(spec, "min_size", 2))
    if m < 1:
        raise NotACliqueLP(_t("colgen.bad_min_size", got=m))
    M = getattr(spec, "max_size", None)
    if M is not None:
        M = int(M)
        if M < max(m, 2):
            raise NotACliqueLP(_t("colgen.bad_max_size", got=M, min=max(m, 2)))
    return problem, alpha, beta, gamma, m, M


def _starting(g, m, M):
    """Every maximal clique large enough; one too large is cut down to a
    clique of `M` vertices around each of its edges, so every edge an allowed
    clique can cover is covered by a starting column."""
    out = set()
    for Q in maximal_cliques(g):
        if len(Q) < m:
            continue
        if M is None or len(Q) <= M:
            out.add(tuple(Q))
            continue
        for a, b in ((a, b) for x, a in enumerate(Q) for b in Q[x + 1:]):
            rest = [v for v in Q if v not in (a, b)][:M - 2]
            out.add(tuple(sorted([a, b] + rest)))
    return [list(Q) for Q in sorted(out)]


def rhs_of(spec, g: Graph):
    raw = getattr(spec, "rhs", 1)
    if isinstance(raw, dict):
        out = []
        for k in range(len(g.edges)):
            i, j = g.edges[k]
            a, b = g.labels[i], g.labels[j]
            v = raw.get("{}-{}".format(a, b), raw.get("{}-{}".format(b, a), 1))
            out.append(Fraction(v))
        return out
    return [Fraction(raw)] * len(g.edges)


def solve(spec, limits=None, max_rounds=500, per_round=40) -> dict:
    """Generate columns until the pricing search finds none; return the
    whole certificate content, or raise."""
    from .engines import lp as lp_engine
    from .limits import Limits
    from .spec import LPSpec

    lim = limits or Limits()
    g = graph_of(spec)
    problem, alpha, beta, gamma, m, M = _params(spec)
    sense, row_sense = PROBLEMS[problem]
    sgn = 1 if sense == "max" else -1
    rhs = rhs_of(spec, g)
    if any(r < 0 for r in rhs):
        raise NotACliqueLP(_t("colgen.negative_rhs"))

    # Starting columns: every maximal clique that is large enough, and for a
    # partition every edge as well when edges are allowed -- which is what
    # makes it feasible. When they are not, phase one decides feasibility.
    cols = _starting(g, m, M)
    if problem == "partition" and m <= 2:
        cols += [[i, j] for (i, j) in g.edges]
    if problem == "partition" and m > 2:
        phase = _phase_one(g, cols, rhs, m, M, lim, max_rounds, per_round)
        if "farkas" in phase:
            return dict(phase, graph=g, problem=problem, alpha=alpha,
                        beta=beta, gamma=gamma, min_size=m, max_size=M,
                        rhs=rhs)
        cols = phase["cols"]
    if problem == "cover":
        covered = {k for Q in cols for k in g.clique_edges(Q)}
        missing = [k for k in range(len(g.edges))
                   if k not in covered and rhs[k] > 0]
        if missing:
            return {"infeasible_edge": g.name(missing[0])}
    seen = {tuple(Q) for Q in cols}
    cols = [list(Q) for Q in sorted(seen)]

    rounds = 0
    while True:
        rounds += 1
        z, x, objective = _master(g, cols, rhs, row_sense, sense, alpha, beta,
                                  gamma, lim, lp_engine, LPSpec)
        got = price(g, z, sgn, alpha, beta, gamma, m, threshold=0,
                    collect=per_round, max_size=M)
        new = [Q for _v, Q in got["found"] if tuple(Q) not in seen]
        if not new:
            break
        if rounds >= max_rounds:
            raise PricingBudget("rounds")
        for Q in new:
            seen.add(tuple(Q))
            cols.append(Q)

    support = [(Q, x[k]) for k, Q in enumerate(cols) if x[k] != 0]
    return {"graph": g, "problem": problem, "alpha": alpha, "beta": beta,
            "gamma": gamma, "min_size": m, "max_size": M, "rhs": rhs, "z": z,
            "support": support, "objective": objective,
            "pricing": got, "rounds": rounds, "generated": len(cols)}


def _phase_one(g, cols, rhs, m, M, lim, max_rounds, per_round) -> dict:
    """Is the partition feasible at all? `min sum a_e` with an artificial
    column per edge, every clique free, columns generated as in phase two.
    Returns `{"cols": [...]}` when the optimum is zero, or the Farkas vector
    `y = -z` and its pricing when it is not."""
    from .engines import lp as lp_engine
    from .spec import LPSpec

    seen = {tuple(Q) for Q in cols}
    cols = [list(Q) for Q in sorted(seen)]
    rounds = 0
    while True:
        rounds += 1
        s = LPSpec(sense="min", title="phase one")
        names = ["q{}".format(k) for k in range(len(cols))]
        for v in names:
            s.variable(v)
        for e in range(len(g.edges)):
            s.variable("a{}".format(e))
        s.objective({"a{}".format(e): 1 for e in range(len(g.edges))})
        rows = [{"a{}".format(e): 1} for e in range(len(g.edges))]
        for k, Q in enumerate(cols):
            for e in g.clique_edges(Q):
                rows[e][names[k]] = 1
        for e in range(len(g.edges)):
            s.constraint(rows[e], "==", rhs[e], name="e{}".format(e))
        res = lp_engine.opt(s, lim)
        cert = res.certificate
        if cert is None or not res.meta.get("exact"):
            raise ArithmeticError(_t("colgen.master_inexact",
                                     detail=res.detail or res.status.value))
        p = cert.payload
        y = dict(zip(p["names"], (Fraction(v) for v in p["dual"])))
        z = [y.get("e{}_le".format(e), Fraction(0))
             - y.get("e{}_ge".format(e), Fraction(0))
             for e in range(len(g.edges))]
        value = Fraction(res.meta["objective"])
        got = price(g, z, -1, Fraction(0), Fraction(0), Fraction(0), m,
                    threshold=0, collect=per_round, max_size=M)
        new = [Q for _v, Q in got["found"] if tuple(Q) not in seen]
        if not new:
            break
        if rounds >= max_rounds:
            raise PricingBudget("rounds")
        for Q in new:
            seen.add(tuple(Q))
            cols.append(Q)
    if value == 0:
        return {"cols": cols}
    return {"farkas": [-v for v in z], "farkas_value": value, "pricing": got,
            "rounds": rounds, "generated": len(cols)}


def _master(g, cols, rhs, row_sense, sense, alpha, beta, gamma, lim,
            lp_engine, LPSpec):
    """The restricted LP, solved and certified exactly by `opt`; its dual read
    back per EDGE, with the sign convention of the internal maximisation."""
    s = LPSpec(sense=sense, title="restricted master")
    names = ["q{}".format(k) for k in range(len(cols))]
    for v in names:
        s.variable(v)
    s.objective({names[k]: weight(Q, g, alpha, beta, gamma)
                 for k, Q in enumerate(cols)})
    rows = [dict() for _ in g.edges]
    for k, Q in enumerate(cols):
        for e in g.clique_edges(Q):
            rows[e][names[k]] = 1
    for e in range(len(g.edges)):
        s.constraint(rows[e], row_sense, rhs[e], name="e{}".format(e))
    res = lp_engine.opt(s, lim)
    cert = res.certificate
    if cert is None or not res.meta.get("exact"):
        raise ArithmeticError(_t("colgen.master_inexact",
                                 detail=res.detail or res.status.value))
    p = cert.payload
    y = dict(zip(p["names"], (Fraction(v) for v in p["dual"])))
    z = []
    for e in range(len(g.edges)):
        name = "e{}".format(e)
        if row_sense == "<=":
            z.append(y.get(name, Fraction(0)))
        elif row_sense == ">=":
            z.append(-y.get(name + "_geq", Fraction(0)))
        else:
            z.append(y.get(name + "_le", Fraction(0))
                     - y.get(name + "_ge", Fraction(0)))
    x = [Fraction(v) for v in p["primal"]]
    objective = sum((weight(Q, g, alpha, beta, gamma) * x[k]
                     for k, Q in enumerate(cols)), Fraction(0))
    return z, x, objective


# --- the check, shared with the verifier -------------------------------------


def check_farkas(payload, max_nodes=MAX_NODES) -> list:
    """An infeasible partition's certificate, recomputed: `r.y > 0`, and --
    by the pricing search over EVERY allowed clique -- no clique has
    `sum_{e in Q} y_e > 0`. Together, Farkas: no `x >= 0` partitions."""
    out = []
    g = Graph(payload["vertices"], payload["edges"])
    m = int(payload["min_size"])
    M = payload.get("max_size")
    M = None if M is None else int(M)
    rhs = [Fraction(v) for v in payload["rhs"]]
    y = [Fraction(v) for v in payload["farkas"]]
    shaped = len(rhs) == len(y) == len(g.edges) and \
        payload.get("problem") == "partition"
    out.append(("shape", shaped, len(g.edges)))
    if not shaped:
        return out
    value = sum((r * v for r, v in zip(rhs, y)), Fraction(0))
    out.append(("farkas_value", value > 0 and
                value == Fraction(payload["farkas_value"]), str(value)))
    try:
        got = price(g, [-v for v in y], 1, Fraction(0), Fraction(0),
                    Fraction(0), m, threshold=0, max_nodes=max_nodes,
                    max_size=M)
    except PricingBudget:
        out.append(("farkas_pricing", False, "budget"))
        return out
    best = got["best"]
    claimed = payload.get("pricing") or {}
    same = (claimed.get("max_reduced") == (None if best is None else str(best))
            and claimed.get("nodes") == got["nodes"])
    out.append(("farkas_pricing", (best is None or best <= 0) and same,
                "{} ({} nodes)".format("-" if best is None else best,
                                       got["nodes"])))
    return out


def check(payload, max_nodes=MAX_NODES) -> list:
    """Every claim in a `clique_lp` payload, recomputed. `(label, ok, detail)`."""
    if "farkas" in payload:
        return check_farkas(payload, max_nodes)
    out = []
    g = Graph(payload["vertices"], payload["edges"])
    problem = payload["problem"]
    sense, row_sense = PROBLEMS[problem]
    sgn = 1 if sense == "max" else -1
    w = payload["weight"]
    alpha, beta, gamma = (Fraction(w["edges"]), Fraction(w["vertices"]),
                          Fraction(w["constant"]))
    m = int(payload["min_size"])
    M = payload.get("max_size")
    M = None if M is None else int(M)
    rhs = [Fraction(v) for v in payload["rhs"]]
    z = [Fraction(v) for v in payload["dual"]]
    shaped = len(rhs) == len(z) == len(g.edges)
    out.append(("shape", shaped, len(g.edges)))
    if not shaped:
        return out

    index = {v: i for i, v in enumerate(g.labels)}
    load = [Fraction(0)] * len(g.edges)
    value = Fraction(0)
    bad_cols = []
    for col in payload["columns"]:
        try:
            Q = sorted(index[str(v)] for v in col["clique"])
            xq = Fraction(col["x"])
        except (KeyError, TypeError, ValueError, ZeroDivisionError):
            bad_cols.append(str(col.get("clique")))
            continue
        if (len(set(Q)) != len(Q) or len(Q) < m or not g.is_clique(Q)
                or xq < 0 or (M is not None and len(Q) > M)):
            bad_cols.append(str(col["clique"]))
            continue
        for e in g.clique_edges(Q):
            load[e] += xq
        value += weight(Q, g, alpha, beta, gamma) * xq
    out.append(("columns", not bad_cols, ", ".join(bad_cols[:3]) or "-"))

    def fits(e):
        if row_sense == "<=":
            return load[e] <= rhs[e]
        if row_sense == ">=":
            return load[e] >= rhs[e]
        return load[e] == rhs[e]

    over = [g.name(e) for e in range(len(g.edges)) if not fits(e)]
    out.append(("primal", not over, ", ".join(over[:3]) or "-"))
    out.append(("objective", value == Fraction(payload["objective"]),
                str(value)))

    def signed(e):
        if row_sense == "<=":
            return z[e] >= 0
        if row_sense == ">=":
            return z[e] <= 0
        return True

    wrong_sign = [g.name(e) for e in range(len(g.edges)) if not signed(e)]
    out.append(("dual_sign", not wrong_sign, ", ".join(wrong_sign[:3]) or "-"))
    dual_value = sum((rhs[e] * z[e] for e in range(len(g.edges))), Fraction(0))
    out.append(("strong", dual_value == sgn * value, str(dual_value)))

    try:
        got = price(g, z, sgn, alpha, beta, gamma, m, threshold=0,
                    max_nodes=max_nodes, max_size=M)
    except PricingBudget:
        out.append(("pricing", False, "budget"))
        return out
    best = got["best"]
    ok = best is None or best <= 0
    claimed = payload.get("pricing") or {}
    same = (claimed.get("max_reduced") == (None if best is None else str(best))
            and claimed.get("argmax") == (None if got["argmax"] is None else
                                          [g.labels[i] for i in got["argmax"]])
            and claimed.get("nodes") == got["nodes"])
    out.append(("pricing", ok and same, "{} ({} nodes)".format(
        "-" if best is None else best, got["nodes"])))
    return out
