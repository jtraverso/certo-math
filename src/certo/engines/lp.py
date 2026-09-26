"""Motor LP/ILP.

El certificado es el DUAL, no la solucion: una solucion primal solo demuestra
que el optimo es >= algo; el dual demuestra que es <=. Juntos, optimalidad.

MODO EXACTO (por defecto). CBC trabaja en punto flotante y devuelve
10.66666656003499 donde la respuesta es 32/3 -- error de 2.5e-7, que es su
tolerancia. Con eso no se puede afirmar igualdad primal-dual ni citar una
constante. Asi que:

    resolver en flotante -> reconstruir racionales -> VERIFICAR en Fraction

y se acepta solo si la verificacion exacta pasa. Una reconstruccion mala no
verifica y se rechaza, asi que la heuristica del paso 2 no compromete nada.
El certificado resultante no depende de confiar en CBC.

Para ILP no hay dual. Se resuelve el entero para el primal y ademas la
relajacion continua, cuyo dual certifica la COTA superior. Queda dicho en el
resultado en vez de fingir optimalidad certificada.
"""
from __future__ import annotations

import os
import time
from fractions import Fraction

import pulp

from .. import exact
from ..certificate import lp_dual_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "pulp/CBC"


# ---------------------------------------------------------------------------
# PuLP 3 and PuLP 4, behind one surface
# ---------------------------------------------------------------------------
#
# PuLP 4.0.0 (2026-09-25) rebuilt the modeller in Rust, and five things this
# file used changed shape at once: a variable is made by the PROBLEM
# (`prob.add_variable`), not by `LpVariable(...)`; `prob.constraints` is a
# method returning a list, not a dict by name; `solve` returns a stats object
# whose `status` is an enum, and the `LpStatus` table is gone; and CBC is no
# longer bundled -- `PULP_CBC_CMD` is gone, `COIN_CMD` finds a binary from
# the optional `cbcbox` wheel or the PATH. PuLP 4 needs Python 3.12, so 3.11
# keeps PuLP 3, and both are supported rather than one pinned: these five
# helpers are the only places either is spoken to.

_STATUS_NAMES = {0: "Not Solved", 1: "Optimal", -1: "Infeasible",
                 -2: "Unbounded", -3: "Undefined"}


def _new_var(prob, name, lo=0, hi=None, cat=None):
    cat = pulp.LpContinuous if cat is None else cat
    if hasattr(prob, "add_variable"):                     # PuLP 4
        return prob.add_variable(name, lowBound=lo, upBound=hi, cat=cat)
    return pulp.LpVariable(name, lowBound=lo, upBound=hi, cat=cat)


def _constraint(prob, name):
    if hasattr(prob, "get_constraint_by_name"):           # PuLP 4
        return prob.get_constraint_by_name(name)
    return prob.constraints.get(name)


def _solve(prob, solver) -> str:
    """The solve, and why it stopped, as PuLP 3 named it. A stop PuLP 3 had
    no name for -- a time or node limit -- keeps PuLP 4's, and is not
    "Optimal", which is all the callers ask."""
    out = prob.solve(solver)
    code = getattr(out, "status", out)
    # CBC's own line "Optimal (within gap tolerance)" is what PuLP 3 read as
    # Optimal and PuLP 4 reports as GapLimit. Same solve, same point; and
    # nothing here takes a solver's word for optimality -- the exact route,
    # and branch and bound for an integer optimum, decide that. So a gap stop
    # WITH a solution keeps PuLP 3's name. Found by `mixed` returning "no
    # design" on PuLP 4 for an example that has one.
    if getattr(code, "name", "") == "GapLimit" and getattr(out, "has_solution",
                                                           False):
        return "Optimal"
    try:
        return _STATUS_NAMES.get(int(code), getattr(code, "name", str(code)))
    except (TypeError, ValueError):
        return str(code)


def _flips_duals(solver_name) -> bool:
    """Does this solver, through this PuLP, report a maximisation's duals
    with the opposite sign to `y >= 0`? Measured, not reasoned: on
    `max a+b+c` over three `<= 1` rows, whose duals are all +1/2, PuLP 3
    gave CBC +1/2 and HiGHS -1/2, and PuLP 4 gives -1/2 for both. Only
    speed rides on it -- the exact route tries both signs -- but a wrong
    guess sends every solve past its cheapest pass."""
    if solver_name == "HiGHS":
        return True
    return not hasattr(pulp, "PULP_CBC_CMD")              # CBC on PuLP 4


def _cbc(seconds):
    """CBC, or None when there is none: PuLP 3 bundles it, PuLP 4 finds it
    through `pulp[cbc]` (the `cbcbox` wheel) or the PATH."""
    if hasattr(pulp, "PULP_CBC_CMD"):                     # PuLP 3
        return pulp.PULP_CBC_CMD(msg=0, timeLimit=seconds)
    try:
        s = pulp.COIN_CMD(msg=False, timeLimit=seconds)
        return s if s.available() else None
    except Exception:  # noqa: BLE001 -- absent, or present and broken
        return None

#: HiGHS, in-process through highspy, for every CONTINUOUS solve -- an LP, and
#: the relaxation of an ILP. CBC stays for the integral ones. Both measured
#: before choosing: on LPs HiGHS took 1.3 ms where CBC took 258, nearly all of
#: that CBC starting as a subprocess; on random MILPs HiGHS was 1.5 to 2 times
#: SLOWER. Nothing about the certificate depends on the choice -- the exact
#: route reconstructs and checks whatever either returns -- so this is only
#: about how long an answer takes. `CERTO_LP_SOLVER=cbc` puts every solve back
#: on CBC, for anyone reproducing a run from before, and for the comparison.
PREFER_HIGHS = os.environ.get("CERTO_LP_SOLVER", "").strip().lower() != "cbc"


def _highs_available() -> bool:
    try:
        return bool(pulp.HiGHS(msg=False).available())
    except Exception:  # noqa: BLE001 -- absent, or present and broken
        return False


def _solver(lim, integral: bool):
    """`(solver, name)` for one solve: HiGHS for a continuous one when it is
    installed, CBC otherwise."""
    seconds = max(1, lim.timeout_ms // 1000)
    if not integral and PREFER_HIGHS and _highs_available():
        return pulp.HiGHS(msg=False, timeLimit=seconds), "HiGHS"
    cbc = _cbc(seconds)
    if cbc is not None:
        return cbc, "CBC"
    # No CBC -- PuLP 4 without `pulp[cbc]` -- but HiGHS solves integer
    # programs too, and the exact route checks whatever either returns.
    if _highs_available():
        return pulp.HiGHS(msg=False, timeLimit=seconds), "HiGHS"
    raise RuntimeError(t("engine.opt.no_lp_solver",
                         version=getattr(pulp, "__version__", "?")))


def _load_report(spec, x, duals_by_name):
    """What the solution does to each declared load, exactly.

    The coefficients travel with it. A load that could only be re-checked by
    re-reading the spec would be a load nobody re-checks: the point of putting
    it in the certificate is that the artefact answers on its own.
    """
    from .. import exact

    from ..certificate import normalised_rows

    names = getattr(spec, "load_names", None) or []
    if not names:
        return None
    by_name = {n: (coeffs, sense, rhs) for n, coeffs, sense, rhs in spec.cons}
    at = {v: x[j] for j, v in enumerate(spec.var_names)}
    out = []
    for n in names:
        if n not in by_name:
            continue
        coeffs, sense, rhs = by_name[n]
        achieved = sum((c * at.get(v, 0) for v, c in coeffs.items()),
                       exact.to_fraction(0))
        bound = exact.to_fraction(rhs)
        slack = bound - achieved if sense == "<=" else achieved - bound
        out.append({
            "name": n, "sense": sense,
            "coeffs": {v: exact.serialize(c) for v, c in coeffs.items()},
            "bound": exact.serialize(bound),
            "achieved": exact.serialize(achieved),
            # For "==" the slack is the deviation, and zero is the only
            # acceptable value; saying so uniformly keeps the reader from
            # having to remember which sense they wrote.
            "slack": exact.serialize(achieved - bound if sense == "=="
                                     else slack),
            "binding": (achieved == bound),
            # d(optimum)/d(bound), which is the number anyone wants and is
            # NOT simply the dual of a row called `n`. `as_leq_system` renames
            # a `>=` row to `n_geq` and negates it, and splits an `==` into
            # two; looking up the original name found nothing and reported a
            # shadow price of zero on a constraint that was costing you.
            "dual": exact.serialize(
                sum((sign * exact.to_fraction(duals_by_name.get(rn, 0))
                     for rn, sign in normalised_rows(n, sense)),
                    exact.to_fraction(0))),
            "rows": [rn for rn, _ in normalised_rows(n, sense)],
        })
    return out


def _integral_point(spec, A, b, c, sol_float):
    """CBC's integer answer, rounded and CHECKED, with its exact objective.

    Rounding a float solution is a guess; checking it against the constraints
    in exact arithmetic is not. A feasible integral point is a genuine bound
    from the other side, so an ILP ends up with both: this as the achievable
    value, the dual as the limit. When they coincide the integer optimum is
    certified exactly, and when they do not the gap is reported rather than
    hidden.
    """
    from fractions import Fraction

    x = [Fraction(round(v)) for v in sol_float]
    if any(v < 0 for v in x):
        return None
    for row, rhs in zip(A, b):
        if sum(a * xi for a, xi in zip(row, x)) > rhs:
            return None
    return x, sum(ci * xi for ci, xi in zip(c, x))


def _build(spec, A, b, c, cons_names, relax=False):
    """`relax=True` forces every variable continuous -- that is what a
    relaxation IS, and reading the spec's kinds there would rebuild the
    integer problem and leave the dual meaningless."""
    # A single category for every variable is the wrong shape for a mixed
    # problem, so ask the spec per variable -- `integer=True` on the spec
    # still means all of them.
    def _cat(v):
        if relax:
            return pulp.LpContinuous
        kind = spec.kind_of(v) if hasattr(spec, "kind_of") else (
            "integer" if getattr(spec, "integer", False) else "continuous")
        return {"continuous": pulp.LpContinuous,
                "integer": pulp.LpInteger,
                "binary": pulp.LpBinary}[kind]
    name = "".join(ch if ch.isalnum() or ch in "._-" else "_"
                   for ch in (spec.title or "opt"))
    prob = pulp.LpProblem(name, pulp.LpMaximize)
    # THE SOLVER NEVER SEES A USER'S NAME. PuLP rewrites the characters it
    # dislikes -- `0-1` becomes `0_1` -- and certo read the duals back by the
    # name it had given, so every row named like an edge came back with no
    # dual. Nothing was wrong, since the exact route derives the dual anyway,
    # but it derived it by enumerating candidates at every node: on a user's
    # 17-column packing 175 of 177 seconds, where pass 1 would have needed
    # one. Two names that rewrite to the same one also made PuLP refuse the
    # rows, and CBC crash on the columns. Positions cannot collide.
    x = {v: _new_var(prob, "x{}".format(j), lo=0,
                     hi=(1 if _cat(v) == pulp.LpBinary else None),
                     cat=_cat(v))
         for j, v in enumerate(spec.var_names)}
    names = spec.var_names
    # Only the non-zeros. A packing's rows are almost all zeros, and adding a
    # term for each of them was half the time of a branch-and-bound node --
    # the solver never saw them, but PuLP built and discarded every one.
    prob += pulp.lpSum(float(c[j]) * x[v] for j, v in enumerate(names) if c[j])
    for i, row in enumerate(A):
        prob += (
            pulp.lpSum(float(row[j]) * x[v] for j, v in enumerate(names)
                       if row[j])
            <= float(b[i]),
            _row(i),
        )
    return prob, x


def _row(i) -> str:
    """The solver's name for row `i`: a position, never the user's name."""
    return "r{}".format(i)


def _duals(prob, cons_names, negate=False):
    """CBC's duals, with `None` where it gave none.

    `pi is None` means the solver reported no dual for that row. That is not
    the same fact as "the dual is zero", and writing the zero down turns an
    absence into a number nobody can tell apart from an answer. It cost a real
    instance its certificate: every `pi` came back None, the zero vector went
    into the certificate, and `certo verify` rejected it -- correctly, since
    `b.0 = 0` bounds nothing.

    The absence is kept so the caller can refuse to certify from it. The
    exact route does not need these at all: complementary slackness and the
    exact simplex derive the dual from the problem.
    """
    out = []
    for i, _name in enumerate(cons_names):
        con = _constraint(prob, _row(i))
        pi = getattr(con, "pi", None) if con is not None else None
        # HiGHS reports the duals of a maximisation with the opposite sign to
        # CBC's, on every problem measured. Every problem here is built as a
        # maximisation, so undoing it here means the exact route starts from
        # the same dual either way -- and writes the same certificate.
        out.append(None if pi is None else (-float(pi) if negate else float(pi)))
    return out


def ms_now(t0) -> float:
    import time as _time
    return (_time.perf_counter() - t0) * 1000


def _min_or_none(values):
    """The smallest entry, or None when there are no entries.

    An empty program is a real thing -- no variables, no rows, optimum zero --
    and its dual is empty too. "The smallest price in a price list nobody
    wrote" has no value, and saying `0` would be a number somebody could read
    as a binding constraint.
    """
    vals = list(values)
    if not vals:
        return None
    from .. import exact as _exact
    return _exact.serialize(min(vals))


def _opt_split(spec, free, lim, use_exact, target, _vectors_only):
    """`opt` over the program with each free variable split in two."""
    import copy

    from .. import exact as _exact

    names = set(spec.var_names)
    pair = {}
    for v in free:
        pos, neg = v + "__pos", v + "__neg"
        k = 1
        while pos in names or neg in names:
            pos, neg = "{}__pos{}".format(v, k), "{}__neg{}".format(v, k)
            k += 1
        names |= {pos, neg}
        pair[v] = (pos, neg)

    out = copy.copy(spec)
    out.var_names, out.bounds, out.kinds = [], {}, {}
    out.cons = []
    for v in spec.var_names:
        kind = spec.kinds.get(v, "continuous")
        if v in pair:
            for w in pair[v]:
                out.var_names.append(w)
                out.bounds[w] = (0, None)
                out.kinds[w] = kind
        else:
            out.var_names.append(v)
            out.bounds[v] = spec.bounds.get(v, (0, None))
            out.kinds[v] = kind

    def split(coeffs):
        row = {}
        for v, c in coeffs.items():
            if v in pair:
                row[pair[v][0]] = c
                row[pair[v][1]] = -_exact.to_fraction(c)
            else:
                row[v] = c
        return row

    out.obj = split(spec.obj)
    for name, coeffs, sense, rhs in spec.cons:
        out.cons.append((name, split(coeffs), sense, rhs))
    # An upper bound on a free variable survives as a row: x_pos - x_neg <= hi.
    for v in free:
        hi = spec.bounds[v][1]
        if hi is not None:
            out.cons.append(("bound_{}_hi".format(v),
                             {pair[v][0]: 1, pair[v][1]: -1}, "<=", hi))

    res = opt(out, lim, use_exact=use_exact, target=target,
              _vectors_only=_vectors_only)
    split_map = {v: list(w) for v, w in pair.items()}
    if res.certificate is not None and not _vectors_only:
        res.certificate.payload["free_split"] = split_map
    sol = res.meta.get("solution")
    if isinstance(sol, dict):
        merged = {}
        for v in spec.var_names:
            if v in pair:
                a, b = (sol.get(w, "0") for w in pair[v])
                try:
                    merged[v] = _exact.serialize(_exact.to_fraction(a)
                                                 - _exact.to_fraction(b))
                except (ValueError, ZeroDivisionError):
                    merged[v] = "{} - {}".format(a, b)
            else:
                merged[v] = sol.get(v)
        res.meta["solution"] = merged
    res.meta["free_split"] = split_map
    return res


def _build_sparse(spec, rows, b, c):
    """The PuLP model from `{column: coefficient}` rows -- the same model
    `_build` makes, with positions for names, without touching a zero."""
    prob = pulp.LpProblem("node", pulp.LpMaximize)
    x = [_new_var(prob, "x{}".format(j), lo=0)
         for j in range(len(spec.var_names))]
    prob += pulp.lpSum(float(cj) * x[j] for j, cj in enumerate(c) if cj)
    for i, r in enumerate(rows):
        prob += (pulp.lpSum(float(v) * x[j] for j, v in r.items())
                 <= float(b[i]), _row(i))
    return prob, x


def _opt_vectors(spec, lim, t0):
    """A branch-and-bound node, end to end from the non-zeros: the sparse
    system, the sparse model, the exact check on the sparse matrix, and only
    the two vectors back. The dense matrix is built only if the exact route
    reaches its last pass, the exact simplex."""
    rows, b, c, names = spec.as_leq_sparse()
    ms = lambda: (time.perf_counter() - t0) * 1000  # noqa: E731
    solver, name = _solver(lim, integral=False)
    engine = "pulp/" + name
    if not c and not rows:
        return Result("opt", Status.SAT, Verdict.SATISFIABLE, engine, ms(),
                      Vectors([], [], "0"), "",
                      meta={"objective": "0", "exact": True,
                            "lp_solver": engine})
    prob, xs = _build_sparse(spec, rows, b, c)
    st = _solve(prob, solver)
    if st == "Infeasible":
        return Result("opt", Status.UNSAT, Verdict.UNSATISFIABLE, engine, ms(),
                      None, detail=t("engine.opt.infeasible"),
                      meta={"lp_solver": engine})
    if st != "Optimal":
        return Result("opt", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      engine, ms(), None,
                      detail=t("engine.opt.cbc", status=st, solver=name),
                      meta={"lp_solver": engine})
    x_float = [float(v.value() or 0.0) for v in xs]
    raw = _duals(prob, names, negate=_flips_duals(name))
    have = all(v is not None for v in raw)
    y_float = [0.0 if v is None else v for v in raw]
    alts = ([[-v for v in y_float], [abs(v) for v in y_float]] if have else [])
    P = exact.Prepared.from_sparse(rows, b, c)
    x_ex, y_ex, rep, denom = exact.certify(P, b, c, x_float, y_float,
                                           y_alts=alts)
    if x_ex is None:
        return Result("opt", Status.SAT, Verdict.SATISFIABLE, engine, ms(),
                      None, detail=t("engine.opt.unverifiable",
                                     value=repr(sum(float(cj) * xv for cj, xv
                                                    in zip(c, x_float)))),
                      meta={"exact": False, "lp_solver": engine})
    objective_ex = rep["objective"]
    if spec.sense == "min":
        objective_ex = -objective_ex
    return Result(
        "opt", Status.SAT, Verdict.SATISFIABLE, engine, ms(),
        Vectors(exact.serialize_all(y_ex), exact.serialize_all(x_ex),
                exact.serialize(rep["objective"])),
        t("engine.opt.exact", value=exact.serialize(objective_ex), denom=denom),
        meta={"objective": exact.serialize(objective_ex), "exact": True,
              "lp_solver": engine})


def _direction_vector(spec, cons_names, direction):
    """Weights on the dual of each DECLARED constraint, as a vector over the
    rows of the internal system: a `<=` row as it is, a `>=` row on its
    `_geq` row, an equality's weight split `+w`/`-w` over its two halves --
    so `d.y` is the weighted sum of the declared constraints' multipliers."""
    declared = {name: sense for name, _c, sense, _r in spec.cons}
    unknown = sorted(set(direction) - set(declared))
    if unknown:
        raise ValueError(t("engine.opt.direction_unknown",
                           names=", ".join(unknown[:4]),
                           known=", ".join(sorted(declared)[:6])))
    index = {n: i for i, n in enumerate(cons_names)}
    d = [exact.to_fraction(0)] * len(cons_names)
    for name, w in direction.items():
        w = exact.to_fraction(w)
        sense = declared[name]
        if sense == "<=":
            d[index[name]] += w
        elif sense == ">=":
            d[index[name + "_geq"]] += w
        else:
            d[index[name + "_le"]] += w
            d[index[name + "_ge"]] -= w
    return d


def _select_dual(spec, A, b, c, cons_names, x_ex, rep, direction, lim):
    """Among the OPTIMAL duals, one maximising `d.y`, by a second exact LP:

        max d.y   s.t.   A^T y >= c,   b.y <= v*,   y >= 0

    where weak duality turns `b.y <= v*` into `b.y = v*`. Returns
    `(y, selection)` -- the chosen dual, and a record carrying that second
    LP's own certificate, which is what proves the choice MAXIMAL rather
    than merely optimal -- or None when the direction is unbounded on the
    optimal face or the second LP could not be certified."""
    from ..spec import LPSpec

    d = _direction_vector(spec, cons_names, direction)
    m, n = len(A), len(c)
    v = rep["objective"]
    s = LPSpec(sense="max", title="dual selection")
    ys = ["y{}".format(i) for i in range(m)]
    for y in ys:
        s.variable(y)
    s.objective({ys[i]: d[i] for i in range(m) if d[i]})
    for j in range(n):
        s.constraint({ys[i]: A[i][j] for i in range(m) if A[i][j]}, ">=", c[j],
                     name="col{}".format(j))
    s.constraint({ys[i]: b[i] for i in range(m) if b[i]}, "<=", v, name="value")
    res = opt(s, lim)
    if res.certificate is None or not res.meta.get("exact"):
        return None
    y = [exact.to_fraction(res.meta["solution"].get(name, "0")) for name in ys]
    if not exact.check_lp(A, b, c, x_ex, y)["ok"]:
        return None                      # not an optimal dual after all
    value = sum((d[i] * y[i] for i in range(m)), exact.to_fraction(0))
    return y, {"direction": exact.serialize_all(d),
               "value": exact.serialize(value),
               "certificate": res.certificate.to_dict()}


class Vectors:
    """What a branch-and-bound node keeps of an exact LP solution: the dual
    and the primal, exactly as a certificate would hold them, and nothing
    else. Not a certificate -- it cannot be saved or verified on its own --
    and named so nothing mistakes it for one."""

    __slots__ = ("payload",)
    kind = "lp_vectors"

    def __init__(self, dual, primal, objective):
        self.payload = {"dual": dual, "primal": primal,
                        "objective": objective, "exact": True}


def opt(spec, limits: Limits | None = None, use_exact: bool = True,
        target=None, dual_direction=None, _vectors_only: bool = False) -> Result:
    """`_vectors_only=True` is for callers that keep only the dual and the
    primal -- branch and bound, which derives every node's program from the
    root. Serialising the whole matrix into a certificate at every node was
    most of a node's cost on 1048 columns: 97 million `serialize` calls in 71
    nodes, for a certificate the tree then discarded. The exact check is the
    same one; only the artefact is smaller."""
    lim = limits or Limits()
    t0 = time.perf_counter()

    for v, (lo, hi) in spec.bounds.items():
        if lo is not None and lo < 0:
            raise ValueError(t("engine.opt.negative_bound", var=v))

    # FREE VARIABLES, natively: each is split into two non-negative ones,
    # x = x_pos - x_neg, the program over those is solved and certified in the
    # standard form, and the split is RECORDED so `verify` can check the two
    # columns are exact negatives of each other -- which is what makes the
    # certified program the image of the one written. A user split every
    # free price by hand before this; before 0.17 `lo=None` was read as 0.
    free = [v for v in spec.var_names if spec.bounds.get(v, (0, None))[0] is None]
    if free:
        return _opt_split(spec, free, lim, use_exact, target, _vectors_only)
    if _vectors_only and use_exact and not (
            getattr(spec, "discrete", None) or getattr(spec, "integer", False)):
        return _opt_vectors(spec, lim, t0)

    A, b, c, cons_names = spec.as_leq_system()

    # AN EMPTY PROGRAM IS VACUOUS, and saying so is the difference between
    # this and a tool that reports "EXACT optimum certified: 0" for a question
    # nobody asked. No variables and no rows does have an optimum -- the empty
    # sum, zero -- and a certificate of it establishes nothing about anything.
    # `exists` already says this about an empty universe; a program with no
    # columns is the same shape one level down.
    if not c and not A:
        return Result(
            "opt", Status.SAT, Verdict.SATISFIABLE, ENGINE, ms_now(t0), None,
            detail=t("engine.opt.empty_program"),
            meta={"objective": "0", "variables": 0, "constraints": 0,
                  "exact": True, "min_dual": None, "vacuous": True})

    # "Has a discrete part" is the condition, not "the whole thing is an ILP":
    # a mixed problem has a dual for its relaxation just the same.
    discrete = bool(getattr(spec, "discrete", [])) or spec.integer

    solver, main_name = _solver(lim, integral=discrete)
    used = [main_name]

    prob, xvars = _build(spec, A, b, c, cons_names)
    st_name = _solve(prob, solver)
    ms = lambda: (time.perf_counter() - t0) * 1000  # noqa: E731
    engine = lambda: "pulp/" + "+".join(dict.fromkeys(used))  # noqa: E731

    if st_name == "Infeasible":
        return Result("opt", Status.UNSAT, Verdict.UNSATISFIABLE, engine(), ms(),
                      None, detail=t("engine.opt.infeasible"),
                      meta={"lp_solver": engine()})
    if st_name != "Optimal":
        return Result("opt", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE,
                      engine(), ms(), None,
                      detail=t("engine.opt.cbc", status=st_name,
                                    solver=main_name),
                      meta={"lp_solver": engine()})

    sol_float = [float(xvars[v].value() or 0.0) for v in spec.var_names]

    # An ILP has two numbers and they are not the same number. CBC's integer
    # answer is one; the relaxation the dual certifies is another, and it is
    # only a BOUND on the first. Reporting the bound as "the objective" is
    # exactly the kind of overclaim this tool exists to prevent -- and it did
    # it, until a real instance where nu = 7 was reported as 15/2.
    # Rounding EVERY variable is only right when every variable is discrete.
    # On a mixed problem it rounds the fractional weights to zero and reports
    # a "design" worth nothing; the achievable value there comes from freezing
    # the discrete part and re-solving the rest, which is `mixed`.
    all_discrete = discrete and not getattr(spec, "continuous", [])
    integral = None
    if all_discrete:
        integral = _integral_point(spec, A, b, c, sol_float)

    # The dual always comes from the continuous relaxation: an ILP has none.
    #
    # The relaxation's status used to be discarded. A relaxation that was not
    # solved to optimality leaves every `pi` empty, and the run carried on as
    # if it had a dual -- which is how a certificate with an identically zero
    # dual gets written. Not fatal, though: the exact route derives the dual
    # from the problem and does not consult CBC at all. So a failed relaxation
    # costs the float fallback and the starting point, not the certificate.
    relax_status = "Optimal"
    if discrete:
        rprob, rx = _build(spec, A, b, c, cons_names, relax=True)
        rsolver, dual_name = _solver(lim, integral=False)
        used.append(dual_name)
        relax_status = _solve(rprob, rsolver)
        dual_src = rprob
        relax_x = ([float(rx[v].value() or 0.0) for v in spec.var_names]
                   if relax_status == "Optimal" else sol_float)
    else:
        dual_src, relax_x, dual_name = prob, sol_float, main_name
    dual_raw = (_duals(dual_src, cons_names, negate=_flips_duals(dual_name))
                if relax_status == "Optimal" else [None] * len(cons_names))
    have_duals = all(v is not None for v in dual_raw)
    dual_float = [0.0 if v is None else v for v in dual_raw]

    # ---- certificacion exacta ------------------------------------------
    exact_ok, x_ex, y_ex, rep, denom = False, None, None, None, None
    if use_exact:
        # CBC no fija el signo del dual; deja que la comprobacion exacta
        # decida. Van en la misma llamada porque solo la pasada 1 los lee: las
        # 2 y 3 derivan el dual del problema, y repetirlas por cada signo
        # repetia el trabajo caro tres veces.
        alts = ([[-v for v in dual_float], [abs(v) for v in dual_float]]
                if have_duals else [])
        x_ex, y_ex, rep, denom = exact.certify(A, b, c, relax_x, dual_float,
                                               y_alts=alts)
        exact_ok = x_ex is not None

    selection = None
    if exact_ok and dual_direction and not _vectors_only:
        chosen = _select_dual(spec, A, b, c, cons_names, x_ex, rep, dual_direction,
                              lim)
        if chosen is not None:
            y_ex, selection = chosen

    if exact_ok and _vectors_only:
        objective_ex = rep["objective"]
        if spec.sense == "min":
            objective_ex = -objective_ex
        return Result(
            "opt", Status.SAT, Verdict.SATISFIABLE, engine(), ms(),
            Vectors(exact.serialize_all(y_ex), exact.serialize_all(x_ex),
                    exact.serialize(rep["objective"])),
            t("engine.opt.exact", value=exact.serialize(objective_ex),
              denom=denom),
            meta={"objective": exact.serialize(objective_ex), "exact": True,
                  "lp_solver": engine()})

    if exact_ok:
        objective_ex = rep["objective"]
        if spec.sense == "min":
            objective_ex = -objective_ex
        loads = _load_report(spec, x_ex,
                             dict(zip(cons_names, y_ex)) if y_ex else {})
        cert = lp_dual_certificate(
            loads=loads, backend=engine(), dual_selection=selection,
            meaning=getattr(spec, "meaning", None),
            sense=spec.sense, objective=exact.serialize(rep["objective"]),
            dual=exact.serialize_all(y_ex), primal=exact.serialize_all(x_ex),
            A=[exact.serialize_all(r) for r in A], b=exact.serialize_all(b),
            c=exact.serialize_all(c), names=cons_names,
            var_names=list(spec.var_names), is_exact=True,
            integer=discrete,
            kinds={v: (spec.kind_of(v) if hasattr(spec, "kind_of")
                       else ("integer" if spec.integer else "continuous"))
                   for v in spec.var_names},
            target=None if target is None else exact.serialize(
                exact.to_fraction(target)),
            integral_point=None if integral is None
            else exact.serialize_all(integral[0]),
            integral_objective=None if integral is None
            else exact.serialize(integral[1]),
        )
        detail = t("engine.opt.exact", value=exact.serialize(objective_ex),
                   denom=denom)
        meta_obj = exact.serialize(objective_ex)
        meta_sol = {v: exact.serialize(x_ex[j])
                    for j, v in enumerate(spec.var_names)} if not discrete else {
            v: repr(sol_float[j]) for j, v in enumerate(spec.var_names)}

        if discrete:
            # The internal system MAXIMISES, so for `sense="min"` every number
            # read out of it is the negation of the declared one. The line
            # above does that for `objective_ex`; this branch replaced both
            # numbers and did not, so a minimisation ILP whose answer was 2
            # reported -2, and so did its certificate. Every "minimum
            # deletion" question has this shape.
            flip = -1 if spec.sense == "min" else 1
            bound = exact.serialize(flip * rep["objective"])
            if integral is None:
                # Nothing to report but the bound -- and it is named a bound.
                detail = t("engine.opt.mixed_bound_only", bound=bound)                         if not all_discrete else                                                   t("engine.opt.ilp_bound_only", bound=bound)
                meta_obj = None
            else:
                meta_obj = exact.serialize(flip * integral[1])
                tight = integral[1] == rep["objective"]
                detail = t("engine.opt.ilp_tight" if tight
                           else "engine.opt.ilp_gap",
                           value=meta_obj, bound=bound)
                meta_sol = {v: exact.serialize(integral[0][j])
                            for j, v in enumerate(spec.var_names)}
    else:
        obj_max = float(pulp.value(prob.objective))
        objective = obj_max if spec.sense == "max" else -obj_max
        meta_obj = objective
        meta_sol = {v: sol_float[j] for j, v in enumerate(spec.var_names)}

        # A float certificate is allowed to be LOOSE -- that is what the
        # tolerance is for. It is not allowed to be one certo rejects. So the
        # tool asks its own verifier before handing the artefact over: an
        # artefact that fails `certo verify` is not a weaker certificate, it
        # is not a certificate, and writing it wastes the reader's trust
        # rather than the tool's time.
        #
        # What goes back instead is the number, plainly labelled uncertified.
        # The verdict stays SATISFIABLE because CBC did exhibit a feasible
        # point; it is the OPTIMALITY claim that lives in the certificate, and
        # `mixed` depends on this step for its skeleton and nothing else.
        why = "" if not use_exact else t("engine.opt.float.why")
        if not have_duals:
            cert, detail = None, t("engine.opt.no_dual", value=repr(objective))
        else:
            cert = lp_dual_certificate(
                sense=spec.sense, objective=obj_max,
                dual=[abs(v) for v in dual_float],
                primal=relax_x, A=[[float(v) for v in r] for r in A],
                b=[float(v) for v in b], c=[float(v) for v in c],
                names=cons_names, var_names=list(spec.var_names),
                is_exact=False, backend=engine(),
            )
            from ..certificate import verify as _verify

            if _verify(cert).ok:
                detail = t("engine.opt.float") + why
            else:
                cert = None
                detail = t("engine.opt.unverifiable", value=repr(objective))

    return Result(
        "opt", Status.SAT, Verdict.SATISFIABLE, engine(), ms(), cert, detail,
        meta={"objective": meta_obj,
              "lp_solver": engine(),
              "objective_float": (None if meta_obj is None
                                  else float(exact.to_fraction(meta_obj))),
              # In the declared sense, like `objective` beside it. This one
              # was computed a third time, from the internal system, and so
              # kept the sign the other two had already lost.
              "bound": (exact.serialize(
                  (-1 if spec.sense == "min" else 1) * rep["objective"])
                  if exact_ok and discrete else None),
              "exact": exact_ok, "solution": meta_sol,
              "integer": discrete, "denominator": denom,
              # `None`, not 0.0, when there is no dual: the smallest entry of
              # a vector nobody produced is not zero, it is nothing.
              #
              # THE EXACT BRANCH DID NOT KEEP THAT PROMISE. `min(y_ex)` on an
              # empty dual raised `ValueError: min() iterable argument is
              # empty`, which a user hit by running a program with no rows at
              # all. The comment above was already right; only this line
              # disagreed with it.
              "min_dual": (_min_or_none(y_ex) if exact_ok
                           else (min([abs(v) for v in dual_float], default=0.0)
                                 if have_duals else None)),
              "target": None if target is None else exact.serialize(
                  exact.to_fraction(target)),
              "meets_target": (None if target is None or not exact_ok else
                               exact.to_fraction(meta_obj)
                               >= exact.to_fraction(target))},
    )


def infeasible_certificate(spec, limits=None):
    """A Farkas ray proving `Ax <= b, x >= 0` has no solution.

    `y >= 0` with `A^T y >= 0` and `b.y < 0`. If such a y exists then for any
    feasible x we would have `0 <= (A^T y).x = y.(Ax) <= y.b < 0`, which is
    the contradiction -- and checking it is three dot products in exact
    rationals, with no solver and no trust in the one that said "infeasible".

    Returns None when no ray is found, which is not the same as "the system is
    feasible": the auxiliary LP is itself solved numerically, and a failure to
    reconstruct it exactly leaves us with nothing to say rather than with a
    claim.
    """
    from .. import exact
    from ..certificate import farkas_ray_certificate
    from ..spec import LPSpec

    A, b, c, names = spec.as_leq_system()
    if not A:
        return None

    # minimise b.y subject to A^T y >= 0, y >= 0, sum y = 1. The normalisation
    # keeps the ray bounded; any positive multiple of a ray is a ray.
    aux = LPSpec(sense="min", title="farkas ray")
    ys = ["y{}".format(i) for i in range(len(A))]
    for v in ys:
        aux.variable(v)
    aux.objective({v: b[i] for i, v in enumerate(ys)})
    for j in range(len(c)):
        aux.constraint({ys[i]: A[i][j] for i in range(len(A))}, ">=", 0,
                       name="col{}".format(j))
    aux.constraint({v: 1 for v in ys}, "==", 1, name="norm")

    res = opt(aux, limits)
    if res.verdict is not Verdict.SATISFIABLE or not res.meta.get("exact"):
        return None
    y = [exact.to_fraction(res.meta["solution"].get(v, 0)) for v in ys]

    # Check the ray ourselves before emitting it. An "infeasibility
    # certificate" that does not certify infeasibility is worse than none.
    if any(v < 0 for v in y):
        return None
    if any(sum(A[i][j] * y[i] for i in range(len(A))) < 0
           for j in range(len(c))):
        return None
    if sum(b[i] * y[i] for i in range(len(A))) >= 0:
        return None

    return farkas_ray_certificate(
        A=[exact.serialize_all(r) for r in A], b=exact.serialize_all(b),
        y=exact.serialize_all(y), names=names)
