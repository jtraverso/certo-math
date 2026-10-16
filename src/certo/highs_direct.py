"""HiGHS, spoken to directly through `highspy` -- not through PuLP.

The two releases before this one were held up by the layer in between:
PuLP 4 with highspy 1.15 reported a maximisation's duals with the other
sign, and PuLP 4.0.1 could not be imported without numpy. The solver itself
was never the problem. Asked directly, it also gives what PuLP throws away:

  the optimal BASIS     which columns and which slacks are basic -- the
                        exact optimum is one elimination on that system,
                        instead of a basis inferred from a float support
  an IIS                the rows an infeasible program cannot satisfy
                        together -- the Farkas ray is then sought on those
                        rows only, and comes back smaller
  a MIP's incumbent     an integer point to start branch and bound from,
  and dual bound        and the solver's bound, said as the solver's

Nothing here is trusted. The basis proposes an exact primal-dual pair that
`exact.check_lp` decides; the IIS restricts where a ray is looked for, and
the ray is checked; the incumbent is re-certified as a design by `mixed`.
Every function returns None when highspy is not installed or the solver
does not answer, and the callers fall back to the PuLP route.

The model is always certo's normal form: max c.x subject to A x <= b,
x >= 0 -- the system `as_leq_sparse` produces.
"""
from __future__ import annotations

import os

_HS = []


def available() -> bool:
    """highspy importable, and not switched off (`CERTO_LP_SOLVER=cbc`, or
    `CERTO_HIGHS_DIRECT=0` to compare against the PuLP route)."""
    if os.environ.get("CERTO_LP_SOLVER", "").strip().lower() == "cbc":
        return False
    if os.environ.get("CERTO_HIGHS_DIRECT", "").strip() in ("0", "no", "off"):
        return False
    if not _HS:
        try:
            import highspy

            _HS.append(highspy)
        except Exception:  # noqa: BLE001 -- absent, or present and broken
            _HS.append(None)
    return _HS[0] is not None


def _model(rows, b, c, integer=(), seconds=None):
    hs = _HS[0]
    h = hs.Highs()
    h.setOptionValue("output_flag", False)
    if seconds:
        h.setOptionValue("time_limit", float(seconds))
    n, m = len(c), len(rows)
    inf = hs.kHighsInf
    lp = hs.HighsLp()
    lp.num_col_ = n
    lp.num_row_ = m
    lp.col_cost_ = [float(v) for v in c]
    lp.col_lower_ = [0.0] * n
    lp.col_upper_ = [inf] * n
    lp.row_lower_ = [-inf] * m
    lp.row_upper_ = [float(v) for v in b]
    lp.sense_ = hs.ObjSense.kMaximize
    # column-wise sparse matrix
    cols = [[] for _ in range(n)]
    for i, r in enumerate(rows):
        for j, a in (r.items() if isinstance(r, dict) else r):
            if a:
                cols[j].append((i, float(a)))
    start, index, value = [0], [], []
    for col in cols:
        for i, a in col:
            index.append(i)
            value.append(a)
        start.append(len(index))
    lp.a_matrix_.format_ = hs.MatrixFormat.kColwise
    lp.a_matrix_.start_ = start
    lp.a_matrix_.index_ = index
    lp.a_matrix_.value_ = value
    lp.a_matrix_.num_col_ = n
    lp.a_matrix_.num_row_ = m
    if integer:
        kinds = [hs.HighsVarType.kContinuous] * n
        for j in integer:
            kinds[j] = hs.HighsVarType.kInteger
        lp.integrality_ = kinds
    h.passModel(lp)
    return h


def _status(h):
    hs = _HS[0]
    st = h.getModelStatus()
    if st == hs.HighsModelStatus.kOptimal:
        return "optimal"
    if st == hs.HighsModelStatus.kInfeasible:
        return "infeasible"
    if st in (hs.HighsModelStatus.kUnbounded, hs.HighsModelStatus.kUnboundedOrInfeasible):
        return "unbounded"
    if st == hs.HighsModelStatus.kTimeLimit:
        return "time"
    return h.modelStatusToString(st)


def solve_lp(rows, b, c, seconds=None) -> dict | None:
    """`{"status", "x", "y", "basis", "objective"}` for max c.x, A x <= b,
    x >= 0. `y` is oriented so that `b.y` is the optimum -- by strong
    duality, measured, not by a table of versions. `basis` is
    `{"cols": [...], "rows": [...]}`: the basic structural columns and the
    rows whose slack is basic."""
    if not available():
        return None
    try:
        h = _model(rows, b, c, seconds=seconds)
        h.run()
        status = _status(h)
        out = {"status": status, "x": None, "y": None, "basis": None,
               "objective": None}
        if status != "optimal":
            return out
        sol = h.getSolution()
        x = list(sol.col_value)
        y = list(sol.row_dual)
        value = float(h.getInfo().objective_function_value)
        s = sum(float(bi) * yi for bi, yi in zip(b, y))
        if abs(s - value) > abs(s + value) + 1e-9:
            y = [-v for v in y]
        basis = h.getBasis()
        hs = _HS[0]
        basic = hs.HighsBasisStatus.kBasic
        out.update(x=x, y=y, objective=value, basis={
            "cols": [j for j, st in enumerate(basis.col_status) if st == basic],
            "rows": [i for i, st in enumerate(basis.row_status) if st == basic]})
        return out
    except Exception:  # noqa: BLE001 -- a solver that misbehaves is a solver absent
        return None


def iis_rows(rows, b, c, seconds=None) -> list | None:
    """The rows of an irreducible infeasible subsystem, or None. Bounds on
    `x >= 0` are always part of the system, so only rows are reported."""
    if not available():
        return None
    try:
        h = _model(rows, b, [0.0] * len(c), seconds=seconds)
        # Measured on highspy 1.15: strategies 0 and 1 return an empty (or
        # invalid) set on a plainly infeasible system; 2 and above find it.
        h.setOptionValue("iis_strategy", 2)
        h.run()
        if _status(h) != "infeasible":
            return None
        got = h.getIis()
        iis = got[1] if isinstance(got, tuple) else got
        if not getattr(iis, "valid_", True):
            return None
        idx = list(getattr(iis, "row_index_", None) or [])
        return sorted(set(int(i) for i in idx)) or None
    except Exception:  # noqa: BLE001
        return None


def solve_mip(rows, b, c, integer, seconds=None) -> dict | None:
    """`{"status", "x", "objective", "dual_bound"}`: HiGHS's incumbent and
    its own bound on the optimum. Neither is certified here: the incumbent
    is re-checked as a design by whoever uses it, and the bound is reported
    as the solver's."""
    if not available():
        return None
    try:
        h = _model(rows, b, c, integer=integer, seconds=seconds)
        h.run()
        info = h.getInfo()
        status = _status(h)
        x = None
        if status in ("optimal", "time") and int(getattr(info, "primal_solution_status", 0)) == 2:
            x = list(h.getSolution().col_value)
        return {"status": status, "x": x,
                "objective": float(info.objective_function_value) if x is not None else None,
                "dual_bound": float(info.mip_dual_bound)}
    except Exception:  # noqa: BLE001
        return None
