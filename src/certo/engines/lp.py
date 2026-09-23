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

import time
from fractions import Fraction

import pulp

from .. import exact
from ..certificate import lp_dual_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "pulp/CBC"


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
    x = {v: pulp.LpVariable(v, lowBound=0,
                            upBound=(1 if _cat(v) is pulp.LpBinary else None),
                            cat=_cat(v))
         for v in spec.var_names}
    prob += pulp.lpSum(float(c[j]) * x[v] for j, v in enumerate(spec.var_names))
    for i, row in enumerate(A):
        prob += (
            pulp.lpSum(float(row[j]) * x[v] for j, v in enumerate(spec.var_names))
            <= float(b[i]),
            cons_names[i],
        )
    return prob, x


def _duals(prob, cons_names):
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
    for name in cons_names:
        con = prob.constraints.get(name)
        pi = getattr(con, "pi", None) if con is not None else None
        out.append(None if pi is None else float(pi))
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


def opt(spec, limits: Limits | None = None, use_exact: bool = True,
        target=None) -> Result:
    lim = limits or Limits()
    t0 = time.perf_counter()

    for v, (lo, hi) in spec.bounds.items():
        if lo is not None and lo < 0:
            raise ValueError(t("engine.opt.negative_bound", var=v))

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

    solver = pulp.PULP_CBC_CMD(msg=0, timeLimit=max(1, lim.timeout_ms // 1000))

    prob, xvars = _build(spec, A, b, c, cons_names)
    code = prob.solve(solver)
    st_name = pulp.LpStatus[code]
    ms = lambda: (time.perf_counter() - t0) * 1000  # noqa: E731

    if st_name == "Infeasible":
        return Result("opt", Status.UNSAT, Verdict.UNSATISFIABLE, ENGINE, ms(), None,
                      detail=t("engine.opt.infeasible"))
    if st_name != "Optimal":
        return Result("opt", Status.UNKNOWN_SOLVER, Verdict.INCONCLUSIVE, ENGINE,
                      ms(), None, detail=t("engine.opt.cbc", status=st_name))

    sol_float = [float(xvars[v].value() or 0.0) for v in spec.var_names]

    # "Has a discrete part" is the condition, not "the whole thing is an ILP":
    # a mixed problem has a dual for its relaxation just the same.
    discrete = bool(getattr(spec, "discrete", [])) or spec.integer

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
        relax_status = pulp.LpStatus[rprob.solve(solver)]
        dual_src = rprob
        relax_x = ([float(rx[v].value() or 0.0) for v in spec.var_names]
                   if relax_status == "Optimal" else sol_float)
    else:
        dual_src, relax_x = prob, sol_float
    dual_raw = (_duals(dual_src, cons_names) if relax_status == "Optimal"
                else [None] * len(cons_names))
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

    if exact_ok:
        objective_ex = rep["objective"]
        if spec.sense == "min":
            objective_ex = -objective_ex
        loads = _load_report(spec, x_ex,
                             dict(zip(cons_names, y_ex)) if y_ex else {})
        cert = lp_dual_certificate(
            loads=loads,
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
                is_exact=False,
            )
            from ..certificate import verify as _verify

            if _verify(cert).ok:
                detail = t("engine.opt.float") + why
            else:
                cert = None
                detail = t("engine.opt.unverifiable", value=repr(objective))

    return Result(
        "opt", Status.SAT, Verdict.SATISFIABLE, ENGINE, ms(), cert, detail,
        meta={"objective": meta_obj,
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
