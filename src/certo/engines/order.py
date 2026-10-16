"""The `order` command: does this term decay in n, or is it Theta(1)?

The gap a user pointed at, in their words: they take a symbolic constraint,
substitute asymptotic magnitudes by hand, and ask whether a term decays. Four
bugs lived in that step, and one of them -- a term constant in `n` -- was
invisible to both Lean and `prove`, because it is not an infeasibility. It is
a feasibility that does not improve with `n`, and a solver asked "is this
satisfiable" will keep saying yes, correctly, forever.

The search here is not a search: substitute, collect, read off the leading
exponent. What makes it worth a certificate is that the substitution is
written down rather than done in someone's head, and that the collection is
exact -- two terms sharing the top exponent whose coefficients cancel really
do cancel, and with `Fraction` that is decided rather than estimated.
"""
from __future__ import annotations

import time

from .. import asymptotics
from ..certificate import order_certificate
from ..i18n import t
from ..limits import Limits
from ..status import Result, Status, Verdict

ENGINE = "certo/order"

from ..budget import honours_timeout  # noqa: E402


@honours_timeout("order", ENGINE)
def order(spec, limits: Limits | None = None, spec_path: str = "") -> Result:
    t0 = time.perf_counter()

    def ms():
        return (time.perf_counter() - t0) * 1000

    derived = None
    orders = dict(spec.orders or {})
    if getattr(spec, "relations", None):
        # The six numbers people put here are derived mentally from relations
        # they already know, and one wrong entry gives a clean false answer.
        # Solving the relations instead is a linear program over the exponents.
        from .. import orderinfer

        try:
            poly0 = asymptotics.parse(spec.expression)
            symbols = sorted({sym for m in poly0.terms for sym, _p in m})
        except asymptotics.NotAsymptotic as e:
            return Result("order", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                          ENGINE, ms(), None,
                          detail=t("engine.order.not_asymptotic",
                                   detail=str(e)))
        try:
            derived = orderinfer.derive_orders(
                spec.relations, spec.orders, symbols, spec.var)
        except orderinfer.NotInferable as e:
            return Result("order", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                          ENGINE, ms(), None, detail=str(e))
        orders = derived["orders"]

    try:
        poly = asymptotics.parse(spec.expression)
        rep = asymptotics.order(poly, orders, spec.var)
    except asymptotics.NotAsymptotic as e:
        return Result("order", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE,
                      ENGINE, ms(), None,
                      detail=t("engine.order.not_asymptotic", detail=str(e)))

    cert = order_certificate(
        laurent=_serialize(poly), orders={k: str(v) for k, v in orders.items()},
        derived=derived,
        var=spec.var, terms=rep["terms"], collected=rep["collected"],
        degree=rep["degree"], verdict=rep["verdict"], expect=spec.expect,
        cancelled=rep["cancelled"], title=spec.title,
    ).stamp(spec_path or None)

    meta = {"degree": rep["degree"], "behaviour": rep["verdict"],
            "cancelled": rep["cancelled"],
            "leading": rep["collected"][:3]}

    if spec.expect is None:
        return Result("order", Status.SAT, Verdict.SATISFIABLE, ENGINE, ms(),
                      cert, detail=t("engine.order.measured",
                                     degree=rep["degree"] or "-",
                                     var=spec.var,
                                     verdict=t("order." + rep["verdict"])),
                      meta=meta)

    if rep["verdict"] == spec.expect:
        return Result("order", Status.UNSAT, Verdict.PROVED, ENGINE, ms(),
                      cert, detail=t("engine.order.holds",
                                     verdict=t("order." + rep["verdict"]),
                                     degree=rep["degree"] or "-",
                                     var=spec.var),
                      meta=meta)

    return Result("order", Status.SAT, Verdict.REFUTED, ENGINE, ms(), cert,
                  detail=t("engine.order.refuted",
                           want=t("order." + spec.expect),
                           got=t("order." + rep["verdict"]),
                           degree=rep["degree"] or "-", var=spec.var),
                  meta=meta)


def _serialize(poly) -> list:
    """The Laurent polynomial, so verification needs neither z3 nor the spec."""
    return [{"monomial": [[s, p] for s, p in m], "coefficient": str(c)}
            for m, c in poly.terms.items()]
