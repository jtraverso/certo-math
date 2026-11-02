"""WHY a result is not an answer, in one word from a fixed list -- and how
long each phase of the run took.

"inconclusive" said that nothing was settled and not what to do next. A
dozen sessions read the detail sentence to tell a negative Bernstein
coefficient (subdivide, raise the degree, add a multiplier) from the clock
(more time) from a template too small (a larger one) -- and the sentence is
written for people, in two languages. The code is for programs:

    clock                    the time budget ran out
    resource                 a bound other than time: conflicts, nodes, memory
    negative_coefficient     a coefficient stayed negative at the depth and
                             degree allowed -- a certificate of THIS shape
                             was not found, nothing is refuted
    negative_point           a rational point where a residual of the route
                             (a dual, a claim) is negative: THIS witness fails
                             there, another may not
    physical_counterexample  a counterexample of the real problem -- in the
                             original domain, or from a domain verifier
    template_too_small       no candidate in the template or bounded domain
                             searched; a larger one may have one
    rounding                 a floating answer that could not be confirmed
                             exactly
    solver_unknown           the solver gave up (nonlinear, quantifiers)
    out_of_theory            the question is outside what the command handles
    unchecked                a proof was found and its check did not finish

`classify(res)` is None for a conclusive result. An engine that KNOWS sets
`meta["why"]`; otherwise the code is read off the detail's catalogue key, and
last off the status -- so every inconclusive result has one.

PHASES. `meta["phases_ms"]`: construction (the spec read into a problem),
search, extraction (the certificate written) and self_check, where the engine
measures them. Only measured phases appear: a phase is never estimated.
"""
from __future__ import annotations

import time
from contextlib import contextmanager

CODES = ("clock", "resource", "negative_coefficient", "negative_point",
         "physical_counterexample", "template_too_small", "rounding",
         "solver_unknown", "out_of_theory", "unchecked")

#: A catalogue key that says which, when the engine did not.
_BY_KEY = {
    "nonneg.unknown": "negative_coefficient",
    "nonneg.multipliers_short": "negative_coefficient",
    "nonneg.witness_short": "negative_coefficient",
    "engine.param.not_shown_box": "negative_coefficient",
    "engine.param.not_shown": "negative_coefficient",
    "atlas.not_proved": "negative_coefficient",
    "engine.opt.infeasible_unproved": "rounding",
    "explore.lp": "rounding",
    "engine.opt.cbc": "rounding",
    "engine.synth.max_iter": "resource",
    "engine.synth.timeout": "clock",
    "engine.cases.badproof": "unchecked",
    "engine.strengthen.none": "template_too_small",
    "engine.synth.domain_rejected": "physical_counterexample",
}


def classify(res):
    """The code, or None when the result is conclusive."""
    st = getattr(res, "status", None)
    if st is None or st.conclusive:
        if (getattr(res, "meta", None) or {}).get("proof_state") == "unchecked":
            return "unchecked"
        return None
    meta = getattr(res, "meta", None) or {}
    code = meta.get("why")
    if code in CODES:
        return code
    from .status import Status

    if st is Status.TIMEOUT:
        return "clock"
    if st is Status.RESOURCE_EXHAUSTED:
        return "resource"
    try:
        from .coverage import why_of

        key = why_of(getattr(res, "detail", ""))
    except Exception:  # noqa: BLE001 -- a reason must never fail a result
        key = None
    if key in _BY_KEY:
        return _BY_KEY[key]
    if st is Status.OUT_OF_THEORY:
        return "out_of_theory"
    if st is Status.EXPLORED:
        return "rounding"
    return "solver_unknown"


class Phases:
    """`with ph("search"): ...` -- milliseconds per phase, summed."""

    def __init__(self):
        self.ms = {}

    @contextmanager
    def __call__(self, name):
        t0 = time.perf_counter()
        try:
            yield
        finally:
            self.ms[name] = self.ms.get(name, 0.0) + (time.perf_counter() - t0) * 1000

    def into(self, res):
        """Record on `res.meta["phases_ms"]`, keeping phases already there."""
        have = dict(res.meta.get("phases_ms") or {})
        for k, v in self.ms.items():
            have[k] = round(have.get(k, 0.0) + v, 2)
        res.meta["phases_ms"] = have
        return res
