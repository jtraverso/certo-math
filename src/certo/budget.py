"""Every engine stops when its budget does.

`Limits.timeout_ms` reached z3 and nothing else: seventeen engines took a
`limits` argument and never read it, and a user who asked a semigroup for
`Limits(timeout_ms=1)` got the whole search back. A budget that is accepted
and ignored is a false statement about the run.

`@honours_timeout(command, engine)` gives an engine the run's clock for its
duration -- the EARLIER of its own `timeout_ms` and any run deadline already
set (`certo.clock`) -- refuses to start once that has passed, and turns an
`OutOfTime` raised by `tick()` inside a long loop into a TIMEOUT result. An
engine that can say what it DID establish catches the clock itself and
returns that instead (`semigroup` keeps every point it decided).
"""
from __future__ import annotations

import functools
import inspect
import time

from . import clock
from .i18n import t


class OutOfTime(RuntimeError):
    """The run's clock passed during an engine's loop."""


_COUNT = [0]


def tick(every: int = 1024):
    """Call in a hot loop: raises `OutOfTime` once the run's clock has
    passed, looking at the clock every `every` calls."""
    _COUNT[0] += 1
    if _COUNT[0] % every == 0 and clock.expired():
        raise OutOfTime()


def _stopped(command, engine, ms, timeout_ms, before):
    from .status import Result, Status, Verdict

    return Result(command, Status.TIMEOUT, Verdict.INCONCLUSIVE, engine, ms, None,
                  detail=t("engine.budget.before" if before else "engine.budget.stopped",
                           ms=timeout_ms),
                  meta={"stopped_by": "time"})


#: every engine wrapped here, by function -- the index `find` reports from,
#: and what the test that runs each one past its deadline walks
WRAPPED = {}


def honours_timeout(command, engine):
    def deco(fn):
        sig = inspect.signature(fn)

        @functools.wraps(fn)
        def wrapper(*args, **kwargs):
            from .limits import Limits

            try:
                bound = sig.bind_partial(*args, **kwargs).arguments
            except TypeError:
                bound = {}
            lim = bound.get("limits") or Limits()
            secs = lim.timeout_ms / 1000 if lim.timeout_ms else None
            t0 = time.perf_counter()
            with clock.within(secs):
                if clock.expired():
                    return _stopped(command, engine, 0.0, lim.timeout_ms, True)
                try:
                    return fn(*args, **kwargs)
                except OutOfTime:
                    return _stopped(command, engine,
                                    (time.perf_counter() - t0) * 1000,
                                    lim.timeout_ms, False)

        wrapper.honours_timeout = True
        WRAPPED["{}.{}".format(fn.__module__, fn.__name__)] = command
        return wrapper
    return deco
