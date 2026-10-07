"""ONE clock for a run, read by every engine that waits.

Three reports said the same thing in different words: a budget bounded a
PHASE, not the call. `--timeout-ms` is handed to each solver call, so a
command that makes forty of them could take forty budgets; the exact LP
reconstruction and the ideal search had clocks of their own only after
0.26.1; and `--deadline`, the one budget that covered the whole run, could
only end it -- every thread's stack on stderr and exit 2 -- because nothing
inside was listening.

This is what they listen to. A run deadline is set once:

  * by `--deadline S` (or `CERTO_DEADLINE_S`) on the command line, for the
    process;
  * by the MCP server for each tool call, in that call's context -- several
    calls run at once in one process, so it is a context variable, not a
    global;

and read everywhere a run can spend time:

  * `Limits.apply_to` caps every z3 call at what is LEFT of the run, so the
    forty solver calls share one budget;
  * the engines with clocks of their own (`ideal`, the exact LP, `profile`,
    CEGIS) stop at whichever comes first, theirs or the run's;
  * long loops (sweeps, branch and bound) ask `expired()` between items.

A run stopped this way ends like any other unsettled question: TIMEOUT,
inconclusive, `stopped_by: deadline`, with whatever it had established. The
hard stop -- stacks and exit -- stays behind it as the backstop for a native
call that never gives the interpreter back.

`--timeout-ms` keeps its meaning: the budget of ONE solver call. A sweep of
a thousand items does not have to fit in ten seconds; a run with a deadline
does have to fit in it.
"""
from __future__ import annotations

import contextvars
import time
from contextlib import contextmanager

_CALL = contextvars.ContextVar("certo_run_deadline", default=None)
_PROCESS = [None]


def deadline():
    """The run's deadline as a `time.monotonic()` value, or None."""
    d = _CALL.get()
    return d if d is not None else _PROCESS[0]


def remaining_s():
    """Seconds left in the run, never negative; None with no deadline."""
    d = deadline()
    return None if d is None else max(0.0, d - time.monotonic())


def expired() -> bool:
    d = deadline()
    return d is not None and time.monotonic() >= d


def cap(own):
    """The earlier of an engine's own deadline and the run's (either may be
    None)."""
    d = deadline()
    if own is None:
        return d
    return own if d is None else min(own, d)


def cap_ms(ms):
    """A per-call budget in ms, cut to what is left of the run; at least 1,
    because 0 means "no limit" to z3."""
    left = remaining_s()
    if left is None:
        return ms
    left_ms = int(left * 1000)
    if not ms:
        return max(1, left_ms)
    return max(1, min(int(ms), left_ms))


def set_process_deadline(seconds):
    """For the CLI: one run per process. None clears it."""
    _PROCESS[0] = None if seconds is None else time.monotonic() + float(seconds)


@contextmanager
def run_deadline(seconds):
    """For one MCP call (or any caller sharing a process): the deadline holds
    in this context and in threads started from it with a copy of it."""
    if seconds is None:
        yield
        return
    token = _CALL.set(time.monotonic() + float(seconds))
    try:
        yield
    finally:
        _CALL.reset(token)
