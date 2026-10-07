"""A run that dies or hangs leaves a trace.

Two reports from one user, and three sightings on a loaded machine here: a
`parametric` that sat 70 minutes at 0% CPU on a spec that takes six seconds,
runs that ended with NO output at all and proved on relaunch, a native crash
`0xC0000409`, and two 900-second hangs of examples that take seconds alone.
None reproduced in isolation, and in every one of them the only evidence was
an absence. That is the thing worth fixing first, because it is the thing that
stops any of them being diagnosed:

  * `faulthandler` is ON for every CLI run. A crash inside native code --
    z3, HiGHS, Clarabel, numpy, cddlib -- prints no Python traceback, so the
    process just ends; with it, stderr gets the stack of every thread at the
    moment of death. Measured first: z3 raising and catching its own C++
    exceptions produces no noise.

  * `--deadline SECONDS` (or `CERTO_DEADLINE_S`) bounds the WHOLE run, not one
    solver call. When it passes, every thread's stack goes to stderr -- which
    is the answer to "what was it waiting on" -- and the process exits 2,
    inconclusive, the same code as any other unsettled question. A watchdog
    in Python can only act when it gets the interpreter, and a hang inside a
    native call may never give it back, so `faulthandler`'s own C watchdog
    stands behind it a few seconds later and exits regardless.

  * `--heartbeat SECONDS` (or `CERTO_HEARTBEAT_S`) writes a line to stderr
    every so often, for a driver that wants to tell slow from stuck.

None of this fixes a cause. It makes the next one say where it was.
"""
from __future__ import annotations

import faulthandler
import os
import sys
import threading
import time
from contextlib import contextmanager

#: How long after the deadline the C watchdog takes over, if the Python one
#: never got the interpreter.
GRACE_S = 10

#: How long after the deadline the run has to stop ON ITS OWN -- every
#: engine reads the run clock (`certo.clock`) and ends with TIMEOUT -- before
#: the Python watchdog prints the stacks and exits.
COOPERATE_S = 3

#: The exit code of a run stopped by its deadline: inconclusive, like every
#: other question certo could not settle.
EXIT_DEADLINE = 2


_JOB = []      # the Windows job handle, kept open for the life of the process


def children_die_with_us() -> bool:
    """Children END WITH CERTO -- a `geng`, `cbc`, `drat-trim` or `lake` --
    instead of outliving a deadline. On Windows the process joins a job
    object that kills every member when its last handle closes, which is
    when certo exits, however it exits. Elsewhere the hard stop kills the
    children itself (`_kill_children`). Best effort: a process already in a
    job that forbids nesting stays as it was, and says nothing."""
    if os.name != "nt" or _JOB:
        return bool(_JOB)
    try:
        import ctypes
        from ctypes import wintypes

        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        # Typed, or the pseudo-handle -1 is truncated to 32 bits on a 64-bit
        # Python and every call fails with ERROR_INVALID_HANDLE.
        k32.CreateJobObjectW.restype = wintypes.HANDLE
        k32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
        k32.GetCurrentProcess.restype = wintypes.HANDLE
        k32.SetInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int,
                                                ctypes.c_void_p, wintypes.DWORD]
        k32.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]

        class IO(ctypes.Structure):
            _fields_ = [(n, ctypes.c_ulonglong) for n in (
                "ReadOperationCount", "WriteOperationCount",
                "OtherOperationCount", "ReadTransferCount",
                "WriteTransferCount", "OtherTransferCount")]

        class Basic(ctypes.Structure):
            _fields_ = [("PerProcessUserTimeLimit", ctypes.c_longlong),
                        ("PerJobUserTimeLimit", ctypes.c_longlong),
                        ("LimitFlags", wintypes.DWORD),
                        ("MinimumWorkingSetSize", ctypes.c_size_t),
                        ("MaximumWorkingSetSize", ctypes.c_size_t),
                        ("ActiveProcessLimit", wintypes.DWORD),
                        ("Affinity", ctypes.c_size_t),
                        ("PriorityClass", wintypes.DWORD),
                        ("SchedulingClass", wintypes.DWORD)]

        class Extended(ctypes.Structure):
            _fields_ = [("BasicLimitInformation", Basic), ("IoInfo", IO),
                        ("ProcessMemoryLimit", ctypes.c_size_t),
                        ("JobMemoryLimit", ctypes.c_size_t),
                        ("PeakProcessMemoryUsed", ctypes.c_size_t),
                        ("PeakJobMemoryUsed", ctypes.c_size_t)]

        job = k32.CreateJobObjectW(None, None)
        if not job:
            return False
        info = Extended()
        info.BasicLimitInformation.LimitFlags = 0x2000   # KILL_ON_JOB_CLOSE
        if not k32.SetInformationJobObject(job, 9, ctypes.byref(info),
                                           ctypes.sizeof(info)):
            k32.CloseHandle(job)
            return False
        if not k32.AssignProcessToJobObject(job, k32.GetCurrentProcess()):
            k32.CloseHandle(job)
            return False
        _JOB.append(job)
        return True
    except Exception:  # noqa: BLE001 -- best effort, never a reason to fail
        return False


def _kill_children():
    """POSIX: the direct children, killed at the hard stop. (On Windows the
    job object does it when the process ends.)"""
    if os.name == "nt":
        return
    try:
        import subprocess

        subprocess.run(["pkill", "-KILL", "-P", str(os.getpid())],
                       capture_output=True, timeout=5)
    except Exception:  # noqa: BLE001
        pass


def _seconds(value, env):
    raw = value if value is not None else os.environ.get(env)
    if raw in (None, ""):
        return None
    try:
        s = float(raw)
    except (TypeError, ValueError):
        return None
    return s if s > 0 else None


def enable_crash_traces():
    """`faulthandler` on stderr, once, if it is not already."""
    try:
        if not faulthandler.is_enabled():
            faulthandler.enable(file=sys.stderr, all_threads=True)
    except Exception:  # noqa: BLE001 -- an unusual stderr must not stop a run
        pass


@contextmanager
def watched(command="", deadline=None, heartbeat=None, out=None):
    """Run the body under an optional deadline and heartbeat. Always undone
    on the way out, because the CLI is also called in-process."""
    from .i18n import t

    err = out or sys.stderr
    deadline = _seconds(deadline, "CERTO_DEADLINE_S")
    heartbeat = _seconds(heartbeat, "CERTO_HEARTBEAT_S")
    stop = threading.Event()
    started = time.monotonic()
    threads = []

    if deadline is not None:
        from . import clock

        # The engines stop at the deadline themselves, with TIMEOUT and what
        # they had; the hard stop below is for a call that never returns.
        clock.set_process_deadline(deadline)
        children_die_with_us()

        def expire():
            if stop.wait(deadline + COOPERATE_S):
                return
            try:
                err.write(t("watch.deadline", seconds=_fmt(deadline),
                            command=command or "certo") + "\n")
                err.flush()
                faulthandler.dump_traceback(file=err, all_threads=True)
                err.flush()
                sys.stdout.flush()
            finally:
                _kill_children()
                os._exit(EXIT_DEADLINE)
        th = threading.Thread(target=expire, name="certo-deadline", daemon=True)
        th.start()
        threads.append(th)
        try:
            faulthandler.dump_traceback_later(deadline + COOPERATE_S + GRACE_S,
                                              exit=True, file=err)
        except Exception:  # noqa: BLE001
            pass

    if heartbeat is not None:
        def beat():
            while not stop.wait(heartbeat):
                try:
                    err.write(t("watch.heartbeat", command=command or "certo",
                                seconds=_fmt(time.monotonic() - started)) + "\n")
                    err.flush()
                except Exception:  # noqa: BLE001
                    return
        th = threading.Thread(target=beat, name="certo-heartbeat", daemon=True)
        th.start()
        threads.append(th)

    try:
        yield
    finally:
        stop.set()
        if deadline is not None:
            from . import clock

            clock.set_process_deadline(None)
            try:
                faulthandler.cancel_dump_traceback_later()
            except Exception:  # noqa: BLE001
                pass


def _fmt(seconds):
    return ("{:.0f}".format(seconds) if seconds >= 10
            else "{:.1f}".format(seconds))
