"""Run a command in this process, without paying for an interpreter.

certo is a CLI, and a CLI costs one Python startup per question. On this
machine that is 1.2 seconds -- `python -c pass` alone, before certo is
imported -- against 70 ms of certo's own. A sweep of 853 linear programs is
two minutes of work behind twenty minutes of starting Python.

That arithmetic is why people leave. A user sweeping 853 graphs, 1992
clique-sums and 180 random chordals went to PuLP/CBC in-process instead, and
the cost was not the time: it was that their fallback worked in FLOATING
POINT, so a ratio came out as `4499996/999999` and a retraction had to be
re-signed with `Fraction`. The exactness certo exists for was lost to a
startup cost that had nothing to do with exactness.

Everything needed was already exported except the one thing that runs:
`certo/__init__.py` gives you every spec type, `Limits`, `Result`,
`Certificate` and `verify`, so you could BUILD a question in-process and CHECK
an answer in-process, and had to shell out to get from one to the other.

    from certo import LPSpec, api

    spec = LPSpec(sense="max", title="w")
    ...
    res = api.run("opt", spec)
    res.meta["objective"]        # '32/3', an exact string
    res.certificate              # the same artefact `--cert` would write

WHAT THIS PROMISES. `run`, `options` and `runnable` are public and will keep
working. The engine modules under `certo.engines` are not: they are reached
through `routing`, and this is the entry point that makes that indirection
somebody else's problem rather than yours.

SELF-CHECK. `run` verifies what it produced, the way the CLI does, and raises
`SelfCheckFailed` rather than returning a certificate that fails its own
verifier -- for SOLVER-FREE certificates only. One whose check calls a solver
again (`unsat_core`, `model`, ...) is returned unchecked, and
`res.meta["self_check"]` is absent rather than "ok"; call `verify` on it when
that matters. It costs 0.7% of an `opt` and it is what caught the defects in
0.11.3. Pass `self_check=False` in a hot loop if you have measured that it
matters; you will be turning off the thing that reads certo's own output.
"""
from __future__ import annotations

import importlib
import inspect

from . import routing
from .status import Result


class SelfCheckFailed(RuntimeError):
    """certo produced a certificate its own verifier rejects.

    This is a bug in certo, never a result about your spec. It carries both
    the `Result` and the `VerifyReport` so a caller that catches it can say
    which check failed.
    """

    def __init__(self, result, report):
        self.result = result
        self.report = report
        failed = [name for name, ok, _ in report.checks if not ok]
        super().__init__(
            "the {} certificate certo just produced fails its own verifier: "
            "{}".format(result.certificate.kind, ", ".join(failed) or "?"))


#: Commands `run` reaches that `routing.RUNNERS` does not carry.
#:
#: RUNNERS is `ask`'s table by definition -- "only the commands `ask` can run
#: with no flags", because guessing a missing piece answers a different
#: question. Here the missing piece is the caller's to supply, so these belong
#: and RUNNERS stays exactly what it says it is.
DECIDED = {
    "range": ("certo.engines.algebra", "variable_range"),
    "audit": ("certo.engines.smt", "audit"),
    "mixed": ("certo.engines.mixed", "mixed"),
    "compose": ("certo.engines.compose", "compose"),
}

#: The decision each of those needs, by keyword. Missing one is an error that
#: names it, rather than a TypeError from four frames inside an engine.
REQUIRED = {"range": ("var",)}

#: Commands that do not run a spec at all, and so are not `run`'s business.
#: `verify` and `load_spec` are already exported from the package; the rest
#: read a directory, the environment or the catalogue. Listed rather than
#: implied, so `tests` can hold `run` to covering everything else.
NOT_FROM_A_SPEC = frozenset({
    "verify", "status", "doctor", "ask", "commands", "repro", "export",
    "ledger", "lint", "enum", "report", "pack", "mcp", "promote",
})


def runnable() -> list:
    """Every command `run` accepts, sorted."""
    # `reduce_parametric` and `sweep_domain` are dispatch keys, not commands:
    # they are what `reduce` and `sweep` become when the spec says so.
    return sorted((set(routing.RUNNERS) | set(DECIDED))
                  - {"reduce_parametric", "sweep_domain"})


def _entry(command: str, spec):
    """The function behind a command, with the same type-aware dispatch `ask`
    uses: a finite domain and a family of graphs are both `sweep` to a reader,
    and one program and a whole family are both `reduce`. Routing on the name
    alone hands a parametric spec to the single-instance engine, which answers
    a weaker question than the one asked.
    """
    key, name = command, type(spec).__name__
    if command == "sweep" and name == "DomainSpec":
        key = "sweep_domain"
    elif command == "reduce" and name == "ParametricSymmetrySpec":
        key = "reduce_parametric"

    where = routing.RUNNERS.get(key) or DECIDED.get(key)
    if where is None:
        if command in NOT_FROM_A_SPEC:
            raise ValueError(
                "`{}` does not run a spec. Use certo.verify for a stored "
                "certificate, or the CLI for the rest.".format(command))
        raise ValueError("no such command: {}. Runnable: {}".format(
            command, ", ".join(runnable())))
    return getattr(importlib.import_module(where[0]), where[1])


def options(command: str, spec=None) -> list:
    """The keyword arguments this command accepts, beyond the spec.

    Derived from the engine's signature, so it cannot drift from what the
    engine takes. `spec` only matters where the dispatch depends on the spec
    type, which is `sweep` and `reduce`.
    """
    fn = _entry(command, spec if spec is not None else object())
    return sorted(p for p, v in inspect.signature(fn).parameters.items()
                  if v.kind in (v.POSITIONAL_OR_KEYWORD, v.KEYWORD_ONLY)
                  and p not in ("spec", "limits", "spec_path")
                  and not p.startswith("_"))    # internal to another engine


def run(command: str, spec, limits=None, *, spec_path=None,
        self_check: bool = True, **kwargs) -> Result:
    """Run one command on one spec, in this process. Returns a `Result`.

    `limits` is a `Limits`, or None for the defaults. `spec_path` stamps the
    certificate with where the spec came from, the way `--cert` does; leave it
    out and the provenance says so rather than inventing a path.

    Anything else is passed to the engine -- `api.options(command)` says what
    each one takes. An unknown keyword is refused by name here rather than
    swallowed, because an option silently ignored is an answer to a different
    question.

    Raises `SelfCheckFailed` if the certificate does not verify; see the
    module docstring.
    """
    missing = [k for k in REQUIRED.get(command, ()) if k not in kwargs]
    if missing:
        raise TypeError("{} needs {}".format(
            command, ", ".join("`{}=`".format(m) for m in missing)))

    spec = routing.prepared(spec)
    wants = routing.SPEC_OF.get(command)
    got = type(spec).__name__
    if wants and wants != "*" and wants != got:
        raise TypeError("{} wants a {}, got a {}".format(command, wants, got))

    fn = _entry(command, spec)
    params = inspect.signature(fn).parameters
    unknown = sorted(set(kwargs) - set(params))
    if unknown:
        raise TypeError("{} does not take {}. It takes: {}".format(
            command, ", ".join(unknown), ", ".join(options(command, spec)) or "-"))

    call = dict(kwargs)
    if "limits" in params:
        call["limits"] = limits
    if spec_path is not None and "spec_path" in params:
        call["spec_path"] = spec_path

    res = fn(spec, **call)

    if res.certificate is not None and spec_path is not None:
        res.certificate.stamp(spec_path)
    if self_check and res.certificate is not None:
        _check(res, limits)

    # The in-process surface is the one a model sweeping a route space uses,
    # so it is the one whose unanswered questions are worth the most. Silent
    # here by design: `run()` returns a Result and prints nothing, ever.
    from . import coverage

    coverage.record(res, "api")
    return res


def _check(res, limits) -> None:
    """The CLI's self-check, with an exception where it has an exit code.

    The CLI prints to stderr and returns 1, and the caller decides. In a
    library the equivalent of "the caller decides" is an exception they can
    catch -- and defaulting to silence would remove the check that found the
    `variable_range` forgery and the zero dual.
    """
    from .certificate import verify

    if not res.certificate.solver_free:
        return          # re-running a search on every call is a cost nobody asked for
    report = verify(res.certificate, limits)
    res.meta["self_check"] = "ok" if report.ok else "FAILED"
    if not report.ok:
        raise SelfCheckFailed(res, report)
