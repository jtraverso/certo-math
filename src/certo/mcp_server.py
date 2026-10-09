"""MCP server: every command, exposed to the LLM directly.

Three design decisions that matter:

1. CERTIFICATES DO NOT COME BACK IN THE RESPONSE. A DIMACS file with its DRAT
   proof is tens of thousands of characters; putting that in the model's
   context throws the window away and buys nothing, because the model cannot
   verify it by reading it. They are written to disk and the path, kind and
   digest come back. To check one, there is `verify`.

2. SPECS ARE PYTHON AND THEY GET EXECUTED. That is inherent to the DSL. The
   server confines paths and generated files to the workspace, but it is not
   a sandbox: do not point it at third-party specs.

3. `dsl_guide` FIRST. The model cannot write a valid spec without seeing the
   shape. The guide is both a tool and a resource.

Tool names, parameters and descriptions are API surface, like the CLI command
names: they stay in English whatever --lang says. What follows the user's
language is the rendered output of each result.
"""
from __future__ import annotations

import functools
import hashlib
import json
import os
from pathlib import Path
from typing import Any

import anyio
from mcp.server.mcpserver import MCPServer

from . import __version__
from .limits import Limits

INSTRUCTIONS = """\
certo: a laboratory for supporting mathematical proofs, with certificates.

ALWAYS start with `dsl_guide` if you are going to write a spec.

Every command returns a verdict and a certificate saved to disk. The
certificate does not travel in the response: use `verify` with the path you
are given.

Only `unsat` and `sat` are conclusive. `unknown_solver`, `timeout`,
`resource_exhausted` and `out_of_theory` all mean "no answer", each for a
different reason -- none of them means "does not exist".

Mind the scope: `synth` DISCOVERS over a bounded domain, it does not prove a
theorem; `sweep` and `cases` settle a FINITE CASE, not the general statement.

Specs are Python code and are executed when loaded.
"""

DSL_GUIDE = '''\
# The certo DSL

Python as the host language. A .py file with a `spec()` function returning one
of these objects. You can pass the file (`spec_path`) or the code itself
(`spec_source`).

## Spec -> prove / check / core / farkas
    import z3
    from certo import Spec
    def spec():
        a, b = z3.Reals("a b")
        s = Spec(title="optional")
        s.assume("a_pos", a > 0)      # NAMED hypotheses: core and farkas use them
        s.assume("b_pos", b > 0)
        s.claim((a + b) * (a + b) >= 4 * a * b)
        return s

    prove:  negate the claim, look for unsat. PROVED / REFUTED (with a
            counterexample). Z3, complete for real arithmetic: this is the
            tool that DECIDES.
    core:   MUS, which hypotheses are really needed.

    prove, core, farkas and compose all check for a VACUOUS proof: if the
    hypotheses contradict each other, every goal follows and the proof says
    nothing. The verdict stays PROVED -- it really is a proof -- but the
    response and the certificate both say so. Treat it as a bug in the spec.
    farkas: the same proof, but with the REASON attached -- non-negative
            rational multipliers that combine the hypotheses with the negated
            goal until everything cancels. Checked by adding fractions, no
            solver. A hypothesis with multiplier 0 is absent, so this says
            which ones the proof uses. This is Lean's `linarith`, and the
            response carries the tactic line to paste.
            farkas(nonlinear=True) is `nlinarith`: products and squares of the
            hypotheses are added first. HEURISTIC -- finding nothing does not
            mean the claim is false; that is what `prove` is for.

## IdealSpec / SOSSpec / NumberSpec -> ideal, sos, number (no SMT at all)
    from certo import IdealSpec, SOSSpec, NumberSpec
    IdealSpec(variables=["x","y"], equations=[x*x+y*y-1, x-y, x+y-3],
              claim=None)        # None: is the system INCONSISTENT?
    # Cofactors with 1 = sum h_i g_i refute it over C, hence over R, Q and Z.
    # With claim=f it certifies f = sum h_i g_i. Groebner DECIDES membership,
    # so a negative answer is conclusive, not a timeout. Checking a cofactor
    # certificate is expanding a product: no solver, no algebra system.

    SOSSpec(variables=["x","y"], poly=x**4 + y**4 - x**2*y**2)
    # p = sum d_i q_i^2, exact rationals. Searched in floating point, rounded
    # and re-verified exactly. NOT complete: a non-negative polynomial need
    # not be a sum of squares, so nothing found is unknown_solver.

    NumberSpec(n=2**31 - 1, question="prime")   # or "factor"
    # A Pratt tree. Checking it is modular exponentiation and nothing else.

## OrderSpec -> order (does this DECAY in n, or is it Theta(1)?)
    from certo import OrderSpec
    def spec():
        return OrderSpec(
            expression=5*k*W*C*C / (u**3 * d**2 * p**10),
            orders={"k": 0, "W": 2, "C": 1, "u": 0, "d": 2, "p": 0},
            expect="decays",              # optional; without it, it measures
        )
    # A question `prove` CANNOT ask. A term constant in n is not infeasible --
    # it is a feasibility that never improves, so a solver keeps saying "yes,
    # satisfiable", correctly, while the bound never gets better. Invisible to
    # SMT and to a proof assistant alike.
    # orders: the exponent of n per symbol. A missing symbol is an ERROR, not
    # an assumption. Certifies the EXPONENT, never the constant in front.

## BoundSpec -> bounds (numbers, rigorously)
    from certo import BoundSpec
    def spec():
        return BoundSpec(
            value=lambda m: m.e / m.pi,      # m = RIGOROUS constants/functions
            claim=("<", "0.866"),            # against an EXACT rational string
            describe="e / pi",
            prec=64,                         # bits; it doubles until settled
        )
    # m: pi, e, euler, and exp log sqrt sin cos tan asin acos atan sinh cosh
    #    tanh gamma lgamma digamma zeta erf erfc. m("1/3") or m(7) builds a
    #    number EXACTLY; a Python float like 0.1 RAISES, because 0.1 is not
    #    one tenth and the enclosure would be rigorous about the wrong number.
    # claim: ("<", r) ("<=", r) (">", r) (">=", r) ("!=", r) ("in", lo, hi),
    #    or leave it out to MEASURE: the certificate records the enclosure.
    # An enclosure can never prove a quantity EQUALS something, only that it
    # differs; and resource_exhausted means "did not settle it", not "false".

## ProofSpec -> compose (the lemmas AND the join between them)
    import z3
    from certo import ProofSpec, Spec
    def spec():
        p = ProofSpec(title="the theorem")
        p.assume("n_ge_6", n >= 6)              # hypothesis of the THEOREM
        p.lemma("arith", proves=sub_spec)       # discharged now, by `prove`
        p.lemma("tight", proves=other, via="nlinarith")
        p.lemma("finite", certificate="certs/drat-1a2b.json",
                states=(R33 <= 6),              # what it licenses you to use
                bridge="the DRAT proof closes the K6 encoding; reading that "
                       "as R(3,3) <= 6 is what the encoding means")
        p.conclude(theorem)
        return p

    A lemma given by `proves=` is DISCHARGED and LINKED: compose checks that
    what its certificate closes entails the statement used downstream. If it
    does not, nothing is emitted -- that gap is the whole reason to compose
    rather than to keep certificates in a folder.

    A lemma given by `certificate=` is a BRIDGE: verified on its own, but the
    step from "this CNF is unsatisfiable" or "these 156 graphs all satisfy P"
    to a formula cannot be checked by anything. Declare it in `bridge=`; it is
    reported by name every time the proof is verified.

    The response also says which lemmas the theorem actually NEEDED.

## SynthSpec -> synth (CEGIS: THERE EXISTS obj, FOR ALL inputs)
    import z3
    from certo import SynthSpec
    def spec():
        a, b = z3.Ints("a b")             # what we are looking for
        x = z3.Int("x")                   # universally quantified
        return SynthSpec(
            impl_vars=[a, b], input_vars=[x], helper_vars=[],
            impl_constraints=z3.And(a >= 0, a <= 40, b >= 0, b <= 40),
            behavior=z3.And(x >= 1, x <= 20),   # BOUNDED search domain
            correctness=(a * x + b >= x * x),
            # For `synth(prove_candidate=True)`: the GENERAL statement. It
            # usually changes both the domain AND the sort (search over
            # bounded integers, prove over the reals, which is decidable).
            universal=lambda vals: Spec().claim(...),   # full control
            # or, the simple case:  universal_behavior=<expr replacing behavior>
        )

## InductSpec -> induct (base cases + a step, and the join between them)
    from certo import InductSpec, Spec
    k = z3.Int("k")
    def spec():
        step = Spec()
        step.assume("k_ge_3", k >= 3)        # a FREE k: valid for every k
        step.assume("P_k", <property at k>)
        step.claim(<property at k+1>)
        return InductSpec(k0=3, base_upto=8,
                          base=lambda j: <Spec|SweepSpec|DomainSpec|cert path>,
                          step=step, step_from=3,
                          bridge="how a finite check becomes P(k)")
    # Z3 has NO induction schema. The principle is applied by the tool and
    # recorded in the certificate; it is not a solver result. What is checked:
    # the base cases are exactly k0..base_upto with no gap, the step starts no
    # later than the base ends, and the step certificate really entails the
    # step statement. The first two are where induction proofs break.

## SetFamily -> the native combinatorial type (structures.py)
    from certo import SetFamily
    f = SetFamily(7, [(0,1,2), (0,3,4), ...])     # hypergraph, design, code...
    f.is_design(2, 1)  f.is_regular(3)  f.is_uniform(3)  f.intersecting()
    SetFamily.all_families(n, k, size)            # the domain to sweep
    # It supplies key(), canonical() and reductions() itself, so a DomainSpec
    # over these can leave key, canonicalize="auto" and reduce="auto".
    # canonical() is EXACT and RAISES on a family too symmetric to do exactly,
    # rather than returning a cheaper invariant that could merge two orbits.

## LPSpec -> opt, and `mixed` when some variables are discrete
    lp.variable("y", kind="binary")     # or kind="integer"
    lp.variable("q")                    # continuous, the default
    # `integer=True` on the SPEC makes every variable integer, which is the
    # wrong shape for a design whose discrete part chooses a structure and
    # whose continuous part packs inside it. Declare kinds per variable and
    # use `mixed`, which certifies the construction and says plainly that it
    # does not claim MILP optimality.

## LPSpec -> opt (the certificate is the DUAL)
    from certo import LPSpec
    def spec():
        lp = LPSpec(sense="max")          # variables >= 0, mandatory
        lp.variable("x"); lp.variable("y")
        lp.objective({"x": 3, "y": 5})
        lp.constraint({"x": 1, "y": 1}, "<=", 10, name="capacity")
        return lp

## CNF / CNFSpec -> cases (DRAT proof) and shrink (MUS)
    from itertools import combinations
    from certo import CNF, CNFSpec
    def spec():
        cnf = CNF(title="R(3,3) on K6")
        def x(i, j): return cnf.var("e%d_%d" % (min(i,j), max(i,j)))
        for t in combinations(range(6), 3):
            a, b, c = x(t[0],t[1]), x(t[0],t[2]), x(t[1],t[2])
            cnf.add(-a, -b, -c); cnf.add(a, b, c)
        return CNFSpec(cnf=cnf)
    # helpers: cnf.at_most_one(lits), cnf.exactly_one(lits), cnf.lex_leq(xs, ys),
    #          cnf.break_vertex_symmetry(edge_var_fn, n)

## SweepSpec -> sweep (predicate over a whole family) and shrink (minimise)
    from certo import Outcome, SweepSpec
    from certo.graphs import is_chordal
    def spec():
        return SweepSpec(n=6, filters=["connected"], predicate=is_chordal)

    # A BARE BOOL predicate makes the sweep REPRODUCIBLE, not certified: the
    # certificate records the verdict vector so `verify` can re-run the
    # predicate and confirm it answers the same, which is NOT the same as
    # establishing those answers are right. `predicate_level` in the response
    # says which of the three you got: certified / reproducible / recorded.
    # The predicate may return an Outcome instead of a bool:
    #   Outcome(ok=False, cert=<Certificate>, detail="...", value=Fraction(25,27))
    #   ok=None  -> inconclusive (counted apart, does not sink the sweep)
    #   cert=... -> makes the sweep CITABLE; verify checks them in cascade
    #   value=...-> the magnitude to calibrate
    # CALIBRATION: SweepSpec(n=6, collect=lambda g: ratio(g), worst="min")
    # returns min, max, mean and the extremes WITH their graph. `predicate` is
    # optional: you can measure without refuting anything. Use Fraction so the
    # statistics stay exact.
    # filters: connected, chordal, triangle_free, k4_free, regular,
    #          has_triangle, min_degree=K, max_degree=K, edges=K
    #          (a callable of your own works too)
    # Graph: .n .m .edges() .neighbors(v) .degree(v) .has_edge(i,j) .to_graph6()

## DomainSpec -> sweep and shrink over ANY finite domain
    from certo import DomainSpec
    def spec():
        return DomainSpec(
            items=[(s, r) for s in range(2, 8) for r in range(2, 8)],
            predicate=lambda p: holds(*p),
            key=lambda p: "s=%d,r=%d" % p,       # stable id for the certificate
            reduce="auto",                       # or a callable, for shrink
            canonicalize=lambda p: tuple(sorted(p)),   # the symmetry, optional
        )
    # With `canonicalize`, a REFUTED sweep reports labelled count, orbit count
    # and a representative per orbit -- 1400 counterexamples that are four
    # objects relabelled is one answer told 1400 times. Every item is still
    # evaluated; the quotient happens on the way out.
    # reduce: "auto" | sets | sequences | decrement | graphs | masks, or your
    # own. "auto" refuses on a type it does not know rather than inventing a
    # reduction that would make a witness minimal for the wrong relation.

## BisectSpec -> bisect (a constant's threshold)
    from certo import BisectSpec
    def spec():
        def build(t):                     # returns a Spec or a CNFSpec
            ...
        return BisectSpec(build=build, lo=0, hi=10, direction="min_true",
                          integer=False, tol=1e-6)
    # direction="min_true": holds for LARGE t -> look for the smallest t.
    # With a CNFSpec, "holds" = UNSAT = no counterexample exists.
    # ASSUMES MONOTONICITY in t. It checks the endpoints and warns if they
    # do not line up.

## NonnegSpec -> nonneg (a polynomial >= 0 on a box)
    from fractions import Fraction
    from certo import NonnegSpec
    from certo.polynomials import Poly
    x = Poly.var(("x",), "x")                    # `**`, `-`, ints work on Poly
    def spec():
        return NonnegSpec(poly=Fraction(3, 10) - x, box={"x": (0, Fraction(1, 2))},
                          region=[("r", Fraction(3, 40) - x**2)])   # g >= 0
    # PROVED: Bernstein coefficients. REFUTED: a point and its exact value.
    # A region writes an algebraic endpoint exactly: [0, sqrt(3/40)] here.
    # An OPEN end is a ray, and rays mix with bounded sides:
    #   box={"R": (0, None), "x": (0, 1)}   # R >= 0, 0 <= x <= 1
    # selects the shift test (v -> lo + u, the ceiling x <= 1 used as a
    # multiplier); meta["method"] says which ran: "bernstein" or "shift".

## AtlasSpec -> atlas (N box certificates, ONE statement)
    AtlasSpec(domain={"p": (0, 1)}, claim=("<=", T), pieces=["box1.json", ...])
    # ONE program for every piece. A piece proving its own bound B counts
    # where T - B >= 0 on its box. `region=` cuts the domain (scope).

## PinSpec -> pin (cp(G) = X, from both sides)
    PinSpec(edges=E, max_size=3, upper=CoverSpec(..., cliques=True),
            lower=CliqueLPSpec(edges=E, problem="partition",
                               weight={"constant": 1}, max_size=3))
    # Both halves must be about THE SAME edges. A lower bound from your own
    # LP (`opt` with round=True) needs assumption="why it bounds cp", and is
    # then RELATIVE.

Many small specs: `batch(command, directory)` runs them all in one process.
`opt` takes round=True (integer optimum <= floor(LP)) and cuts="clique".

## Limits (every command)
    timeout_ms, rlimit (z3's deterministic work unit), conflict_budget (SAT),
    max_iterations (synth). Determinism comes from rlimit/conflict_budget,
    not from the clock.
'''


# ---------------------------------------------------------------------------
# workspace
# ---------------------------------------------------------------------------


def _workspace() -> Path:
    p = Path(os.environ.get("CERTO_WORKSPACE", Path.cwd())).resolve()
    p.mkdir(parents=True, exist_ok=True)
    (p / "certs").mkdir(exist_ok=True)
    (p / "specs").mkdir(exist_ok=True)
    return p


def _resolve(path: str) -> Path:
    """Confine the path inside the workspace."""
    ws = _workspace()
    p = (ws / path).resolve() if not Path(path).is_absolute() else Path(path).resolve()
    if ws not in p.parents and p != ws:
        raise ValueError(
            "path outside the workspace ({}): {}".format(ws, path))
    return p


def _spec_file(spec_path: str | None, spec_source: str | None) -> Path:
    if (spec_path is None) == (spec_source is None):
        raise ValueError("give exactly one: spec_path or spec_source")
    if spec_path is not None:
        p = _resolve(spec_path)
        if not p.exists():
            raise FileNotFoundError("spec file does not exist: " + str(p))
        return p
    digest = hashlib.sha256(spec_source.encode()).hexdigest()[:12]
    p = _workspace() / "specs" / "inline_{}.py".format(digest)
    p.write_text(spec_source, encoding="utf-8")
    return p


def _limits(timeout_ms=10_000, rlimit=20_000_000, conflict_budget=1_000_000,
            max_iterations=10_000) -> Limits:
    return Limits(timeout_ms=timeout_ms, rlimit=rlimit,
                  conflict_budget=conflict_budget, max_iterations=max_iterations)


# ---------------------------------------------------------------------------
# summary: what DOES come back to the model
# ---------------------------------------------------------------------------

_CAP = 10
_BIG = ("trace", "counterexamples", "graph6", "witness", "solution",
        "blocked", "errors", "describe")


def _trim(meta: dict) -> dict:
    out = {}
    for k, v in meta.items():
        if k == "solution" and isinstance(v, dict):
            nz = {a: b for a, b in v.items() if b}
            out[k] = dict(list(nz.items())[:_CAP])
            if len(nz) > _CAP:
                out[k + "_omitted"] = len(nz) - _CAP
        elif k in _BIG and isinstance(v, (list, dict)):
            items = list(v.items()) if isinstance(v, dict) else v
            out[k] = dict(items[:_CAP]) if isinstance(v, dict) else items[:_CAP]
            if len(items) > _CAP:
                out[k + "_omitted"] = len(items) - _CAP
        elif k == "proof_check" and isinstance(v, dict):
            out[k] = {c: {"ok": r.get("ok"), "detail": r.get("detail")}
                      for c, r in v.items()}
        else:
            out[k] = v
    return out


def _runtime() -> dict:
    import sys
    from pathlib import Path

    from . import __file__ as pkg

    return {"python": sys.executable, "certo": str(Path(pkg).parent)}


def _scope(res) -> list:
    from .scope import scope_of

    return scope_of(res.certificate)


def _emit(res, save_cert: bool = True, spec_file=None) -> dict:
    """Render a Result for the model, stamping provenance on the way out.

    Stamping here rather than in each tool: without it a certificate produced
    over MCP carries no spec path, so `ledger verify` cannot find what made it
    and a sweep cannot be replayed -- it silently drops from `reproducible` to
    `recorded` between the run and its own verification.
    """
    if spec_file is not None and res.certificate is not None:
        from . import card as _card

        _card.attach(res.certificate, spec_file)
        res.certificate.stamp(spec_file)

    # Nothing may be printed here -- stdout is the protocol -- so the coverage
    # log is written and not announced. `certo doctor` is where a model or a
    # person finds out it exists.
    from . import coverage

    coverage.record(res, "mcp")

    from . import __version__

    out: dict[str, Any] = {
        # The server's OWN version. After a `pip install` a running server
        # keeps the old code until the client reconnects, and results from
        # two versions mixed silently; now every answer says which one.
        "certo_version": __version__,
        # WHICH certo answered: the interpreter and the package it imported.
        # A user's PATH and MCP server ran 0.24.0 while PyPI had 0.25.0, and
        # another interpreter on the same machine imported older code; the
        # version alone does not say where it came from.
        "runtime": _runtime(),
        "command": res.command,
        "verdict": res.verdict.value,
        "status": res.status.value,
        "conclusive": res.status.conclusive,
        "detail": res.detail,
        # What the claim is restricted to, beside it rather than buried in
        # the certificate: a box, a column family, a finite case, bridges.
        "scope": _scope(res),
        "engine": res.engine,
        "elapsed_ms": round(res.elapsed_ms, 1),
        "meta": _trim(res.meta),
    }
    # OLD CODE, said out loud: the package on disk is newer than what this
    # server loaded, so these results are the old version's.
    from . import mcpctl
    from .i18n import t as _t

    old = mcpctl.stale()
    if old:
        out["stale"] = True
        out["stale_note"] = _t("mcp.stale", installed=old[0], loaded=old[1])
    # A vacuous proof looks exactly like a good one in a summary, so it does
    # not get to hide inside `meta`.
    if res.meta.get("vacuous"):
        out["vacuous"] = True
    # Same reason: a sweep that establishes nothing about its predicate must
    # not summarise as a plain PROVED.
    if res.meta.get("level"):
        out["predicate_level"] = res.meta["level"]
    if res.certificate is None:
        out["certificate"] = None
        out["certificate_note"] = "no certificate: nothing to audit here"
        return out
    c = res.certificate
    info = {"kind": c.kind, "solver_free": c.solver_free,
            "digest": c.digest(), "note": c.note}
    if save_cert:
        p = _workspace() / "certs" / "{}-{}.json".format(res.command, c.digest())
        p.write_text(c.to_json(), encoding="utf-8")
        info["path"] = str(p.relative_to(_workspace())).replace("\\", "/")
        info["verify_with"] = "verify(certificate_path='{}')".format(info["path"])
    out["certificate"] = info
    return out


_HINTS = (
    ("does not define a spec",
     "your file must define `def spec():` returning one of the DSL objects"),
    ("expected",
     "you are calling the wrong command for that spec type; see dsl_guide"),
    ("needs",
     "you are calling the wrong command for that spec type; see dsl_guide"),
    ("outside the workspace",
     "paths are relative to the workspace and cannot escape it"),
    ("spec file does not exist",
     "write the file first, or pass the code in spec_source"),
    ("exactly one",
     "give spec_path OR spec_source, not both and not neither"),
    ("unknown filter",
     "valid filters: connected, chordal, triangle_free, k4_free, regular, "
     "has_triangle, min_degree=K, max_degree=K, edges=K"),
    ("negative lower bound",
     "the dual certificate requires variables >= 0; reformulate the LP"),
    ("universal obligation",
     "add universal= or universal_behavior= to the SynthSpec; see dsl_guide"),
)


def _emit_f(f, res):
    """`_emit` with the spec file, for the tools that return in one line."""
    return _emit(res, spec_file=f)


def _hint(e: Exception) -> str:
    msg = str(e).lower()
    for needle, hint in _HINTS:
        if needle in msg:
            return hint
    if isinstance(e, (SyntaxError, NameError, ImportError)):
        return "your spec does not even run; check dsl_guide and the imports"
    return "see dsl_guide"


import contextvars as _contextvars
import time


def _tr(key, **kw):
    from .i18n import t as _t

    return _t(key, **kw)


#: The id of the `_off` call made by the tool running in this context.
_CURRENT = _contextvars.ContextVar("certo_mcp_call", default=None)

#: Tools that do no solving: answered even with the breaker open, so a
#: client can still find out what is going on.
_LIGHT = {"commands", "find", "dsl_guide", "doctor", "mcp", "status"}


def _guard(fn):
    """Return the error as data, not as an exception.

    The SDK turns any exception into "Error executing tool X" and swallows the
    reason; a model reading that cannot fix its spec. This way it sees what
    happened and what to correct.
    """
    @functools.wraps(fn)
    async def wrapper(*a, **kw):
        from . import clock

        # THE CIRCUIT BREAKER. Calls the watchdog gave up on may still be
        # running -- a thread cannot be stopped -- and past a few of them the
        # server is spending its cores on answers nobody will read.
        alive = _abandoned_alive()
        if len(alive) >= BREAKER_AT and fn.__name__ not in _LIGHT:
            return {"ok": False, "error_type": "CircuitOpen",
                    "error": _tr("mcp.breaker", n=len(alive)),
                    "hint": _tr("mcp.breaker.hint")}
        # Every spec any tool loads -- including one a certificate names in
        # its payload, several calls deep -- stays inside the workspace, for
        # the duration of the call.
        before = os.environ.get("CERTO_SPEC_ROOT")
        os.environ["CERTO_SPEC_ROOT"] = str(_workspace())
        seconds = _call_seconds()
        token = _CURRENT.set(None)
        try:
            # THE WATCHDOG. The run deadline is in this call's context, so
            # every engine stops at it; past it plus a grace, the client is
            # answered without the result.
            with clock.run_deadline(seconds):
                out = None
                with anyio.move_on_after(seconds + CALL_GRACE_S) as scope:
                    out = await fn(*a, **kw)
                if scope.cancelled_caught:
                    cid = _CURRENT.get()
                    if cid is not None and cid in _RUNNING:
                        _ABANDONED.add(cid)
                    out = {"ok": False, "status": "timeout",
                           "stopped_by": "watchdog",
                           "error": _tr("mcp.watchdog", tool=fn.__name__,
                                        seconds=int(seconds + CALL_GRACE_S))}
        except Exception as e:  # noqa: BLE001
            out = {"ok": False, "error_type": type(e).__name__,
                   "error": str(e), "hint": _hint(e)}
        finally:
            _CURRENT.reset(token)
            if before is None:
                os.environ.pop("CERTO_SPEC_ROOT", None)
            else:
                os.environ["CERTO_SPEC_ROOT"] = before
        # A server older than what is installed answers every call, so every
        # answer says so -- FIRST, where it is read. After a `pip install` the
        # running process keeps the old code until the client restarts it.
        stale = _stale_warning()
        if stale and isinstance(out, dict):
            out = {"WARNING": stale, **out}
        return out

    return wrapper


def _stale_warning(running_file=None, running=None, installed=None):
    """The warning, when the code this process runs is not the version
    installed on disk; None otherwise. Read every call: the install can
    change under a long-running server at any time. The arguments exist for
    the tests; a server passes none."""
    running = running or __version__
    try:
        from importlib.metadata import distribution
        from pathlib import Path

        if running_file is None:
            from . import __file__ as running_file

        # Only when THIS process imported an INSTALLED package: code run
        # from a checkout is not a stale server, and a checkout can carry
        # metadata of its own naming some old version (this one says 0.12.1).
        here = Path(running_file).resolve().parts
        if not any(part.lower() in ("site-packages", "dist-packages")
                   for part in here):
            return None
        installed = installed or distribution("certo-math").version
    except Exception:  # noqa: BLE001 -- not installed, or no metadata
        return None
    if installed == running:
        return None
    return _t_stale(running=running, installed=installed)


def _t_stale(**kw):
    from .i18n import t as _t

    return _t("mcp.stale_server", **kw)


#: Seconds a tool call may take, all of it: the RUN deadline every engine
#: reads (`certo.clock`), so a call ends with TIMEOUT and what it had rather
#: than holding the client. `CERTO_MCP_CALL_S` changes it.
CALL_S = 600.0

#: After the deadline, how long the call has to come back on its own before
#: the client is answered without it.
CALL_GRACE_S = 15.0

#: Calls abandoned and still running before new heavy calls are refused: a
#: thread cannot be killed, and each one keeps its memory and a core.
BREAKER_AT = 2

_RUNNING: dict = {}     # call id -> (tool, thread, started)
_ABANDONED: set = set()


def _call_seconds() -> float:
    try:
        return float(os.environ.get("CERTO_MCP_CALL_S") or CALL_S)
    except ValueError:
        return CALL_S


def _abandoned_alive() -> list:
    """The abandoned calls whose threads are still running."""
    for cid in list(_ABANDONED):
        if cid not in _RUNNING:
            _ABANDONED.discard(cid)
    return [cid for cid in _ABANDONED if cid in _RUNNING]


async def _off(fn, *a, **kw):
    """Off the protocol thread: solving can take a while. Registered while it
    runs, so the watchdog can tell an abandoned call that is still working
    from one that finished; abandoned on cancel, because a thread cannot be
    stopped and the client must not wait for it."""
    import threading

    cid = object()

    def run():
        _RUNNING[cid] = (getattr(fn, "__name__", "?"), threading.current_thread(),
                         time.monotonic())
        try:
            return fn(*a, **kw)
        finally:
            _RUNNING.pop(cid, None)

    _CURRENT.set(cid)
    return await anyio.to_thread.run_sync(run, abandon_on_cancel=True)


# ---------------------------------------------------------------------------
# servidor
# ---------------------------------------------------------------------------

mcp = MCPServer(name="certo", version=__version__, instructions=INSTRUCTIONS)


# --- prompts: ready instructions the client offers the model -----------------
#
# A model using certo for the first time writes the spec wrong more often
# than the mathematics. Each prompt is a short route -- find, guide, lint,
# run, verify -- and its spec's fields are read from the discovery index, so
# the prompt cannot drift from the code the way a hand-written guide did.


#: Specs built by calling methods rather than by setting fields.
_BUILDERS = ("variable", "objective", "constraint", "assume", "claim", "conclude")


def _fields_of(spec_name: str) -> str:
    import inspect

    import certo

    from . import discovery

    cls = getattr(certo, spec_name, None)
    methods = [n for n in _BUILDERS if cls is not None and callable(getattr(cls, n, None))]
    if methods:
        # A builder: its METHODS are the interface; its fields are state.
        rows = []
        for n in methods:
            fn = getattr(cls, n)
            sig = str(inspect.signature(fn)).replace("(self, ", "(").replace("(self)", "()")
            doc = (inspect.getdoc(fn) or "").split("\n")[0][:100]
            rows.append("  .{}{}{}".format(n, sig, "  -- " + doc if doc else ""))
        return "\n".join(rows)
    c = discovery.contract(spec_name) or {}
    rows = ["  {}{}: {}".format(f["field"],
                                "" if f.get("default") is None
                                else " = " + str(f["default"]),
                                (f.get("summary") or "")[:110])
            for f in c.get("fields") or []
            if f["field"] not in ("title",)]
    return "\n".join(rows)


def _route(command: str, spec_name: str, goal: str, task: str, extra: str = "") -> str:
    return "\n".join([
        "Use certo to {} -- with a certificate, not an estimate.".format(goal),
        "",
        "The problem: {}".format(task or "(describe it, then follow the steps)"),
        "",
        "1. Write a spec file in the workspace defining `def spec():` that "
        "returns a {}, written with:".format(spec_name),
        _fields_of(spec_name),
        "2. Call `lint` on it and fix every error before running anything.",
        "3. Call `{}` (or `run` with command='{}') on it.".format(command, command),
        "4. Call `verify` on the certificate path it returns. Read `degree`: "
        "`complete` is checked by exact arithmetic; anything else says what "
        "was not. Read `scope`: what the claim is restricted to.",
        "5. Report the verdict, the scope and the certificate path. Do not "
        "report an `unknown`, `timeout` or `inconclusive` as a negative.",
    ] + ([extra] if extra else []))


@mcp.prompt(name="first-spec", description=(
    "Start here: find what certo does for a problem, then write, lint, run "
    "and verify the spec."))
def prompt_first_spec(problem: str = "") -> str:
    return "\n".join([
        "Use certo for this problem, with a certificate: {}".format(problem or "(state it)"),
        "",
        "1. Call `find` with what you need in plain words; read the top "
        "results and `find(exact=...)` the one that fits.",
        "2. Call `dsl_guide` for how that spec is written.",
        "3. Write the spec, `lint` it, run its command, `verify` the certificate.",
        "4. Report the verdict, its `scope` and `degree`, and the certificate path.",
    ])


@mcp.prompt(name="certify-lp", description=(
    "Optimise a linear program and certify the optimum exactly (primal and "
    "dual in rationals), refusing a floating-point answer."))
def prompt_certify_lp(problem: str = "") -> str:
    return _route("opt", "LPSpec", "optimise a linear program exactly", problem,
                  "Pass exact_required=true to `opt`: a floating-point fallback "
                  "is then refused instead of returned. If you already know the "
                  "optimum in rationals, pass primal={var: 'p/q'} to certify it.")


@mcp.prompt(name="prove-polynomial-nonneg", description=(
    "Show a polynomial is >= 0 on a box, a ray, or the part a region cuts -- "
    "or find the point where it fails."))
def prompt_nonneg(problem: str = "") -> str:
    return _route("nonneg", "NonnegSpec", "show a polynomial is non-negative", problem,
                  "A box entry (lo, None) is a ray; an algebraic endpoint is a "
                  "region condition g >= 0, written exactly, not a rational cut.")


@mcp.prompt(name="assign-with-hall", description=(
    "Assign items to receivers under capacities, with a Hall set proving no "
    "larger assignment exists."))
def prompt_assign(problem: str = "") -> str:
    return _route("assign", "AssignmentSpec",
                  "place items on the receivers they are allowed, as many as possible",
                  problem)


@mcp.resource("certo://dsl", mime_type="text/markdown",
              description="certo DSL reference")
def dsl_resource() -> str:
    return DSL_GUIDE


@mcp.tool(description="DSL reference. Read this BEFORE writing a spec.")
def dsl_guide() -> str:
    # The hand-written guide, then every spec, field and flag DERIVED from
    # the code: the guide lagged ParametricSpec and AtlasSpec for releases.
    from . import discovery

    return DSL_GUIDE + discovery.guide_appendix()


def _spec_tool(engine_call, expected=None):
    async def run(spec_path=None, spec_source=None, timeout_ms=10_000,
                  rlimit=20_000_000, **kw):
        from .spec import load_spec

        f = _spec_file(spec_path, spec_source)
        obj = await _off(load_spec, f, expected)
        lim = _limits(timeout_ms, rlimit, kw.pop("conflict_budget", 1_000_000),
                      kw.pop("max_iterations", 10_000))
        return _emit_f(f, await _off(engine_call, obj, lim, **kw))

    return run


@mcp.tool(description=(
    "Prove the claim of a Spec: negate it and look for unsat. Returns PROVED "
    "with the unsat core (which hypotheses were used), or REFUTED with a "
    "counterexample that verifies without a solver."))
@_guard
async def prove(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 10_000, rlimit: int = 20_000_000,
                drat: bool = False) -> dict:
    from .engines import smt
    from .spec import Spec

    return await _spec_tool(smt.prove, Spec)(spec_path, spec_source,
                                             timeout_ms, rlimit, drat=drat)


@mcp.tool(description=(
    "Satisfiability of a Spec's hypotheses plus claim. SAT returns a model; "
    "UNSAT returns the core that explains it. Set hypotheses_only=true to ask "
    "the question people actually reach for: IS THIS REGIME NON-EMPTY? It "
    "drops the claim, returns a model when the hypotheses hold together, and "
    "the MINIMAL CLASH when they do not. Asking it by writing claim(False) "
    "instead returns unsat for every regime, empty or not."))
@_guard
async def check(spec_path: str | None = None, spec_source: str | None = None,
                hypotheses_only: bool = False, integers: bool = False,
                regime: str | None = None,
                timeout_ms: int = 10_000, rlimit: int = 20_000_000) -> dict:
    from .engines import smt
    from .spec import Spec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), Spec)
    res = await _off(smt.check, spec, _limits(timeout_ms, rlimit),
                     hypotheses_only, integers, regime)
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "MUS over a Spec's hypotheses: which are actually needed and which are "
    "redundant. This is the tool for simplifying a proof. Given a MultiSpec "
    "it returns the hypothesis-by-goal TABLE instead: which hypotheses each "
    "goal needs, which is what decides how small a Lean interface can be."))
@_guard
async def core(spec_path: str | None = None, spec_source: str | None = None,
               timeout_ms: int = 10_000, rlimit: int = 20_000_000) -> dict:
    from .engines import smt
    from .spec import MultiSpec, Spec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f)
    lim = _limits(timeout_ms, rlimit)

    if isinstance(sp, MultiSpec):
        res = await _off(smt.core_matrix, sp, lim)
        out = _emit(res, spec_file=f)
        out["table"] = res.meta.get("table")
        out["never_used"] = res.meta.get("never_used")
        return out
    if not isinstance(sp, Spec):
        raise TypeError("core needs a Spec or a MultiSpec; spec() returned "
                        + type(sp).__name__)
    return _emit_f(f, await _off(smt.core, sp, lim))


@mcp.tool(description=(
    "Does a term DECAY in a parameter, or is it Theta(1)? Substitute "
    "asymptotic magnitudes -- d is about n^2, C about n -- and read off the "
    "leading exponent. This asks a question `prove` CANNOT: a term constant "
    "in n is not an infeasibility, it is a feasibility that never improves, "
    "so a solver asked 'is this satisfiable' says yes forever and correctly "
    "while the bound it sits in never gets better. That class of bug is "
    "invisible to an SMT solver and to a proof assistant alike. Orders are "
    "given per symbol ({'d': 2} for n^2, 0 for a constant); a symbol with no "
    "entry is an ERROR, not an assumption. It certifies the EXPONENT, never "
    "the constant in front of it. Division by a SUM is refused, because its "
    "order depends on which term dominates."))
@_guard
async def order(spec_path: str | None = None, spec_source: str | None = None,
                expect: str | None = None, timeout_ms: int = 20_000) -> dict:
    from .engines import order as od
    from .spec import OrderSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, OrderSpec)
    if expect:
        sp.expect = expect
    res = await _off(od.order, sp, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    for k in ("degree", "behaviour", "cancelled", "leading"):
        out[k] = res.meta.get(k)
    return out


@mcp.tool(description=(
    "Settle a NUMERIC inequality rigorously: e, pi, log, gamma, zeta and "
    "friends, with interval/ball arithmetic. Every operation returns an "
    "enclosure that provably contains the true value, so an inequality that "
    "holds for the whole enclosure holds for the number -- which is what a "
    "float computation can never claim. The enclosure comes back as EXACT "
    "rationals. Precision is the work budget: it doubles until the enclosure "
    "settles the claim, and running out is reported as resource_exhausted, "
    "meaning THIS DID NOT SETTLE IT, never 'it is false'. Use it whenever a "
    "proof needs 'this constant is below 0.4' and the constant is not "
    "algebraic; `prove` and `farkas` cannot see transcendental functions at "
    "all. Python floats in the expression are REFUSED, because a float is not "
    "the decimal it is written as."))
@_guard
async def bounds(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 30_000, prec: int = 0,
                 max_prec: int = 0) -> dict:
    from .engines import bounds as bd
    from .spec import BoundSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, BoundSpec)
    if prec:
        sp.prec = prec
    if max_prec:
        sp.max_prec = max_prec
    res = await _off(bd.bounds, sp, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    for k in ("lo", "hi", "width", "prec", "backend"):
        out[k] = res.meta.get(k)
    return out


@mcp.tool(description=(
    "A MIXED design: a discrete skeleton found by search, with the continuous "
    "part certified exactly. This is NOT MILP optimality and does not claim "
    "to be. CBC chooses the discrete structure (uncertified); the assignment "
    "is then rounded and CHECKED exactly, the residual LP over the continuous "
    "variables is solved with an exact rational dual, and every original "
    "constraint is re-checked at the full point. Use it for EXISTENCE proofs, "
    "where exhibiting a construction that reaches a target is the whole job. "
    "The spec declares kinds per variable: lp.variable('y', kind='binary') "
    "next to lp.variable('q'). Three numbers come back and they differ: what "
    "the design achieves, the conditional optimum given that skeleton, and "
    "the relaxation bound over all skeletons -- and if the first meets the "
    "third, global optimality is certified for free."))
@_guard
async def mixed(spec_path: str | None = None, spec_source: str | None = None,
                target: str | None = None, timeout_ms: int = 120_000,
                explore: bool = False, prove_optimal: bool = False,
                max_nodes: int = 5000, wall_timeout_ms: int | None = None,
                freeze: dict | None = None) -> dict:
    """`prove_optimal` is branch and bound to a certified integer optimum
    (`max_nodes`, `wall_timeout_ms`); `freeze` is a discrete assignment found
    elsewhere, {variable: value}, whose continuous part is certified."""
    import dataclasses

    from .engines import mixed as mx
    from .packing import PackingSpec
    from .spec import LPSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f)
    if type(sp).__name__ == "HypergraphSpec":
        sp = sp.to_lp()
    if isinstance(sp, PackingSpec):
        # As the CLI does: a packing whose items are whole-or-nothing IS a
        # mixed design. The tool refused one the command accepted.
        sp = dataclasses.replace(sp, integer=sp.integer or True).to_lp()
    elif not isinstance(sp, LPSpec):
        raise TypeError("mixed needs an LPSpec or a PackingSpec; spec() "
                        "returned " + type(sp).__name__)
    if prove_optimal:
        from .engines import bb

        res = await _off(bb.prove_optimal, sp, _limits(timeout_ms),
                         spec_path=str(f), max_nodes=max_nodes,
                         wall_ms=wall_timeout_ms)
        out = _emit(res, spec_file=f)
        for k in ("optimum", "nodes", "by_bound", "infeasible", "leaves", "gap"):
            if k in res.meta:
                out[k] = res.meta[k]
        return out
    if explore:
        from . import explore as ex

        return _emit(await _off(ex.lp, "mixed", sp, _limits(timeout_ms),
                                target if target is not None else sp.target),
                     spec_file=f)
    res = await _off(mx.mixed, sp, _limits(timeout_ms), str(f),
                     target if target is not None else sp.target, freeze)
    out = _emit(res, spec_file=f)
    for k in ("achieved", "conditional", "bound", "target", "deficit",
              "globally_optimal", "selected"):
        out[k] = res.meta.get(k)
    return out


@mcp.tool(description=(
    "POLYNOMIAL equations, decided algebraically -- no SMT involved. With "
    "claim=None it asks whether the system is INCONSISTENT and returns "
    "cofactors h_i with 1 = sum h_i g_i, which refutes it over the COMPLEX "
    "numbers and hence over the reals, rationals and integers. With a claim f "
    "it certifies f = sum h_i g_i, i.e. f vanishes on every common root. "
    "Finding the cofactors is a Groebner basis computation; CHECKING them is "
    "expanding a product in exact rationals, so the certificate needs neither "
    "a solver nor an algebra system. Groebner DECIDES membership: a negative "
    "answer is conclusive, not a timeout. Reach for this when `prove` is "
    "grinding on polynomial equalities."))
@_guard
async def ideal(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000, eliminate_linear: bool = False) -> dict:
    from .engines import algebra
    from .spec import IdealSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, IdealSpec)
    res = await _off(algebra.ideal, sp, _limits(timeout_ms), str(f), None,
                     True if eliminate_linear else None)
    out = _emit(res, spec_file=f)
    out["cofactors"] = res.meta.get("cofactors")
    return out


@mcp.tool(description=(
    "Verify an EXACT COVER: a universe, parts, and every element in exactly "
    "one part. A clique partition of a graph is the main case -- give the "
    "edges as the universe and VERTEX SETS as the parts with cliques=true, "
    "and each part is refused unless every pair among its vertices really is "
    "an edge. Checking is counting: no solver, no search, no trust in "
    "whatever produced the cover. This certifies a cover you HAVE; finding a "
    "minimum one is NP-hard and is not what this does. For the other half -- "
    "that no smaller cover exists -- run `opt` on the same universe and pair "
    "the exact dual with this, the way `opt --gap` pairs the two sides of a "
    "packing."))
@_guard
async def cover(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000, optimize: bool = False,
                prove_optimal: bool = False, max_nodes: int = 5000,
                wall_timeout_ms: int | None = None, minimum: bool = False,
                max_states: int | None = None) -> dict:
    """`optimize` adds the other side: the relaxation's bound on the cover
    number and, with `prove_optimal`, the integer optimum by branch and
    bound -- each labelled with what it IS. `minimum` proves the minimum
    number of `candidates` by a recurrence over masks, the whole table its
    certificate (solver-free)."""
    from .engines import algebra
    from .spec import CoverSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f))
    if type(spec).__name__ == "HypergraphSpec":
        spec = spec.to_cover()
    elif not isinstance(spec, CoverSpec):
        raise TypeError("cover needs a CoverSpec or a transversal "
                        "HypergraphSpec; spec() returned " + type(spec).__name__)
    if minimum:
        return _emit(await _off(algebra.cover_minimum, spec, _limits(timeout_ms),
                                str(f), max_states), spec_file=f)
    res = await _off(algebra.cover, spec, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    if optimize and res.certificate is not None:
        bounds = await _off(algebra.cover_bounds, spec, _limits(timeout_ms),
                            prove_optimal=prove_optimal, max_nodes=max_nodes,
                            wall_ms=wall_timeout_ms)
        # Three numbers, each with WHAT it is and what proves it. `optimum`
        # sat beside an `exact_cover` certificate that proves validity and
        # size only, and was read as that certificate's claim; it is proved
        # by branch and bound, whose certificate is now saved and named.
        opt_path = None
        if bounds.get("optimum_cert") is not None:
            c = bounds["optimum_cert"]
            pth = _workspace() / "certs" / "cover-optimum-{}.json".format(c.digest())
            pth.write_text(c.to_json(), encoding="utf-8")
            opt_path = str(pth.relative_to(_workspace())).replace("\\", "/")
        out["bounds"] = {
            "parts": {"value": res.meta.get("parts"),
                      "is": "an UPPER bound: the cover you have, valid -- "
                            "the exact_cover certificate proves this and its "
                            "size, not that it is minimum"},
            "relaxation": {"value": bounds.get("relaxation"),
                           "is": "a LOWER bound: the exact LP dual, fractional"},
            "optimum": {"value": bounds.get("optimum"),
                        "is": ("the integer optimum, PROVED by branch and "
                               "bound -- see its own certificate")
                        if bounds.get("optimum") is not None else
                        "not proved (prove_optimal off, or stopped)",
                        "certificate": opt_path},
            "stopped": bounds.get("stopped")}
    return out


@mcp.tool(description=(
    "A bound that holds for EVERY value of a parameter, not the ones you "
    "tried. Give an LP whose coefficients are POLYNOMIALS in a parameter plus "
    "a dual y you already have (read it off `opt` on one instance), and this "
    "certifies opt(p) <= b(p).y for all p at or above a floor. Weak duality "
    "holds symbolically; the check is substituting p = p0 + u and reading the "
    "signs off the coefficients, with no solver. This is the finite-to-"
    "infinite jump: a sweep says 'checked for p = 5..12', this says 'holds "
    "for every p >= 10'. The shift test is SUFFICIENT and not necessary, so a "
    "failure means the route did not work and NEVER that the bound is false; "
    "no certificate is emitted for one."))
@_guard
async def parametric(spec_path: str | None = None,
                     spec_source: str | None = None,
                     timeout_ms: int = 60_000, explore: bool = False) -> dict:
    from .engines import algebra
    from .spec import ParametricSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), ParametricSpec)
    if explore:
        from . import explore as ex

        return _emit(await _off(ex.parametric, spec, _limits(timeout_ms)),
                     spec_file=f)
    res = await _off(algebra.parametric, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "PEAK: the best INTEGER choice for a whole family of concave quadratics, "
    "and the value there. Use when a value function is optimised over "
    "something that must be a whole number -- a clique size, a block count, a "
    "number of parts -- and the claim is quantified over a parameter rather "
    "than checked for the cases somebody ran. A write-up completes the "
    "square, says the objective is an integer at integer argument, and "
    "concludes the maximum is the FLOOR of the continuous peak; the floor of "
    "a parametric expression is not a polynomial and so is not checkable. "
    "This certifies the same thing without one: moving the origin to the "
    "claimed maximiser x*, an integer step t changes the objective by "
    "A t^2 + q'(x*) t, which is <= 0 for every non-zero integer t exactly "
    "when A <= q'(x*) <= -A -- two polynomial inequalities, checked by "
    "expanding and reading signs, no solver. The bound is ATTAINED because "
    "x* is an integer, so the answer is the integer maximum and not an upper "
    "bound on it; a maximiser with non-integer coefficients is refused rather "
    "than assumed integral. Which integer is nearest the vertex usually "
    "depends on the parameter modulo something, so a family splits into "
    "residue classes and EACH IS ITS OWN SPEC -- they are different claims. "
    "certo does not search for x*: round the real vertex and hand it over."))
@_guard
async def peak(spec_path: str | None = None,
               spec_source: str | None = None,
               timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import PeakSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), PeakSpec)
    res = await _off(algebra.peak, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "ELIMINATE a variable from exactly two polynomials and get the condition "
    "on the ones that remain. The answer is the resultant: it vanishes "
    "exactly when the two share a root in the eliminated variable, so "
    "'do f and g have a common solution in t' becomes a polynomial condition "
    "on everything else. Comes with the Bezout identity Res = A*f + B*g, so "
    "checking it is expanding two products -- no solver, no algebra system. "
    "A resultant that is a NON-ZERO CONSTANT proves no common root exists at "
    "all. Res = 0 is necessary for a common root always, and sufficient only "
    "over an algebraically closed field with a non-vanishing leading "
    "coefficient; the certificate says which case you are in. For more than "
    "two equations use `ideal`."))
@_guard
async def eliminate(spec_path: str | None = None,
                    spec_source: str | None = None,
                    variable: str | None = None,
                    timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import EliminateSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), EliminateSpec)
    if variable:
        spec.eliminate = variable
    res = await _off(algebra.eliminate, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "Certify a polynomial NON-NEGATIVE everywhere as an exact sum of squares: "
    "p = sum d_i q_i^2 with rational d_i and rational linear forms. The Gram "
    "matrix is searched for in floating point and never reaches the "
    "certificate -- it is rounded, re-projected and re-verified in exact "
    "rationals, the same way `opt` reconstructs its dual. INCOMPLETE on "
    "purpose: from degree 4 in 3 variables there are non-negative polynomials "
    "that are not sums of squares (Motzkin), so finding nothing is "
    "unknown_solver and NEVER 'it goes negative'. For degree 2, `farkas "
    "--nonlinear` is cheaper."))
@_guard
async def sos(spec_path: str | None = None, spec_source: str | None = None,
              timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import SOSSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, SOSSpec)
    res = await _off(algebra.sos, sp, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    out["squares"] = res.meta.get("squares")
    return out


@mcp.tool(description=(
    "PRIMALITY with a certificate, or a factorisation whose factors carry "
    "one. `n.is_prime()` is true, fast and unciteable; a Pratt certificate is "
    "the same fact with the evidence: a witness generating (Z/n)^*, plus a "
    "certificate for each prime factor of n-1, recursively down to 2. "
    "Checking the whole tree is modular exponentiation and nothing else. A "
    "composite n comes back REFUTED, which is a real answer rather than a "
    "failure to find one."))
@_guard
async def number(n: int, question: str = "prime",
                 timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import NumberSpec

    res = await _off(algebra.number, NumberSpec(n=n, question=question),
                     _limits(timeout_ms), "")
    out = _emit(res)
    for k in ("witness", "factors", "checks", "nodes", "depth"):
        if res.meta.get(k) is not None:
            out[k] = res.meta[k]
    return out


@mcp.tool(description=(
    "Finite base cases plus an inductive step, chained by INDUCTION, with the "
    "join checked. Z3 has no induction schema: the principle is applied by "
    "this tool and the certificate's structure is the application -- it is "
    "recorded, not verified by a solver. What IS checked is the part that "
    "goes wrong: the base cases are exactly k0..base_upto with no gap, the "
    "step starts no later than the base ends, the step is proved with the "
    "index FREE (so universally valid), and every base case has its own "
    "certificate. A base covering 3..8 with a step valid only from k>=10 "
    "proves nothing about 9, and reads identically in prose."))
@_guard
async def induct(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import induct as ind
    from .spec import InductSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, InductSpec)
    res = await _off(ind.induct, sp, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    for k in ("base_cases", "step_from", "bridges"):
        out[k] = res.meta.get(k)
    return out


@mcp.tool(description=(
    "Assemble lemmas and their certificates into ONE proof, with the join "
    "between them checked. Every other tool produces a leaf; this produces "
    "the proof. For each lemma discharged here it verifies the LINK -- that "
    "what the lemma's certificate actually closes entails the statement used "
    "downstream -- which is where hand-assembled arguments break (a lemma "
    "proved under one hypothesis, used under another). A lemma supplied as a "
    "stored certificate instead (a sweep, a DRAT proof) is a BRIDGE: verified "
    "on its own, but the step to a first-order formula is a modelling "
    "decision, so it is recorded by name and reported on every verification. "
    "The response says which lemmas the theorem needed and which it did not."))
@_guard
async def compose(spec_path: str | None = None, spec_source: str | None = None,
                  timeout_ms: int = 60_000) -> dict:
    from .engines import compose as cp
    from .spec import ProofSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, ProofSpec)
    res = await _off(cp.compose, sp, _limits(timeout_ms), str(f), _workspace())
    out = _emit(res, spec_file=f)
    for k in ("lemmas", "used", "unused", "bridges"):
        out[k] = res.meta.get(k)
    return out


@mcp.tool(description=(
    "linarith/nlinarith with the certificate attached: non-negative rational "
    "multipliers that combine the hypotheses with the negated goal until "
    "everything cancels and what is left is false. Checked by adding "
    "fractions, no solver. Hypotheses with multiplier 0 are absent, so this "
    "also says which ones the proof really uses. nonlinear=true is nlinarith: "
    "products and squares of the hypotheses are added first, which is a "
    "HEURISTIC -- finding nothing does NOT mean the claim is false, and "
    "`prove` (Z3 nlsat, complete for real arithmetic) is the tool that "
    "decides. The response carries the Lean tactic line this corresponds to. "
    "INFEASIBILITY directly: a claim of False, or an LPSpec, asks whether the "
    "hypotheses contradict each other; a feasible system comes back REFUTED "
    "with its point."))
@_guard
async def farkas(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 20_000, nonlinear: bool = False) -> dict:
    from .engines import farkas as fk
    from .i18n import t as _t
    from .spec import LPSpec, Spec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f)
    if not isinstance(sp, (Spec, LPSpec)) and type(sp).__name__ != "PackingSpec":
        raise TypeError(_t("spec.wrong_type", got=type(sp).__name__,
                           want="Spec / LPSpec"))
    res = await _off(fk.farkas, sp, _limits(timeout_ms), nonlinear, str(f))
    out = _emit(res, spec_file=f)
    out["multipliers"] = res.meta.get("multipliers")
    out["lean"] = res.meta.get("hint")
    if res.meta.get("point"):
        out["point"] = res.meta["point"]
    return out


@mcp.tool(description=(
    "CEGIS over a SynthSpec: THERE EXISTS an object such that FOR ALL inputs "
    "of the BOUNDED domain. Returns the object found and the counterexamples "
    "that forced it. CAREFUL: this is a bounded DISCOVERY, not a theorem. "
    "With prove_candidate=True it fixes the object and additionally proves "
    "the universal statement (the spec must supply universal= or "
    "universal_behavior=)."))
@_guard
async def synth(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 10_000, max_iterations: int = 10_000,
                prove_candidate: bool = False) -> dict:
    from .certificate import synth_proved_certificate
    from .engines import cegis
    from .spec import SynthSpec, load_spec
    from .status import Verdict

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f, SynthSpec)
    lim = _limits(timeout_ms, max_iterations=max_iterations)
    res = await _off(cegis.synth, sp, lim)

    if not prove_candidate or res.verdict is not Verdict.PROVED:
        out = _emit(res, spec_file=f)
        out["scope"] = ("BOUNDED synthesis: the object holds in the spec's "
                        "domain; this is not a theorem")
        return out

    uni = await _off(cegis.prove_candidate, sp,
                     res.certificate.payload["implementation"], lim)
    combo = synth_proved_certificate(
        candidate=res.meta.get("implementation"),
        synth_cert=res.certificate.to_dict(),
        universal_cert=uni.certificate.to_dict() if uni.certificate else None,
    ).stamp(f)
    res.certificate = combo
    out = _emit(res, spec_file=f)
    out["candidate"] = res.meta.get("implementation")
    out["universal_proof"] = {"verdict": uni.verdict.value,
                              "status": uni.status.value, "detail": uni.detail}
    out["scope"] = ("UNIVERSAL PROOF: PASS" if uni.verdict is Verdict.PROVED
                    else "the candidate does NOT generalise: " + uni.detail)
    return out


@mcp.tool(description=(
    "Solve an LPSpec (LP or ILP) or a PackingSpec. The certificate is the "
    "DUAL, checked with pure EXACT rational arithmetic. For an ILP the dual "
    "certifies the relaxation bound, not integer optimality: `gap=true` on a "
    "PackingSpec returns BOTH sides as one certificate -- the fractional "
    "optimum mu* with its dual, the integral nu with its point -- and the gap "
    "between them; `round=true` certifies integer optimum <= floor(LP). "
    "`target` is the value to reach; `no_exact` skips the exact "
    "reconstruction (faster, NOT citable); `dual_direction` ({row: weight}, "
    "or 'row=w,...') picks among optimal duals. `exact_required=true`: no "
    "floating-point fallback -- INCONCLUSIVE with the failed exact check "
    "named. `primal={var: 'p/q'}`: certify an exact optimum you already have."))
@_guard
async def opt(spec_path: str | None = None, spec_source: str | None = None,
              timeout_ms: int = 10_000, by_type: bool = False,
              explore: bool = False, round: bool = False,
              cuts: str | None = None, gap: bool = False,
              target: str | None = None, no_exact: bool = False,
              dual_direction: dict | str | None = None,
              exact_required: bool = False,
              primal: dict | None = None, diffuse: bool = False) -> dict:
    from .engines import lp
    from .packing import PackingSpec
    from .spec import LPSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f)
    if type(sp).__name__ == "HypergraphSpec":
        sp = sp.to_lp()
    if isinstance(sp, PackingSpec):
        packing, sp = sp, sp.to_lp()
    elif isinstance(sp, LPSpec):
        packing = None
    else:
        raise TypeError("opt needs an LPSpec or a PackingSpec; spec() returned "
                        + type(sp).__name__)
    if diffuse:
        return _emit(await _off(lp.diffuse, sp, _limits(timeout_ms)), spec_file=f)

    if gap:
        if packing is None:
            raise TypeError("gap=true needs a PackingSpec: the integral side "
                            "is a packing's")
        from .packing import gap_result

        res = await _off(gap_result, packing, _limits(timeout_ms), target)
        out = _emit(res, spec_file=f)
        for k in ("mu", "nu", "gap", "tight", "integral_level", "reached"):
            if k in res.meta:
                out[k] = res.meta[k]
        return out
    if explore:
        from . import explore as ex

        return _emit(await _off(ex.lp, "opt", sp, _limits(timeout_ms),
                                target=target), spec_file=f)
    res = await _off(lp.opt, sp, _limits(timeout_ms), use_exact=not no_exact,
                     target=target, round=round, cuts=cuts,
                     dual_direction=lp.direction_from(dual_direction),
                     exact_required=exact_required, primal=primal)
    out = _emit(res, spec_file=f)
    if packing is not None:
        from .packing import loads_from_dual

        out["loads"] = dict(list(loads_from_dual(res.certificate).items())[:_CAP])
        if by_type:
            out["by_type"] = {}
            for kind in packing.kinds:
                sub = await _off(lp.opt, packing.restricted({kind}).to_lp(),
                                 _limits(timeout_ms))
                out["by_type"][kind] = sub.meta.get("objective")
    return out


@mcp.tool(description=(
    "SAT over a CNFSpec with a verified DRAT proof. UNSAT with a proof is a "
    "citable FINITE CASE -- not the general theorem: it is checked without "
    "running any code and without trusting the solver. SAT returns the witness."))
@_guard
async def cases(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 10_000, conflict_budget: int = 1_000_000,
                solver: str = "internal") -> dict:
    from .cnf import CNF, CNFSpec
    from .engines import sat
    from .spec import load_spec

    f = _spec_file(spec_path, spec_source)
    obj = await _off(load_spec, f)
    if not isinstance(obj, (CNF, CNFSpec)):
        raise TypeError("cases needs a CNF or CNFSpec; spec() returned "
                        + type(obj).__name__)
    s = obj if isinstance(obj, CNFSpec) else CNFSpec(cnf=obj, title=obj.title)
    lim = _limits(timeout_ms, conflict_budget=conflict_budget)
    return _emit_f(f, await _off(sat.cases, s, lim, solver))


@mcp.tool(description=(
    "Enumerate every graph on n vertices up to isomorphism, filtered. "
    "Filters: connected, chordal, triangle_free, k4_free, regular, "
    "has_triangle, min_degree=K, max_degree=K, edges=K. n<=8 without nauty."))
@_guard
async def enum(n: int, filters: list[str] | None = None,
               timeout_ms: int = 60_000) -> dict:
    from .engines import graphsearch

    # No spec here: enum takes n and filters directly, so there is no file
    # to stamp against.
    res = await _off(graphsearch.enum, n, filters or [], _limits(timeout_ms))
    out = _emit(res)
    g6 = res.certificate.payload["graph6"] if res.certificate else []
    out["graphs_sample"] = g6[:_CAP]
    out["graphs_total"] = len(g6)
    return out


@mcp.tool(description=(
    "Run a SweepSpec's predicate over the whole enumerated family. PROVED "
    "settles the FINITE CASE, not the theorem. REFUTED lists counterexamples; "
    "pass them to `shrink` to minimise them. If the spec sets `collect`, the "
    "response also carries min/max/mean and the extremes with their graph. "
    "With n_range=\"4..8\" it sweeps every size and reports the first one that "
    "fails; stop_on_first stops there. Also accepts a DomainSpec for any "
    "finite domain, not just graphs. witnesses=true, after a refuted sweep of "
    "a DomainSpec with a symmetry and a reducer, minimises one representative "
    "per orbit: the sweep, the orbits and the witnesses as ONE certificate."))
@_guard
async def sweep(spec_path: str | None = None, spec_source: str | None = None,
                by_orbit: bool = False,
                timeout_ms: int = 60_000, cert_mode: str = "failures",
                n_range: str | None = None,
                stop_on_first: bool = False, explore: bool = False,
                witnesses: bool = False) -> dict:
    """`witnesses=true`, after a refuted sweep of a DomainSpec with a
    symmetry and a reducer: one minimal witness per orbit, and the sweep,
    the orbits and the witnesses as ONE certificate."""
    from .engines import domain, graphsearch
    from .spec import DomainSpec, SweepSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    sp = await _off(load_spec, f)
    if explore and isinstance(sp, (DomainSpec, SweepSpec)):
        from . import explore as ex

        return _emit(await _off(ex.sweep, sp, _limits(timeout_ms)),
                     spec_file=f)
    if n_range:
        if not isinstance(sp, SweepSpec):
            raise TypeError("n_range only applies to a SweepSpec")
        try:
            lo, hi = (int(x) for x in n_range.split(".."))
        except ValueError:
            raise ValueError("n_range expects LO..HI, for example 4..8")
        res = await _off(graphsearch.sweep_range, sp, lo, hi,
                         _limits(timeout_ms), stop_on_first, cert_mode)
    elif isinstance(sp, DomainSpec):
        res = await _off(domain.sweep_domain, sp, _limits(timeout_ms),
                         cert_mode, by_orbit)
    elif isinstance(sp, SweepSpec):
        res = await _off(graphsearch.sweep, sp, _limits(timeout_ms), True,
                         cert_mode, by_orbit=by_orbit)
    else:
        raise TypeError("sweep needs a SweepSpec (graphs) or a DomainSpec "
                        "(any finite domain); spec() returned "
                        + type(sp).__name__)
    found = None
    if witnesses:
        from .engines.shrink import orbit_witnesses
        from .i18n import t as _t_
        from .status import Verdict

        if res.verdict is not Verdict.REFUTED or not res.meta.get("orbits"):
            raise ValueError(_t_("cli.witness.needs_orbits"))
        if not isinstance(sp, DomainSpec) or sp.reduce is None:
            raise ValueError(_t_("cli.witness.needs_reduce"))
        res.certificate, found = await _off(orbit_witnesses, sp, res,
                                            _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    if res.meta.get("calibration"):
        out["calibration"] = res.meta["calibration"]
    if found is not None:
        out["witnesses"] = [{k: w[k] for k in ("representative", "size",
                                               "minimal", "steps")}
                            for w in found]
    return out


@mcp.tool(description=(
    "Minimise a counterexample. With a SweepSpec it reduces a graph (deleting "
    "vertices and edges); with a CNFSpec it extracts a MUS. The result is "
    "1-MINIMAL, not minimum: no ONE-step reduction is still a counterexample. "
    "A DomainSpec works too, from `item` (an id) or the sweep's first "
    "counterexample; `from_cert` starts from the WORST counterexample a "
    "stored sweep recorded; `objective=true` minimises the spec's objective "
    "along the way."))
@_guard
async def shrink(spec_path: str | None = None, spec_source: str | None = None,
                 graph: str | None = None, timeout_ms: int = 60_000,
                 keep_filters: bool = True, item: str | None = None,
                 objective: bool = False, from_cert: str | None = None) -> dict:
    """As the command: a SweepSpec (graphs), a DomainSpec (any finite domain,
    starting from `item` or the sweep's first counterexample) or a CNFSpec.
    `from_cert` starts from the WORST counterexample a stored sweep recorded;
    `objective` minimises the spec's objective along the way."""
    from .cnf import CNF, CNFSpec
    from .engines import domain, graphsearch, shrink as shr
    from .graphs import Graph
    from .spec import DomainSpec, SweepSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    obj = await _off(load_spec, f)
    lim = _limits(timeout_ms)

    if isinstance(obj, (CNF, CNFSpec)):
        s = obj if isinstance(obj, CNFSpec) else CNFSpec(cnf=obj, title=obj.title)
        return _emit_f(f, await _off(shr.shrink_cnf, s, lim))

    if isinstance(obj, DomainSpec):
        items = {obj.id_of(i): i for i in obj.enumerate()}
        if item:
            start = items.get(item)
            if start is None:
                raise ValueError("no item with id " + item)
        else:
            sw = await _off(domain.sweep_domain, obj, lim)
            ces = sw.meta.get("counterexamples", [])
            if not ces:
                return {"command": "shrink", "verdict": "inconclusive",
                        "detail": "the sweep found no counterexample to minimise",
                        "meta": _trim(sw.meta), "certificate": None}
            start = items[ces[0]]
        return _emit_f(f, await _off(shr.shrink_domain, obj, start, lim,
                                     spec_path=str(f), use_objective=objective))

    if not isinstance(obj, SweepSpec):
        raise TypeError("shrink needs a SweepSpec, a DomainSpec or a CNFSpec; "
                        "spec() returned " + type(obj).__name__)

    if from_cert:
        from .cli import _worst_from_cert

        start = Graph.from_graph6(_worst_from_cert(
            str(_resolve(from_cert)), getattr(obj, "worst", "min")))
    elif graph:
        start = Graph.from_graph6(graph)
    else:
        sw = await _off(graphsearch.sweep, obj, lim)
        ces = sw.meta.get("counterexamples", [])
        if not ces:
            return {"command": "shrink", "verdict": "inconclusive",
                    "detail": "the sweep found no counterexample to minimise",
                    "meta": _trim(sw.meta), "certificate": None}
        start = Graph.from_graph6(ces[0])

    return _emit_f(f, await _off(shr.shrink_graph, obj, start, lim,
                                 str(f), keep_filters,
                                 use_objective=objective))


@mcp.tool(description=(
    "Certified bisection over a BisectSpec: find a constant's threshold. The "
    "certificate is the PAIR that brackets it (a proof on the good side, a "
    "refutation on the bad one). ASSUMES MONOTONICITY in the parameter."))
@_guard
async def bisect(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import bisect as bis
    from .spec import BisectSpec

    return await _spec_tool(bis.bisect, BisectSpec)(
        spec_path, spec_source, timeout_ms)


@mcp.tool(description=(
    "Audit ledger: 'list' shows what was run, 'verify' re-reads every "
    "certificate the log points at and re-verifies it. A certificate that "
    "changed since it was logged comes back as 'changed', which is different "
    "from failing verification. Append to it by passing log=true to a command."))
@_guard
async def ledger(action: str = "list", file: str | None = None,
                 limit: int = 20, timeout_ms: int = 60_000) -> dict:
    from . import ledger as _ledger

    path = _resolve(file) if file else (_workspace() / _ledger.DEFAULT_NAME)
    if action == "list":
        rows = _ledger.read(path)
        return {"path": str(path), "total": len(rows), "entries": rows[-limit:]}
    if action == "verify":
        rep = _ledger.verify_all(path, _limits(timeout_ms))
        rep["path"] = str(path)
        rep["rows"] = rep["rows"][-limit:]
        return rep
    raise ValueError("action must be 'list' or 'verify'")


@mcp.tool(description=(
    "EXISTS: does a cover exist at all -- and when it does not, the "
    "refutation that says so. The other half of `cover`, which certifies a "
    "cover you already have. Use it for a finite NON-EXISTENCE: no triangle "
    "decomposition of this graph, no partition into at most k parts. Two "
    "answers and both are certificates -- when one exists the solver model "
    "is a SUGGESTION whose parts go through the counting verifier of `cover`, "
    "and when none does you get a DRAT refutation checked by unit "
    "propagation with no solver. `max_parts` caps how many parts may be used. "
    "WHAT IT DOES NOT SAY: that no cover exists AT ALL. It says none exists "
    "using these candidates, which is the same statement only when the "
    "candidates are every part that could have been used."))
@_guard
async def exists(spec_path: str | None = None, spec_source: str | None = None,
                max_parts: int | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import CoverSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), CoverSpec)
    res = await _off(algebra.exists, spec, _limits(timeout_ms), str(f), "internal", max_parts)
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "FAMILY: the largest of a finite family of linear programs, with every "
    "other one bounded below it. Use it when the answer is a maximum over "
    "many cases -- every bipartition, every profile -- and solving the best "
    "one is not the claim. Two claims and they are NOT symmetric: the winner "
    "ATTAINS the value with an exact primal and dual that meet, and every "
    "other item is BOUNDED by a feasible dual, which is weak duality and "
    "much cheaper than solving. Nothing stores a linear program: each is "
    "rebuilt from the spec at verification, so a dual belonging to a "
    "different item does not fit -- and verification NEEDS the spec file and "
    "fails loudly without it. Every item program must be a maximisation. "
    "Budget roughly a fifth of a second per item."))
@_guard
async def family(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 600_000) -> dict:
    from .engines import algebra
    from .spec import FamilySpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), FamilySpec)
    res = await _off(algebra.family_max, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "RATIO: a rational-function inequality, for every parameter value at "
    "once, with no solver. `(n-2)/n^2 <= 1/n for every n >= 2` and its "
    "cousins -- a step bound, a window width, an error term. `prove` settles "
    "these too and its certificate re-checks by running a solver again; this "
    "one re-checks by cross-multiplying and reading signs. The step that can "
    "go wrong is clearing the denominators, so it is the step that gets "
    "checked: both must be shown POSITIVE on the ray, and one that cannot be "
    "is refused rather than assumed, because a negative denominator flips "
    "the inequality. Relation is `<=` or `<`; `>=` is refused, being the "
    "same claim with the sides swapped. A failure means the route did not "
    "work, NEVER that the inequality is false."))
@_guard
async def ratio(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import RatioSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), RatioSpec)
    res = await _off(algebra.ratio, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "MOMENT: the expected number of bad events, in exact rationals, and the "
    "existence a mean below one buys. The probabilistic method -- if "
    "E[X] < 1 some outcome has none of them, so an object avoiding all of "
    "them exists. Two ways to supply it: `events`, a list of probabilities "
    "summed by linearity of expectation which needs NO independence, or "
    "`tails`, a distribution as P(X>=1), P(X>=2), ... whose masses are the "
    "successive differences. In floating point, 0.9999999 and 1.0000001 have "
    "both been written down as less than one; here the sum is exact and "
    "re-added on verification. The existence conclusion is drawn ONLY when "
    "the quantity is declared a count -- non-negative and integer-valued -- "
    "because a mean below one for something that could be one half "
    "everywhere puts no outcome at zero."))
@_guard
async def moment(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import MomentSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), MomentSpec)
    res = await _off(algebra.moment, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "ENTRY: where a finite sequence first crosses a threshold, and how far "
    "past it lands. Two claims and the SECOND carries the weight: it crosses "
    "at k, and it had NOT crossed at any earlier index. An off-by-one, or a "
    "`<=` where the argument needed `<`, and the first index is not first "
    "while every later step rests on it. With a `step_bound` you also get "
    "the WINDOW: the step before the crossing was on the near side, so the "
    "crossing overshoots by at most delta. The certificate carries only the "
    "prefix up to the crossing, because nothing past it is part of either "
    "claim. A sequence that never crosses comes back REFUTED with no "
    "certificate -- there is no first index when there is no crossing."))
@_guard
async def entry(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import EntrySpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), EntrySpec)
    res = await _off(algebra.entry, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "REPRO: bundle specs, certificates, versions and hashes into one "
    "directory somebody can check with nothing installed but certo. Two "
    "rules make it worth having. NOTHING INVALID GOES IN: every certificate "
    "is verified on the way and one that fails is left out and NAMED, "
    "because a bundle containing a certificate that does not check is worse "
    "than no bundle -- it looks like evidence. NOTHING UNTIED GOES IN "
    "QUIETLY: a certificate names its spec by hash, and when the file has "
    "moved on the manifest says so rather than shipping a different file in "
    "silence."))
@_guard
async def repro(directory: str | None = None, out: str | None = None,
                include_ledger: bool = True,
                timeout_ms: int = 120_000) -> dict:
    from . import repro as _repro

    where = _resolve(directory) if directory else _workspace()
    dest = _resolve(out) if out else (_workspace() / "repro")
    return await _off(_repro.bundle, str(where), str(dest),
                      _limits(timeout_ms), include_ledger)


@mcp.tool(description=(
    "REPORT: something went wrong and you want to know WHOSE fault it is -- "
    "certo's, the spec's, or the machine's -- before anybody files anything. "
    "Give it the certo command line that misbehaved (e.g. `opt spec.py "
    "--target 5`), and optionally a certificate and whether the RESULT is "
    "mathematically false. It re-runs the command keeping the traceback that "
    "the CLI throws away, and classifies with evidence: `certo-bug` when certo "
    "produced a certificate its own verifier rejects (the one certain "
    "verdict); `certo-bug?` when an exception came from a call certo made; "
    "`spec` when it came from the spec's own code or `lint` reports an error; "
    "`environment` when `doctor` finds something missing; `soundness` when a "
    "certificate VERIFIES and is reported false -- the worst bug this tool can "
    "have. It writes a local folder and returns its path, the triage and a "
    "link. IT NEVER FILES ANYTHING. The folder contains the spec, which may be "
    "unpublished mathematics, so what gets shared is the PERSON'S decision "
    "after reading it: tell them where it is and let them choose. Before "
    "blaming yourself for a failure, run this -- a report this project "
    "received from an agent turned out to be certo's own bug."))
@_guard
async def report(command_line: str | None = None,
                 certificate_path: str | None = None,
                 wrong: bool = False, include_coverage: bool = False,
                 out: str | None = None,
                 stderr_path: str | None = None) -> dict:
    import shlex

    from . import report as _report

    argv = shlex.split(command_line) if command_line else None
    if argv and argv[0] == "certo":
        argv = argv[1:]
    dest = str(_resolve(out)) if out else None
    cert = str(_resolve(certificate_path)) if certificate_path else None
    err = str(_resolve(stderr_path)) if stderr_path else None
    info = await _off(_report.build, argv, cert, wrong, include_coverage, dest,
                      err)
    info["note"] = ("nothing has been sent; the folder includes the spec, "
                    "so ask the person before sharing any of it")
    return info


@mcp.tool(description=(
    "DOCTOR: what this install can and cannot do, with what happens without "
    "each missing piece. Run it when something came back inconclusive and "
    "you want to know whether that was the mathematics or the machine -- a "
    "missing exact LP backend, no external SAT solver, no arbitrary-"
    "precision library. It answers whether the problem is the spec or the "
    "environment, which is otherwise expensive to answer by guessing."))
@_guard
async def doctor() -> dict:
    from . import doctor as _doctor

    return await _off(_doctor.report)


@mcp.tool(description=(
    "QUOTIENT: a partition of a program's rows and columns, and the "
    "EQUIVALENCE it induces -- the physical program and the quotient have the "
    "same SET of attainable values, by an explicit projection `z_j = sum over "
    "the class of x_C` and lifting `x_C = z_j / M_j`. Equality of optima is a "
    "corollary, and no duality is needed. This is strictly stronger than "
    "comparing two computed optima, which is what `reduce` does after "
    "checking a group: two numbers agreeing is also what a wrong reduction "
    "with a compensating error produces. THE PARTITION IS AN INPUT -- a group "
    "action produces one, so does a colour refinement, so does a person who "
    "knows the classes -- which separates the finite-sum core from the group "
    "theory. WHAT IS CHECKED against the matrix: the classes partition with "
    "no empty fibre; capacities and senses constant on row classes, weights "
    "and bounds on column classes; and REGULARITY both ways, since `H_ij` "
    "(one resource, how much of object class j uses it) and `B_ij` (one "
    "object, how much of resource class i it uses) are different quantities "
    "tied by `N_i H_ij = M_j B_ij`. A partition failing any of them is "
    "REFUSED naming the two rows that disagree: one edge at capacity zero "
    "among capacity-one edges breaks it, and the aggregate would otherwise "
    "report an optimum the physical program cannot attain. It says NOTHING "
    "about integrality: an integer orbit mass need not lift to integer "
    "objects."))
@_guard
async def quotient(spec_path: str | None = None,
                   spec_source: str | None = None,
                   timeout_ms: int = 120_000) -> dict:
    from .engines import algebra
    from .spec import EquitableQuotientSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), EquitableQuotientSpec)
    res = await _off(algebra.equitable_quotient, spec, _limits(timeout_ms),
                     str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "SOLVE: an exact linear system `A x = b`, over the rationals or the "
    "integers, with a witness whichever way it goes. The certificate is the "
    "solution and the system it solves, so re-checking is ONE matrix-vector "
    "product -- and because `A` and `b` travel with `x`, the check is against "
    "the system that was stated rather than the one somebody remembers "
    "stating. UNSOLVABLE is certified too: `y` with `y.A = 0` and `y.b != 0`. "
    "UNDERDETERMINED returns a particular solution plus a basis of the kernel, "
    "because reporting one point of an affine subspace as the answer is how a "
    "free parameter disappears. `domain=\"integer\"` decides it by the Smith "
    "normal form instead, and \"no integer solution\" is a different answer "
    "from \"no solution\". It establishes NEITHER non-negativity NOR, over "
    "the rationals, integrality: a rational solution to the equations of a "
    "packing is not a packing. Use `opt` or `farkas` for the first."))
@_guard
async def solve(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import LinearSystemSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), LinearSystemSpec)
    res = await _off(algebra.linear_system, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "RANGE: how far one variable may go over a regime -- the whole interval, "
    "not one point of it. `check --hypotheses-only` exhibits a MODEL, which "
    "answers whether the regime is inhabited and nothing else; a user who "
    "needed `a <= 1/3` got `a = 0` and derived the rest by hand. Both ends "
    "here are exact rational LP duals, so the certificate carries the "
    "NON-NEGATIVE COMBINATION of hypotheses that yields each bound and "
    "checking it is adding fractions. The variables are FREE -- a regime is "
    "not a packing and `a` may be negative. AN EMPTY REGIME IS ITS OWN "
    "ANSWER, not an infinite interval: over an empty regime every direction "
    "is unbounded, and reading that as `the variable ranges over everything` "
    "is the permissive-looking mistake. A strict binding row makes the "
    "endpoint OPEN and says so. Linear hypotheses only: a non-linear one is "
    "refused by name rather than dropped, because dropping it would widen "
    "the range -- wrong in the direction that looks safe."))
@_guard
async def range(spec_path: str | None = None,  # noqa: A001 - the tool IS `range`
                spec_source: str | None = None,
                var: str = "", timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import Spec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), Spec)
    res = await _off(algebra.variable_range, spec, var, _limits(timeout_ms),
                     str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "CYCLE: a parameter that depends on itself, and whether the loop can "
    "close. The expensive shape is three innocent lines -- `k >= "
    "tower(1/delta)`, `rho <= K/(3k^2)`, `delta <= rho` -- none of which "
    "mentions a cycle, and there is one. Declare each dependency as a GROWTH "
    "CLASS (`poly` with a degree, `exp`, `tower`, optionally of the "
    "reciprocal) and certo composes them once and compares the two ends. When "
    "the comparison is STRICT in the direction that refutes the closing "
    "constraint, no positive parameter survives, and the certificate is the "
    "chain plus that one comparison -- no solver. THE CLASSES ARE YOURS: that "
    "`k` grows like a tower is what your lemma says, and certo checks only "
    "what follows from it. MONOTONICITY IS TRACKED, so an edge whose "
    "available bound points the wrong way is REFUSED rather than composed -- "
    "composing it could declare a live regime empty. A cycle that is not "
    "refuted comes back `not established by this route`, never `there is no "
    "cycle`."))
@_guard
async def cycle(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import CycleSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), CycleSpec)
    res = await _off(algebra.dependency_cycle, spec, _limits(timeout_ms),
                     str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "BIND: tie a certificate to the Lean declaration meant to justify it, and "
    "check that the declaration actually gives what the certificate assumed. "
    "The failure this exists for: a bound certified ASSUMING a fine counting "
    "estimate, and a packaged lemma that uses density <= 1 and gives "
    "something useless -- discovered three modules later, by reading the "
    "statement. certo reads the certificate's provenance, loads the spec it "
    "came from, finds the named hypothesis, and asks whether what you say the "
    "declaration PROVIDES entails it. A gap is reported at bind time, which "
    "is when you are looking at the statement. IT REMAINS A BRIDGE: nothing "
    "here reads Mathlib, so that your rendering is faithful is your claim, "
    "and `verify` says so every time. A spec that changed since the "
    "certificate was issued is reported STALE rather than read as if it had "
    "not."))
@_guard
async def bind(spec_path: str | None = None, spec_source: str | None = None,
               timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import BindSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), BindSpec)
    res = await _off(algebra.lean_binding, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "CONE: the local toric data two geometric theorems consume, computed from "
    "the ray generators instead of assumed. Returns, exactly and without a "
    "solver: whether each generator is PRIMITIVE, the MULTIPLICITY (the index "
    "of the sublattice they span), the HEIGHT functional `u` with "
    "`<u, v> = 1` on every generator, and the DISCREPANCY `<u, w> - 1` of any "
    "ray you name. THE LATTICE IS DECLARED, NEVER GUESSED, and it changes the "
    "ANSWER rather than the error: one real cell is multiplicity 16 read in "
    "Z^4 and 1 read in the lattice its generators are primitive in, so a "
    "multiplicity without its lattice is half a sentence. CREPANT is a "
    "question about what a SUBDIVISION adds -- a generator's discrepancy is "
    "zero by construction wherever a height functional exists -- so with no "
    "subdivision named the answer is None rather than a vacuous yes. A "
    "non-simplicial cone still gets an answer: the missing quantity is "
    "recorded with why, instead of the certificate being refused. IT PROVES "
    "NO GEOMETRY: that multiplicity one gives a smooth chart, that "
    "discrepancy zero gives a crepant modification, that a fibre is SNC or "
    "reduced -- those are theorems about varieties and nothing here "
    "establishes them."))
@_guard
async def cone(spec_path: str | None = None, spec_source: str | None = None,
               timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import ConeSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), ConeSpec)
    res = await _off(algebra.toric_cone, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "PROFILE: how an optimum responds to ONE capacity across an interval, as "
    "a certified FUNCTION rather than a value. Not `parametric`, which bounds "
    "a family whose parameter sits in the data; here the parameter is a single "
    "row's capacity `t` and the answer is concave, piecewise affine, with "
    "breakpoints. Reach for it when the question is not 'what is the optimum' "
    "but 'what survives when only a fraction of the shared resource is "
    "available' -- the shape near zero decides whether an obstruction "
    "amplifies when a piece is repeated, which the single value at t=1 cannot "
    "tell you. YOU SUPPLY the breakpoints, one dual per segment and one primal "
    "source per breakpoint; finding them is parametric programming and any "
    "solver may do it. certo CHECKS, and recomputes every number from the "
    "columns. WHY FINITE DATA SETTLES A CONTINUUM: a dual's feasibility never "
    "mentions a capacity, so one dual bounds every `t` in its segment at once; "
    "two sources at a segment's ends attain the whole segment, because "
    "interpolating them is feasible at the interpolated capacity with the "
    "interpolated value; and sorted segments sharing endpoints tile the "
    "domain. Bound plus attainment plus coverage is EQUALITY, not a bound. It "
    "is a statement about the column set given: that those are all the "
    "columns, or that the rows mean what they are called, is a separate "
    "obligation it does not discharge."))
@_guard
async def profile(spec_path: str | None = None, spec_source: str | None = None,
                  timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import ProfileSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), ProfileSpec)
    res = await _off(algebra.capacity_profile, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "SEMIGROUP: an affine semigroup `S = N.a_1 + ... + N.a_k` as a CHECKER. "
    "`cone` answers questions about the RATIONAL cone over these generators; "
    "this answers questions about what you can actually REACH by adding them, "
    "and the difference between the two is where normality lives. For each "
    "named point it reports whether it is in the CONE (with non-negative "
    "rational coefficients, or a separating functional `y` with `<y,a_i> <= "
    "0 < <y,v>` when it is outside -- one vector, checked by k+1 dot "
    "products), in the GROUP (integer coefficients, possibly negative, via "
    "Hermite normal form), and in the SEMIGROUP (non-negative INTEGER "
    "coefficients). A point in the cone and in the group but NOT in the "
    "semigroup REFUTES normality, and all three parts are arithmetic. It also "
    "reports whether the generating set is MINIMAL, naming any generator that "
    "lies in the semigroup generated by the others. EVERY SEARCH TERMINATES "
    "BECAUSE OF A GRADING: a functional `u` with `<u,a_i> >= 1` bounds the "
    "total number of generators in any representation by `<u,v>`, and that "
    "bound travels in the certificate so a verifier redoes the search rather "
    "than believing it. Without such a functional no search here is finite, "
    "and it says so instead of looking for a while. `pointed` is true with the "
    "grading, false with a zero combination of the generators that proves it, "
    "and NULL when neither was found -- null is undecided, not no. With "
    "pycddlib installed (`backend: cddlib`) pointedness and cone membership "
    "are decided from the facets. IT NEVER CLAIMS S IS NORMAL: a witness "
    "refutes normality, and "
    "establishing it means deciding membership for every lattice point of the "
    "cone, which is what Normaliz is for. `normal` is null on purpose."))
@_guard
async def semigroup(spec_path: str | None = None, spec_source: str | None = None,
                    timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import SemigroupSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), SemigroupSpec)
    res = await _off(algebra.affine_semigroup, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "COLUMNS: an LP over EVERY clique of a graph, one row per edge, solved "
    "WITHOUT listing the cliques. `problem` is packing (max, load <= rhs), "
    "cover (min, >=) or partition (min, =); each clique Q of size >= "
    "min_size is a column with weight a|E(Q)| + b|Q| + c from `weight` "
    "{edges, vertices, constant}. Column generation with an EXACT pricing "
    "search: the certificate holds the support, the exact dual of every edge "
    "row, and the search that shows no clique has positive reduced cost -- "
    "which the verifier RERUNS, so there is no oracle to trust. Weak duality "
    "then proves the optimum over all cliques. Use it where listing the "
    "cliques for `opt` is too many; for a few hundred, `opt` is as fast. "
    "`max_size` bounds the family from above (only edges and triangles, "
    "say). A partition with min_size > 2 may be infeasible: that is then "
    "PROVED, by a Farkas vector whose pricing search the verifier reruns."))
@_guard
async def columns(spec_path: str | None = None, spec_source: str | None = None,
                  timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import CliqueLPSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), CliqueLPSpec)
    res = await _off(algebra.clique_lp, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "ATLAS: a parameter domain covered by boxes, each certified by "
    "`parametric`, and ONE statement for the whole. Every piece is verified "
    "again; all must be the same program with the same claim; and the "
    "covering is recomputed exactly -- the domain split at the pieces' edges, "
    "each cell inside a piece or shown outside the `region` by Bernstein "
    "coefficients. A cell that is neither is NAMED with its coordinates: the "
    "sliver a box-by-box proof leaves. Pieces given as paths are referenced "
    "by digest; `cited` boxes make the statement relative. No charts yet."))
@_guard
async def atlas(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 120_000) -> dict:
    from .engines import algebra
    from .spec import AtlasSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), AtlasSpec)
    res = await _off(algebra.atlas, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "FIND: is it in certo, and where? Search every command, flag, spec field, "
    "certificate kind and Python API function by WHAT YOU NEED, in English or "
    "Spanish -- most of certo is flags and fields, not commands, and this is "
    "how to find them. `exact='opt.round'` (or a spec, field or kind name) "
    "returns one contract: its flags, fields with defaults, options. Start "
    "here when unsure which tool fits."))
@_guard
async def find(query: str = "", exact: str | None = None, n: int = 8) -> dict:
    from . import discovery

    if exact:
        got = discovery.contract(exact)
        if got is None:
            return {"ok": False, "exact": exact,
                    "near": [e["id"] for e in discovery.find(exact.replace(".", " "), n=5)]}
        return {"ok": True, "contract": got}
    rows = discovery.find(query, n=n)
    out = {"ok": bool(rows), "query": query,
           "results": [{k: v for k, v in e.items() if k != "text"} for e in rows]}
    said = discovery.notes(query)
    if said:
        out["notes"] = said
    return out


@mcp.tool(description=(
    "RUN: any command that takes a spec, by name -- the generic entry point the "
    "compact server exposes instead of one tool per command. `command` as "
    "`find` names it (opt, nonneg, pin...); `options` are the engine's keyword "
    "options (`find(exact=command)` lists them). The certificate is written to "
    "the workspace and its path returned; check it with `verify`."))
@_guard
async def run(command: str, spec_path: str | None = None,
              spec_source: str | None = None, options: dict | None = None,
              timeout_ms: int = 120_000) -> dict:
    from . import api
    from .spec import load_spec

    if command not in api.runnable():
        return {"ok": False, "error": "{} does not run a spec; these do: {}".format(
            command, ", ".join(api.runnable()))}
    f = _spec_file(spec_path, spec_source)
    spec = await _off(load_spec, str(f))
    res = await _off(api.run, command, spec, _limits(timeout_ms),
                     spec_path=str(f), **(options or {}))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "BATCH: every spec file in a workspace directory through ONE command, in "
    "this server's process (or `jobs` worker processes): one certificate per "
    "spec, written beside the others and named after it, each self-checked "
    "as a single run is. Rows in the directory's order. Nothing is joined "
    "into one claim -- that is `atlas` (boxes) or `status --manifest`."))
@_guard
async def batch(command: str, directory: str, pattern: str = "*.py",
                out_directory: str | None = None, jobs: int = 1,
                timeout_ms: int = 60_000) -> dict:
    from . import api
    from . import batch as B
    from .i18n import t as _t

    if command not in api.runnable():
        return {"ok": False, "error": _t("cli.batch.not_runnable", command=command,
                                        commands=", ".join(api.runnable()))}
    d = _resolve(directory)
    out = _resolve(out_directory) if out_directory else d / "certs"
    files = B.specs_in(d, pattern)
    rows = await _off(B.run, command, files, out, max(1, jobs), timeout_ms)
    ws = _workspace()
    for r in rows:
        for k in ("spec", "certificate"):
            if r.get(k):
                try:
                    r[k] = str(Path(r[k]).resolve().relative_to(ws))
                except ValueError:
                    pass
    return {"command": command, "summary": B.summary(rows),
            "rows": rows[:_CAP], "rows_total": len(rows)}


@mcp.tool(description=(
    "ASSIGN: items to receivers under capacities (pages to the hosts each "
    "may use, jobs to machines...). Returns the LARGEST integral assignment "
    "and a Hall set U of receivers with cap(U) + |items not confined to U| "
    "equal to its size -- so it is maximum, checked by counting, no LP. With "
    "a target out of reach, REFUTED and U is the bottleneck, named: too few "
    "items, too little capacity, or a set of receivers the items are stuck on."))
@_guard
async def assign(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import AssignmentSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), AssignmentSpec)
    res = await _off(algebra.assign, spec, _limits(timeout_ms), str(f))
    out = _emit(res, spec_file=f)
    if res.certificate is not None:
        out["assignment"] = dict(list(res.certificate.payload["assignment"].items())[:_CAP])
        out["hall"] = res.certificate.payload["hall"]
    return out


@mcp.tool(description=(
    "PIN: the clique partition number of a graph pinned from both sides. "
    "`upper` an exact cover by cliques (cp <= X), `lower` a clique LP "
    "(cp >= ceil(L)) -- certificates or specs -- both re-verified and shown "
    "to be about the SAME edge list before their numbers are compared. Equal: "
    "cp = X PROVED. Otherwise the range, certified. A lower bound from an "
    "`opt --round` of your own program needs `assumption=`, and is relative."))
@_guard
async def pin(spec_path: str | None = None, spec_source: str | None = None,
              timeout_ms: int = 120_000) -> dict:
    from .engines import algebra
    from .spec import PinSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), PinSpec)
    res = await _off(algebra.pin, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "NONNEG: a polynomial is >= 0 on a box, or on the part of it a region "
    "`g >= 0` cuts. PROVED carries Bernstein coefficients on a subdivision "
    "(and constant multipliers of the region's conditions); REFUTED carries a "
    "point of the box inside the region with the exact negative value. A "
    "region also writes an algebraic endpoint exactly: [0, sqrt(3/40)] is the "
    "box [0, 1/2] with 3/40 - x^2 >= 0. Solver-free."))
@_guard
async def nonneg(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import NonnegSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), NonnegSpec)
    res = await _off(algebra.nonneg, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "PROMOTE: run an exploration again CERTIFIED and say whether the two "
    "agree. `explore=true` on opt, mixed, parametric and sweep answers "
    "cheaply -- floating point, samples, verdict `likely`, no certificate; "
    "promote is how a likely answer becomes a proved one. Give the record a "
    "CLI `--explore --record FILE` wrote."))
@_guard
async def promote(record_path: str, timeout_ms: int = 120_000) -> dict:
    from . import explore, report

    rec = explore.load_record(_resolve(record_path))
    run = await _off(report.rerun, list(rec["argv"]))
    res = run.get("result")
    if res is None:
        return {"ok": False, "error": run.get("exception") or "no result"}
    agrees, why = explore.agreement(rec, res)
    out = _emit(res)
    out["explored"] = rec.get("answer")
    out["agrees"], out["why"] = agrees, why
    return out


@mcp.tool(description=(
    "PACK: every certificate under a directory into ONE zip, each member "
    "compressed on its own and readable alone, with a manifest of names, "
    "digests and kinds. `verify` then takes the zip (every member and the "
    "manifest) or `family.zip#member`. For thousands of box certificates: "
    "7.8x smaller and one file instead of thousands."))
@_guard
async def pack(src: str, out: str) -> dict:
    from . import store

    return await _off(store.pack, str(_resolve(src)), str(_resolve(out)))


@mcp.tool(name="mcp", description=(
    "MCP: which certo MCP servers are running, when each started, and which "
    "started before the installed package -- STALE, answering with old code. "
    "Lists only: stopping a server ends another client's session, so that is "
    "left to the person, with `certo mcp restart --yes` on the command line."))
@_guard
async def mcp_servers(action: str = "status") -> dict:
    # Not `def mcp`: that name is the server object every `@mcp.tool` uses.
    from . import mcpctl
    from .i18n import t as _t

    out = await _off(mcpctl.status)
    out["stale_here"] = bool(mcpctl.stale())
    out["to_stop"] = _t("mcp.stop_from_cli")
    return out


@mcp.tool(description=(
    "MATRIX: exact integer linear algebra -- rank, determinant, Hermite and "
    "Smith normal form -- with the unimodular transforms carried alongside "
    "their inverses, so every answer is checkable by integer matrix "
    "MULTIPLICATION rather than by repeating the elimination. `U.A = H` with "
    "`U.U_inv = I` proves U is unimodular, so A and H have the same row "
    "lattice; H's shape then gives the rank and its diagonal the determinant, "
    "up to the sign of det(U), which is known to be +1 or -1 and is settled "
    "exactly by one determinant modulo an odd prime. Smith adds a column "
    "transform and a checked divisibility chain, which is what makes the "
    "invariant factors -- and so the torsion of Z^n / A Z^m -- a finite "
    "checkable fact. `rows` and `cols` on the spec select a submatrix first, "
    "which is how you ask about a MINOR. Entries must be integers: 2.5 is "
    "refused rather than rounded. INERTIA: `question=\"inertia\"` or "
    "`\"psd\"` takes a SYMMETRIC matrix of exact rationals (ints, Fractions, "
    "or strings like \"3/7\") and answers by a congruence S.A.S^T = D with "
    "S.S_inv = I, so the signs of D are the inertia by Sylvester's law; `psd` "
    "is REFUTED with a vector x where x^T A x < 0. For many matrices in a "
    "loop, `certo.inertia.signature(rows)` in Python gives the same counts "
    "exactly, fast, without a certificate."))
@_guard
async def matrix(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000) -> dict:
    from .engines import algebra
    from .spec import MatrixSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), MatrixSpec)
    res = await _off(algebra.integer_matrix, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "REDUCE: quotient a linear program by a group acting on it, with the "
    "averaging argument CHECKED rather than asserted. Every write-up that "
    "says 'averaging over the automorphism group, an optimal solution may be "
    "assumed constant on each orbit' is using a bridge; its three hypotheses "
    "are finite checks given a generating set -- the action permutes the "
    "variables, the constraint set is invariant, the objective is invariant. "
    "With those, the feasible region is convex so the average of an optimum "
    "is feasible, the objective is invariant so it has the same value, and it "
    "is constant on orbits by construction. The quotient has one variable per "
    "orbit with coefficients summed. WHERE THE GROUP COMES FROM is not "
    "certo's job -- nauty computes it, this checks it -- and a generator that "
    "is not an automorphism is REFUSED by name, because a wrong group does "
    "not give a weaker reduction, it gives a wrong one. A "
    "ParametricSymmetrySpec asks the same question about a FAMILY: orbits "
    "with multiplicities that are POLYNOMIALS in the parameters, and rows "
    "that exist only where their conditions hold. The objective is not "
    "declared -- substituting one variable per orbit sums each orbit, so the "
    "objective IS the multiplicities. The regimes (the distinct row sets the "
    "conditions cut parameter space into) are DERIVED, so a piecewise closed "
    "form can be compared against them: a formula with three branches over a "
    "program with four regimes is missing a case. TWO LEVELS, kept apart: the "
    "quotient's SHAPE is symbolic, while that the declared group really has "
    "these orbits is checked per instance on a finite window. Agreement on a "
    "window is falsifiability, not proof, and the certificate says so. "
    "parametric=true ASSERTS the family: one instance is refused, not "
    "answered with the weaker single-instance result."))
@_guard
async def reduce(spec_path: str | None = None, spec_source: str | None = None,
                 timeout_ms: int = 60_000, parametric: bool = False) -> dict:
    """`parametric=true` ASSERTS the family: a spec that is one instance is
    refused rather than answered with the weaker single-instance result."""
    from .engines import algebra
    from .spec import ParametricSymmetrySpec, SymmetrySpec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f))
    if parametric and not isinstance(spec, ParametricSymmetrySpec):
        from .i18n import t as _t

        raise TypeError(_t("cli.reduce.not_parametric", got=type(spec).__name__))
    if isinstance(spec, ParametricSymmetrySpec):
        res = await _off(algebra.reduce_parametric, spec, _limits(timeout_ms),
                         str(f))
        return _emit(res, spec_file=f)
    if not isinstance(spec, SymmetrySpec):
        from .i18n import t as _t

        raise TypeError(_t("spec.wrong_type", got=type(spec).__name__,
                           want="SymmetrySpec or ParametricSymmetrySpec"))
    res = await _off(algebra.reduce_symmetry, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "AUDIT: does each hypothesis earn its place? Drops each one in turn and "
    "hunts a counterexample to what remains. `core` answers the other half -- "
    "which hypotheses an unsat core NEEDED -- and catches a theorem stated "
    "with slack. This catches the opposite and more expensive mistake: a "
    "theorem stated TOO STRONGLY, formalised, and only then found to be about "
    "a smaller class than claimed. FOUR answers per hypothesis and they are "
    "different: NEEDED with a witness assignment that shows HOW it matters, "
    "REDUNDANT so the theorem can be stated without it, DOMAIN when it was "
    "holding up a well-definedness condition rather than a mathematical one, "
    "and UNKNOWN when the budget ran out -- never folded into the others, "
    "because not finding a counterexample is not the absence of one. DOMAIN "
    "exists because division is TOTAL in SMT: `n/0` is a value the solver "
    "invents, so dropping a hypothesis that guards a denominator would "
    "otherwise yield an instant counterexample that is about the solver and "
    "not about the theorem. Every divisor that could vanish is collected up "
    "front and every search is guarded by it; a DOMAIN hypothesis must NOT be "
    "dropped -- discharge it as a side condition in the proof assistant. Run "
    "it BEFORE formalising. It does NOT prove the hypothesis set is minimal: "
    "dropping them one at a time says nothing about dropping two."))
@_guard
async def audit(spec_path: str | None = None, spec_source: str | None = None,
                timeout_ms: int = 60_000) -> dict:
    from .engines import smt
    from .spec import Spec, load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f), Spec)
    res = await _off(smt.audit, spec, _limits(timeout_ms), str(f))
    return _emit(res, spec_file=f)


@mcp.tool(description=(
    "ASK: one entry point. Give it a spec file and it runs whatever command "
    "that spec's TYPE asks for, reporting which one it chose so the answer "
    "stays traceable to a command you can run directly. Use it when you have "
    "already written the spec and do not want to pick between thirty-four "
    "commands -- a RatioSpec is a ratio question, a PeakSpec is a peak "
    "question, and the choice was never a choice. It refuses rather than "
    "guessing when the command needs a decision it cannot make for you, such "
    "as whether you want integer optimality proved. Call `commands` instead "
    "when you know the QUESTION but have not written a spec yet."))
@_guard
async def ask(spec_path: str | None = None, spec_source: str | None = None,
              timeout_ms: int = 120_000) -> dict:
    import inspect

    from .i18n import t as _t
    from .routing import prepared, runner_for
    from .spec import load_spec

    f = _spec_file(spec_path, spec_source)
    spec = load_spec(str(f))
    command, fn = runner_for(spec)
    if fn is None:
        return {"ok": False, "spec": type(spec).__name__, "command": command,
                "detail": _t("cli.ask.unknown", got=type(spec).__name__)
                if command is None
                else _t("cli.ask.needs_flags", command=command,
                        got=type(spec).__name__)}
    ready = prepared(spec)
    if "spec_path" in inspect.signature(fn).parameters:
        res = await _off(fn, ready, _limits(timeout_ms), str(f))
    else:
        res = await _off(fn, ready, _limits(timeout_ms))
    out = _emit(res, spec_file=f)
    out["routed_to"] = command
    return out


@mcp.tool(description=(
    "COMMANDS: which command answers which question, as a routing table. "
    "Read the QUESTION, not the name. Call this FIRST when you know what you "
    "want to establish but not which tool establishes it: it maps is this "
    "true, how big, does it hold for every case, does one exist at all, and "
    "is my setup even sane onto the tool that answers each. Every row "
    "carries the spec type it takes and whether its certificate re-checks "
    "WITHOUT a solver, which for two routes to the same fact is usually the "
    "deciding difference and is invisible from the name."))
@_guard
async def commands() -> dict:
    from .routing import table

    return table()


@mcp.tool(description=(
    "Re-verify a stored certificate. Those marked solver_free are checked "
    "without any solver: arithmetic, evaluation or unit propagation. ALWAYS "
    "use this before taking a result as settled."))
@_guard
async def verify(certificate_path: str, timeout_ms: int = 60_000) -> dict:
    from .certificate import Certificate
    from .certificate import verify as vc

    from . import store

    head, member = store.split_ref(certificate_path)
    p = _resolve(head)
    if member is None and str(p).lower().endswith(".zip"):
        return await _off(store.verify_archive, str(p), 1, timeout_ms)
    ref = str(p) if member is None else "{}#{}".format(p, member)
    cert = Certificate.from_dict(store.read_json(ref))
    rep = await _off(vc, cert, _limits(timeout_ms))
    # rep.to_dict() and not a hand-built subset: this used to drop `warnings`,
    # which is where every "this says less than it looks like" lives -- a
    # bridge that is asserted rather than derived, a vacuous proof, a sweep
    # whose predicate nothing certified. An ok=True with those removed is the
    # overclaim this tool exists to prevent.
    from . import card as _card

    return dict(rep.to_dict(), card=_card.card_of(cert, rep))


@mcp.tool(description=(
    "Where the work stands: read every certificate in a directory and report "
    "what is established, what is STILL OWED (bridges and assumptions the "
    "results rest on), what is HOLLOW (vacuous proofs, sweeps that certified "
    "nothing), and what is STALE (the spec changed since the certificate was "
    "issued). Start here when picking up a workspace you did not build. It "
    "reads the certificates rather than re-verifying them unless you ask. "
    "manifest=true: the set in canonical order with one fingerprint; with "
    "`expect` (headlines, or a workspace file of them) it names what is "
    "MISSING, not only what is there."))
@_guard
async def status(directory: str | None = None, verify_all: bool = False,
                 timeout_ms: int = 60_000, root: str | None = None,
                 since: str | None = None, manifest: bool = False,
                 expect: list[str] | str | None = None) -> dict:
    """With `root` (a certificate path): the report UNDER that target -- every
    certificate it is built from with its degree of checking, every
    obligation still open, and what in the directory is off the route.
    `since`: a previous such report, saved as JSON, to say what changed.
    `manifest`: the set in canonical order with one fingerprint; `expect`
    (headlines, or a workspace file of them, one per line) names what is
    MISSING rather than only what is there."""
    import json as _json

    from . import status_report

    where = _resolve(directory) if directory else _workspace()
    if manifest or expect:
        wanted = None
        if isinstance(expect, str):
            wanted = [ln.strip() for ln in _resolve(expect).read_text(
                encoding="utf-8").splitlines() if ln.strip()]
        elif expect:
            wanted = [str(x) for x in expect]
        return await _off(status_report.manifest, str(where), expect=wanted)
    if root:
        rep = await _off(status_report.route, str(_resolve(root)), str(where),
                         _limits(timeout_ms))
        if since:
            before = _json.loads(_resolve(since).read_text(encoding="utf-8"))
            rep["since"] = status_report.since(rep, before.get("route", before))
        return {"route": rep}
    return await _off(status_report.scan, str(where), verify_all,
                      _limits(timeout_ms))


@mcp.tool(description=(
    "Check a spec BEFORE spending the compute on it. Catches a missing goal, "
    "hypotheses that contradict each other (so any proof would be vacuous), "
    "an inductive step that starts after the base cases end, an empty family, "
    "a domain of 10^9 items, and a predicate returning `bool` -- which means "
    "the sweep will be `reproducible`, not `certified`. Loading a spec "
    "executes it; nothing else here runs the solver on the goal or enumerates "
    "a whole domain. Cheap, and worth doing every time."))
@_guard
async def lint(spec_path: str | None = None, spec_source: str | None = None,
               timeout_ms: int = 10_000) -> dict:
    from . import lint as _lint

    f = _spec_file(spec_path, spec_source)
    return await _off(_lint.lint, str(f), _limits(timeout_ms))


@mcp.tool(description=(
    "Export a graph counterexample as Lean 4 DATA plus a skeleton, read from "
    "a stored shrink/sweep/graph_set certificate or from a graph6 string. "
    "Compiles against Lean/Mathlib v4.28.0 (including its `decide` sanity "
    "checks); another version may need adjusting. The edge list is exact "
    "either way."))
@_guard
async def export_lean(certificate_path: str | None = None,
                      graph: str | None = None) -> dict:
    from . import lean
    from .certificate import Certificate
    from .graphs import Graph

    if graph:
        graphs, source = [Graph.from_graph6(graph)], "graph6 " + graph
    elif certificate_path:
        from . import store

        p = _resolve(certificate_path)
        data = store.read_json(p)
        graphs = lean.graphs_from_certificate(data)
        source = "{} (certificate {})".format(
            certificate_path, Certificate.from_dict(data).digest())
    else:
        raise ValueError("give exactly one: certificate_path or graph")

    text = lean.graphs_to_lean(graphs, source)
    out = _workspace() / "certs" / "lean_{}.lean".format(
        hashlib.sha256(text.encode()).hexdigest()[:12])
    out.write_text(text, encoding="utf-8")
    return {"graphs": len(graphs),
            "path": str(out.relative_to(_workspace())).replace("\\", "/"),
            "compiled": False,
            "warning": "checked against Lean/Mathlib v4.28.0; another version "
                       "may need adjusting. The edge list is exact either way."}


@mcp.tool(description=(
    "Dump a spec to its textual form: SMT-LIB2 for Spec/SynthSpec, DIMACS "
    "for CNF. Useful for archiving or handing to another tool."))
@_guard
async def export(spec_path: str | None = None, spec_source: str | None = None,
                 negate_goal: bool = False, max_chars: int = 4000) -> dict:
    import z3

    from . import z3util
    from .cnf import CNF, CNFSpec
    from .spec import Spec, SynthSpec, load_spec

    f = _spec_file(spec_path, spec_source)
    obj = await _off(load_spec, f)

    if isinstance(obj, (CNF, CNFSpec)):
        text = (obj.cnf if isinstance(obj, CNFSpec) else obj).to_dimacs()
        fmt = "dimacs"
    elif isinstance(obj, Spec):
        parts = list(obj.formulas)
        if obj.goal is not None:
            parts.append(z3.Not(obj.goal) if negate_goal else obj.goal)
        text, fmt = z3util.smt2(*parts), "smt2"
    elif isinstance(obj, SynthSpec):
        impl, behav, corr = obj.normalized()
        text = "\n".join("; ---- {} ----\n{}".format(n, z3util.smt2(e))
                         for n, e in (("impl", impl), ("behavior", behav),
                                      ("correctness", corr)))
        fmt = "smt2"
    else:
        raise TypeError("export does not support " + type(obj).__name__)

    out = {"format": fmt, "chars": len(text), "truncated": len(text) > max_chars}
    out["text"] = text[:max_chars]
    return out


#: The tools a COMPACT server keeps: find what exists, run it, check what it
#: wrote, and the guide. Fifty-odd tools is a long list for a model to read
#: before it knows what it needs; four, and `find`, is not.
COMPACT = ("find", "run", "verify", "dsl_guide")


def compact() -> list:
    """Reduce this server to `COMPACT`. Returns the tools removed."""
    names = [tl.name for tl in mcp._tool_manager.list_tools()]
    gone = [n for n in names if n not in COMPACT]
    for n in gone:
        mcp.remove_tool(n)
    return gone


def _watch_parent(grace_s=10.0):
    """Exit when the client that started this server is gone.

    A user found 28 servers alive at once: a server lives as long as its
    stdin stays open, and a dead client does not always close it -- a
    process it started may still hold the pipe. The parent dying is the
    signal that nobody can talk to this server again.

    A parent that dies within `grace_s` of the start was a LAUNCHER (a shim
    that starts the server and exits), not the client: then the watch is
    dropped rather than the server. `CERTO_MCP_NO_PARENT_WATCH=1` turns it
    off.
    """
    import os
    import threading
    import time

    if os.environ.get("CERTO_MCP_NO_PARENT_WATCH"):
        return None
    ppid = os.getppid()
    if ppid <= 1:
        return None
    t0 = time.monotonic()

    if os.name == "nt":
        import ctypes

        k32 = ctypes.windll.kernel32
        handle = k32.OpenProcess(0x00100000, False, ppid)   # SYNCHRONIZE
        if not handle:
            return None

        def gone():
            return k32.WaitForSingleObject(handle, 0xFFFFFFFF) == 0
    else:
        def gone():
            while os.getppid() == ppid:
                time.sleep(5)
            return True

    def watch():
        if gone() and time.monotonic() - t0 > grace_s:
            os._exit(0)

    th = threading.Thread(target=watch, daemon=True, name="certo-parent-watch")
    th.start()
    return th


def main(argv=None) -> None:
    import os
    import sys

    argv = sys.argv[1:] if argv is None else argv
    _watch_parent()
    if "--compact" in argv or os.environ.get("CERTO_MCP_COMPACT"):
        compact()
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
