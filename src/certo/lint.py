"""`certo lint`: the questions worth asking before the compute is spent.

The primary consumer of this tool is a language model writing a spec, and a
model has no way to know its spec is well-posed until it runs -- by which
point a sweep over 10^9 items is already running, or a base case has proved
six sweeps before the engine notices the inductive step starts too late.

So: a dry pass. It loads the spec and looks at its shape, doing the cheapest
thing that answers a real question and nothing more. The rule it holds to is
that every finding names something that WILL bite, not something that might:
a linter nobody believes is a linter nobody reads.

Three findings earn their keep on their own.

  A CONTRADICTORY HYPOTHESIS SET, found here rather than after the proof.
  `prove` already reports vacuity, and reporting it first, for the cost of one
  solver call on a strictly easier problem, turns a valid-and-empty result
  into a question asked before anybody believed the answer.

  AN INDUCTIVE STEP THAT STARTS TOO LATE. The engine refuses this too, but
  only after discharging every base case, which is usually where the time
  goes. The check is a comparison of two integers.

  A PREDICATE THAT RETURNS `bool`. It is a perfectly good thing to write, and
  it means the sweep will report `reproducible` rather than `certified`. That
  difference has been read wrong by people who wrote the predicate themselves,
  so it is better said in advance than discovered in a verdict.

Loading a spec EXECUTES it: that is how specs work here, and lint is no
exception. It does not run the solver on the goal, enumerate a whole domain,
or call a predicate more than once.
"""
from __future__ import annotations

from pathlib import Path

from .i18n import t

ERROR, WARN, NOTE = "error", "warn", "note"

#: Above this, enumerating the domain is itself the expensive part, so the
#: count is reported as "at least" and the iterable is left alone.
PEEK = 100_000

#: Graphs on n vertices up to isomorphism (OEIS A000088). Knowing the size of
#: a sweep should not cost what the sweep costs, and this is the whole reason
#: the number is in a table rather than counted: `certo lint` on n = 10 has to
#: answer in the time it takes to read the file.
GRAPH_COUNTS = {0: 1, 1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044,
                8: 12346, 9: 274668, 10: 12005168, 11: 1018997864,
                12: 165091172592}

#: Without `geng`, enumeration is the Python augmentation, which is quadratic
#: in a big number. Seven vertices is 1044 graphs and instant; eight is not.
CHEAP_WITHOUT_GENG = 7
CHEAP_WITH_GENG = 9


def _f(level, key, **kw):
    return {"level": level, "key": key, "text": t("lint." + key, **kw)}


# ---------------------------------------------------------------------------


def lint(path, limits=None) -> dict:
    """Load the spec at `path` and say what is wrong with it before it runs."""
    from .spec import load_spec

    try:
        spec = load_spec(path)
    except FileNotFoundError:
        return _report(path, None, [_f(ERROR, "no_file", path=str(path))])
    except AttributeError as exc:
        if "spec()" in str(exc):
            # A script, not a broken spec. "The spec did not load" sends the
            # reader hunting for a syntax error that is not there.
            return _report(path, None, [_f(ERROR, "no_spec_fn",
                                           path=str(path))])
        return _report(path, None, [_f(ERROR, "load_failed",
                                       error="AttributeError: {}".format(exc))])
    except Exception as exc:                     # the spec itself blew up
        return _report(path, None,
                       [_f(ERROR, "load_failed", error="{}: {}".format(
                           type(exc).__name__, exc))])

    name = type(spec).__name__
    checker = CHECKS.get(name)
    if checker is None:
        return _report(path, name, [_f(NOTE, "unknown_kind", kind=name)])

    findings = list(checker(spec, limits))
    if not getattr(spec, "title", ""):
        # `status` reads titles; a directory of untitled certificates is a
        # directory of filenames, which is what this is trying to prevent.
        findings.append(_f(NOTE, "no_title"))
    return _report(path, name, findings)


def _report(path, kind, findings) -> dict:
    by = {lvl: [f for f in findings if f["level"] == lvl]
          for lvl in (ERROR, WARN, NOTE)}
    return {
        "spec": str(path), "kind": kind,
        "command": COMMANDS.get(kind or "", ""),
        "findings": by[ERROR] + by[WARN] + by[NOTE],
        "errors": len(by[ERROR]), "warnings": len(by[WARN]),
        "notes": len(by[NOTE]),
        "ok": not by[ERROR] and not by[WARN],
    }


COMMANDS = {
    "Spec": "prove / check / core", "MultiSpec": "core", "SynthSpec": "synth",
    "LPSpec": "opt / mixed / bb / farkas", "PackingSpec": "opt --gap / opt --by-type",
    "SweepSpec": "sweep", "DomainSpec": "cases", "BisectSpec": "bisect",
    "BoundSpec": "bounds", "ProofSpec": "compose", "InductSpec": "induct",
    "IdealSpec": "ideal", "SOSSpec": "sos", "NumberSpec": "number",
    "OrderSpec": "order", "CNFSpec": "sat", "CNF": "sat",
    "EliminateSpec": "eliminate", "ParametricSpec": "parametric",
}


# ---------------------------------------------------------------------------
# the checks, one generator per spec type
# ---------------------------------------------------------------------------


def _contradictory(assumptions, limits):
    """Do the hypotheses clash among themselves, and which ones?

    The same question `prove` asks after succeeding. Asking it first costs one
    solver call on a strictly easier problem than the proof, and the answer is
    the difference between "valid" and "valid and about nothing".
    """
    if len(assumptions) < 2:
        return None
    import z3

    from .engines.smt import _mus
    from .limits import Limits

    lim = limits or Limits()
    s = z3.Solver()
    s.set(unsat_core=True)
    if lim.timeout_ms:
        s.set("timeout", lim.timeout_ms)
    ind = {}
    for n, phi in assumptions:
        ind[n] = z3.Bool("lint_" + n)
        s.add(z3.Implies(ind[n], phi))
    if s.check(*ind.values()) != z3.unsat:
        return None
    raw = {str(p)[5:] for p in s.unsat_core()}
    names = [n for n, _ in assumptions]
    return _mus(s, ind, [n for n in names if n in raw] or names, lim)


def _magnitude_shaped(expr):
    """Does this divide by a PRODUCT of symbols? Then it is a magnitude question.

    The expression that cost a user three hand-written sessions was
    `5kWC^2 / (u^3 d^2 p^10)`: a quotient whose denominator is several symbols
    at once. `prove` says SAT on it forever and correctly, because it is not an
    infeasibility -- it is a feasibility that does not improve with `n`.

    Two or more distinct symbols at negative exponent is the trigger. One is
    too common to mean anything; two is the shape.
    """
    from .asymptotics import NotAsymptotic, parse

    try:
        poly = parse(expr)
    except (NotAsymptotic, Exception):
        return None
    negative = {sym for mono in poly.terms for sym, power in mono if power < 0}
    return sorted(negative) if len(negative) >= 2 else None


#: Where `prove` stops being usable on a univariate polynomial goal.
#:
#: MEASURED, not chosen. On `t^k <= t` over `[0, 1]` -- a statement that is
#: trivially true and squarely inside the decidable fragment:
#:
#:     t^9  <= t        29 ms   proved
#:     t^10 <= t        12 ms   proved
#:     t^11 <= t     20198 ms   TIMEOUT
#:
#: A cliff between 10 and 11, not a slope. A user brought a degree-63 schedule
#: polynomial and spent 71 minutes reaching `INCONCLUSIVE [timeout]` with no
#: certificate; reducing the degree by hand (substituting `t = s^3`, plus a
#: domination argument) let certo close the same question in 4.3 ms.
#:
#: One family measured, so this WARNS and does not route: nlsat's behaviour
#: depends on more than the degree, and a linter that is wrong about something
#: expensive is a linter people switch off.
DEGREE_CLIFF = 11


def _polynomial_degree(expr, var):
    """The degree of `expr` in `var`, or None if it is not a polynomial.

    Walks the z3 term rather than multiplying it out: the goal that prompted
    this was degree 63, and expanding it to count is doing the work the check
    exists to avoid.
    """
    import z3

    if z3.is_const(expr):
        return 1 if str(expr) == str(var) else 0
    if z3.is_add(expr) or z3.is_sub(expr):
        parts = [_polynomial_degree(a, var) for a in expr.children()]
        return None if any(p is None for p in parts) else max(parts)
    if z3.is_mul(expr):
        parts = [_polynomial_degree(a, var) for a in expr.children()]
        return None if any(p is None for p in parts) else sum(parts)
    if z3.is_app_of(expr, z3.Z3_OP_POWER):
        base, power = expr.arg(0), expr.arg(1)
        # Over the reals z3 types the exponent as a REAL numeral, so
        # `is_int_value` says no to `t**63` and the whole check went quiet.
        if z3.is_int_value(power):
            k = power.as_long()
        elif z3.is_rational_value(power) and power.denominator_as_long() == 1:
            k = power.numerator_as_long()
        else:
            return None
        if k < 0:
            return None
        inner = _polynomial_degree(base, var)
        return None if inner is None else inner * k
    if z3.is_div(expr):
        num, den = expr.arg(0), expr.arg(1)
        if _polynomial_degree(den, var) != 0:
            return None            # a rational function, not a polynomial
        inner = _polynomial_degree(num, var)
        return inner
    return None


def _high_degree_univariate(goal):
    """The degree of a one-variable polynomial goal, when it is past the cliff.

    Univariate because that is where the measurement is. A multivariate goal
    of the same degree is a different problem and this says nothing about it.
    """
    from .z3util import free_consts

    names = free_consts(goal)
    if len(names) != 1:
        return None
    var = names[0]
    degrees = [_polynomial_degree(side, var) for side in _sides(goal)]
    if not degrees or any(d is None for d in degrees):
        return None
    top = max(degrees)
    return top if top >= DEGREE_CLIFF else None


def _check_spec(spec, limits):
    if spec.goal is None:
        yield _f(ERROR, "spec.no_goal")
    else:
        import z3

        # `claim(False)` is how people ask "are my hypotheses satisfiable?",
        # and it is the one phrasing that cannot answer it.
        if z3.is_false(spec.goal):
            yield _f(WARN, "spec.claim_false")
        elif z3.is_true(spec.goal):
            yield _f(WARN, "spec.claim_true")
        else:
            # `order` shipped in 0.5.0 and the person who needed it did not
            # find it. Naming it where the shape appears is the one place a
            # user is guaranteed to be looking.
            for side in _sides(spec.goal):
                names = _magnitude_shaped(side)
                if names:
                    yield _f(NOTE, "spec.magnitude",
                             names=", ".join(names[:4]))
                    break
            degree = _high_degree_univariate(spec.goal)
            if degree is not None:
                yield _f(WARN, "spec.high_degree", degree=degree,
                         proved=DEGREE_CLIFF - 1, cliff=DEGREE_CLIFF)
    if not spec.assumptions:
        yield _f(NOTE, "spec.no_hypotheses")
    clash = _contradictory(spec.assumptions, limits)
    if clash:
        yield _f(ERROR, "spec.vacuous", names=", ".join(clash))


def _sides(goal):
    """The two sides of a comparison, or nothing."""
    import z3

    if z3.is_app(goal) and goal.num_args() == 2:
        return [goal.arg(0), goal.arg(1)]
    return []


def _check_multi(spec, limits):
    if not getattr(spec, "goals", None):
        yield _f(ERROR, "multi.no_goals")
    clash = _contradictory(spec.assumptions, limits)
    if clash:
        yield _f(ERROR, "spec.vacuous", names=", ".join(clash))


def _probe(fn, item):
    """What does this predicate return? One call, and failures are findings.

    Calling it once is the only way to know, and knowing is the point: `bool`
    means `reproducible`, an `Outcome` carrying a certificate means
    `certified`, and people who wrote the predicate themselves have read that
    difference wrong.
    """
    from .spec import Outcome

    try:
        out = fn(item)
    except Exception as exc:
        return "raised", "{}: {}".format(type(exc).__name__, exc)
    if isinstance(out, Outcome):
        return ("certified" if out.cert is not None else "outcome"), ""
    if isinstance(out, bool):
        return "bool", ""
    return "other", type(out).__name__


def _predicate_findings(spec, sample):
    if spec.predicate is None:
        return
    what, detail = _probe(spec.predicate, sample)
    if what == "raised":
        yield _f(ERROR, "sweep.predicate_raised", error=detail)
    elif what == "bool":
        yield _f(NOTE, "sweep.bool")
    elif what == "outcome":
        yield _f(NOTE, "sweep.outcome_no_cert")
    elif what == "other":
        yield _f(ERROR, "sweep.predicate_type", got=detail)


def _check_sweep(spec, limits):
    from .graphs import _geng_path, enumerate_graphs

    if spec.predicate is None and spec.collect is None:
        yield _f(ERROR, "sweep.nothing")

    known = GRAPH_COUNTS.get(spec.n)
    if known is not None:
        yield _f(NOTE, "sweep.size" if not spec.filters else "sweep.size_raw",
                 n=known, vertices=spec.n)
        if known > 1_000_000:
            yield _f(WARN, "sweep.big", n=known, vertices=spec.n)
    elif spec.n > max(GRAPH_COUNTS):
        yield _f(WARN, "sweep.enormous", vertices=spec.n)

    budget = CHEAP_WITH_GENG if _geng_path() else CHEAP_WITHOUT_GENG
    if spec.n > budget:
        # Enumerating to find out what the predicate returns would cost what
        # the sweep costs, which is the thing this is here to save.
        yield _f(NOTE, "sweep.not_probed", vertices=spec.n)
        return
    try:
        family, _engine, total = enumerate_graphs(spec.n, spec.filters)
    except Exception as exc:
        yield _f(ERROR, "sweep.enumerate_failed", error=str(exc))
        return
    if spec.filters:
        yield _f(NOTE, "sweep.filtered", n=len(family), total=total)
    if not family:
        # An empty family passes every predicate. The sweep would be correct
        # and would have established nothing: the graph-shaped version of a
        # vacuous proof.
        yield _f(ERROR, "sweep.empty", n=spec.n)
        return
    if len(family) > 20_000 and spec.canonicalize is None:
        yield _f(WARN, "sweep.big_no_canon", n=len(family))
    for f in _predicate_findings(spec, family[0]):
        yield f
    for f in _small_sizes(spec):
        yield f


def _small_sizes(spec):
    """The degenerate sizes below the one swept: 0, 1 and 2 vertices.

    A statement proved by a sweep at n=7 and meant for every n is still a
    statement about n=0, where the only graph has no vertices and every
    "for all vertices" holds for free. A user's statement was false there, and
    it went to a proof assistant that way: the sweep had never been asked. At
    most four graphs per size, so this costs nothing to check.
    """
    if spec.predicate is None:
        return
    from .engines.graphsearch import _evaluate
    from .graphs import enumerate_graphs

    for k in range(0, min(spec.n, 3)):
        try:
            fam, _e, _t = enumerate_graphs(k, spec.filters, use_geng=False)
        except Exception:  # noqa: BLE001
            continue
        if not fam:
            yield _f(NOTE, "sweep.small_empty", k=k)
            continue
        bad = []
        for g in fam:
            out = _evaluate(spec, g)
            if out.ok is not True:
                bad.append(g.to_graph6())
        if bad:
            yield _f(WARN, "sweep.small_fails", k=k, n=spec.n,
                     graphs=", ".join(bad[:3]))


def _peek(spec):
    """How many items, without materialising a domain that might be enormous.

    `spec.enumerate()` builds the whole list, which is exactly the thing this
    is here to avoid doing by accident.
    """
    import itertools

    it = spec.items() if callable(spec.items) else spec.items
    try:
        return len(it), False
    except TypeError:
        pass
    head = list(itertools.islice(iter(it), PEEK + 1))
    return (PEEK, True) if len(head) > PEEK else (len(head), False)


def _check_domain(spec, limits):
    if spec.predicate is None and spec.collect is None:
        yield _f(ERROR, "sweep.nothing")
    try:
        n, capped = _peek(spec)
    except Exception as exc:
        yield _f(ERROR, "domain.items_failed", error=str(exc))
        return
    if not n:
        yield _f(ERROR, "domain.empty")
        return
    if capped:
        yield _f(WARN, "domain.huge", n=PEEK)
    else:
        yield _f(NOTE, "domain.size", n=n)
        if n > 1_000_000:
            yield _f(WARN, "domain.big", n=n)
    if spec.reduce is None:
        yield _f(NOTE, "domain.no_reduce")
    if spec.key is None:
        yield _f(NOTE, "domain.no_key")

    items = spec.items() if callable(spec.items) else spec.items
    first = next(iter(items), None)
    if first is not None:
        for f in _predicate_findings(spec, first):
            yield f


def _check_lp(spec, limits):
    if not spec.var_names:
        yield _f(ERROR, "lp.no_variables")

    # The expensive one. `no_variables` only fires when NONE were declared;
    # the shape that actually bites is one typo among several correct names,
    # where the program still solves and the answer is confidently wrong.
    declared = set(spec.var_names)
    stray = {}
    for where, coeffs in ([("objective", spec.obj)] +
                          [(n, c) for n, c, _s, _r in spec.cons]):
        for key in coeffs:
            if key not in declared:
                stray.setdefault(key, where)
    if stray:
        yield _f(ERROR, "lp.undeclared_variable",
                 names=", ".join(sorted(stray)[:4]),
                 where=", ".join(sorted(set(stray.values()))[:3]))
    if not spec.cons:
        yield _f(ERROR, "lp.no_constraints")
    if spec.integer:
        # A user read `integer=True` as "there are integers in here" and got
        # every variable rounded. Saying so up front costs nothing.
        yield _f(WARN, "lp.integer_all", n=len(spec.var_names))
    discrete = [v for v in spec.var_names
                if spec.kinds.get(v, "continuous") != "continuous"]
    if not spec.obj:
        yield _f(NOTE, "lp.no_objective")
    if discrete:
        yield _f(NOTE, "lp.mixed", n=len(discrete),
                 total=len(spec.var_names))
        unbounded = [v for v in discrete
                     if (spec.bounds.get(v) or (0, None))[1] is None
                     and spec.kinds.get(v) != "binary"]
        if unbounded:
            # `bb` splits on a discrete variable's range; without an upper
            # bound there is no finite tree to build.
            yield _f(WARN, "lp.unbounded_discrete",
                     names=", ".join(sorted(unbounded)[:5]))


def _check_packing(spec, limits):
    if not spec.items:
        yield _f(ERROR, "packing.no_items")
        return
    yield _f(NOTE, "packing.size", items=len(spec.items),
             resources=len(spec.resources))
    if spec.kinds:
        yield _f(NOTE, "packing.kinds", names=", ".join(spec.kinds))
    if spec.integer is False:
        # `opt` on a packing solves the RELAXATION. That is a real number and
        # a useful one, and it is not the packing number.
        yield _f(NOTE, "packing.fractional")
    elif spec.integer is not True:
        yield _f(NOTE, "packing.integer_kinds",
                 names=", ".join(sorted(str(k) for k in spec.integer)))


def _check_proof(spec, limits):
    if spec.goal is None:
        yield _f(ERROR, "spec.no_goal")
    if not spec.lemmas:
        yield _f(WARN, "proof.no_lemmas")
    for lem in spec.lemmas:
        if lem.certificate:
            p = Path(lem.certificate)
            if not p.is_file():
                yield _f(ERROR, "proof.cert_missing", name=lem.name,
                         path=str(p))
            if not lem.bridge:
                # The bridge prose is the whole reason a bridge is allowed:
                # nothing can check that the certificate licenses `states`, so
                # the argument that it does has to be written down by a person.
                yield _f(WARN, "proof.no_bridge", name=lem.name)
    bridges = [l.name for l in spec.lemmas if l.is_bridge]
    if bridges:
        yield _f(NOTE, "proof.bridges", n=len(bridges),
                 names=", ".join(bridges[:5]))
    clash = _contradictory(spec.assumptions, limits)
    if clash:
        yield _f(ERROR, "spec.vacuous", names=", ".join(clash))


def _check_induct(spec, limits):
    step_from = spec.k0 if spec.step_from is None else spec.step_from
    if spec.base_upto < spec.k0:
        yield _f(ERROR, "induct.no_base", k0=spec.k0, upto=spec.base_upto)
    if step_from > spec.base_upto:
        # The engine refuses this too -- after discharging every base case,
        # which is where the hours are. Two integers, compared first.
        yield _f(ERROR, "induct.gap", step=step_from, upto=spec.base_upto)
    n = spec.base_upto - spec.k0 + 1
    if n > 0:
        yield _f(NOTE, "induct.base_count", n=n, k0=spec.k0,
                 upto=spec.base_upto)
    if not spec.bridge:
        yield _f(WARN, "induct.no_bridge")


def _check_matrix(spec, limits):
    """What is worth knowing BEFORE Smith or Hermite runs.

    The cost is the reason this exists. Measured here, square, entries in
    [-4, 4]:

        32 x 32   0.04s      48 x 48   0.22s
        64 x 64   2.2s       80 x 80   5.6s

    which is roughly n^4 and steep enough that the difference between "this
    will take a moment" and "this will take the afternoon" is a couple of
    dozen rows. A user's real matrix is 64 by 64, so the threshold sits well
    above that: warning somebody about the size they actually work at is
    noise, and noise is how a linter gets ignored about the rest.
    """
    from .interchange import NotInterchangeable, load
    from .lattice import NotAnIntegerMatrix, parse

    source = spec.matrix
    if isinstance(source, (str, bytes)) or hasattr(source, "__fspath__"):
        # A data file: read it now rather than at run time, so a fingerprint
        # that disagrees is caught before anything is computed.
        try:
            source = load(source)["entries"]
        except NotInterchangeable as exc:
            yield _f(ERROR, "matrix.data_file", error=str(exc))
            return
    elif isinstance(source, dict) and "entries" in source:
        source = source["entries"]

    try:
        A = parse(source)
    except NotAnIntegerMatrix as exc:
        yield _f(ERROR, "matrix.not_a_matrix", error=str(exc))
        return

    n, m = len(A), len(A[0])

    question = getattr(spec, "question", "hermite")
    if question not in ("det", "determinant", "rank", "hermite", "smith"):
        yield _f(ERROR, "matrix.unknown_question", question=question)
    elif question in ("det", "determinant"):
        rows = getattr(spec, "rows", None)
        cols = getattr(spec, "cols", None)
        height = len(rows) if rows is not None else n
        width = len(cols) if cols is not None else m
        if height != width:
            yield _f(ERROR, "matrix.not_square", n=height, m=width)

    for name, sel, limit in (("rows", getattr(spec, "rows", None), n),
                             ("cols", getattr(spec, "cols", None), m)):
        if sel is None:
            continue
        if not len(sel):
            yield _f(ERROR, "matrix.empty_selection", which=name)
        bad = [i for i in sel if not (0 <= int(i) < limit)]
        if bad:
            yield _f(ERROR, "matrix.selection_range", which=name,
                     values=", ".join(map(str, bad[:4])), limit=limit)
        if len(set(sel)) != len(sel):
            yield _f(WARN, "matrix.selection_repeats", which=name)

    # An all-zero row or column is not an error -- the rank is still the
    # rank -- but it is almost always a construction that lost a term, and
    # it is invisible in a 64 by 64 wall of numbers.
    zero_rows = [i for i, row in enumerate(A) if not any(row)]
    zero_cols = [j for j in range(m) if not any(row[j] for row in A)]
    if zero_rows or zero_cols:
        yield _f(WARN, "matrix.empty_blocks",
                 rows=len(zero_rows), cols=len(zero_cols),
                 first=(zero_rows or zero_cols)[0])

    # Repeated rows or columns mean the rank is lower than the shape suggests,
    # and in data somebody typed by hand they usually mean a line was pasted
    # twice rather than a genuine dependency.
    for label, vectors in (("rows", [tuple(r) for r in A]),
                           ("columns", [tuple(row[j] for row in A)
                                        for j in range(m)])):
        seen, dupes = {}, []
        for i, v in enumerate(vectors):
            if any(v) and v in seen:
                dupes.append((seen[v], i))
            seen.setdefault(v, i)
        if dupes:
            yield _f(WARN, "matrix.duplicates", which=label, n=len(dupes),
                     a=dupes[0][0], b=dupes[0][1])

    entries = n * m
    if entries > 40_000:
        yield _f(WARN, "matrix.very_large", n=n, m=m, entries=entries)
    elif entries > 10_000:
        yield _f(NOTE, "matrix.large", n=n, m=m, entries=entries)

    if question == "smith" and entries > 10_000:
        yield _f(NOTE, "matrix.smith_cost", n=n, m=m)


def _check_bound(spec, limits):
    from .numerics import NoBackend, backend_name

    try:
        backend_name()
    except NoBackend:
        yield _f(ERROR, "bound.no_backend")
    if spec.claim is None:
        yield _f(NOTE, "bound.measures")
    if spec.max_prec < spec.prec:
        yield _f(ERROR, "bound.prec", prec=spec.prec, max=spec.max_prec)


def _check_order(spec, limits):
    from .asymptotics import NotAsymptotic, parse

    try:
        poly = parse(spec.expression)
    except NotAsymptotic as exc:
        yield _f(ERROR, "order.not_laurent", error=str(exc))
        return
    missing = sorted({s for m in poly.terms for s, _ in m} - set(spec.orders))
    if missing:
        # An unassigned symbol is the error the whole command exists to
        # prevent: a magnitude assumed in someone's head rather than written.
        yield _f(ERROR, "order.unassigned", names=", ".join(missing))
    unused = sorted(set(spec.orders) - {s for m in poly.terms for s, _ in m})
    if unused:
        yield _f(NOTE, "order.unused", names=", ".join(unused))
    if spec.expect is None:
        yield _f(NOTE, "order.measures")


def _check_sos(spec, limits):
    try:
        import numpy  # noqa: F401
    except ImportError:
        # The search is numeric even though the certificate is exact, so
        # without numpy `sos` cannot start at all.
        yield _f(ERROR, "sos.no_numpy")
    if not spec.variables:
        yield _f(ERROR, "sos.no_variables")


def _check_parametric(spec, limits):
    if spec.sense != "max":
        yield _f(ERROR, "param.max_only", sense=spec.sense)
    if not spec.parameters:
        yield _f(ERROR, "param.no_parameters")
        return
    bad = [str(n) for n, _, sense, _ in spec.constraints if sense != "<="]
    if bad:
        yield _f(ERROR, "param.le_only", names=", ".join(bad[:4]))
    names = [str(n) for n, _, _, _ in spec.constraints]
    dual = {str(n): v for n, v in spec.dual.items()}
    missing = [n for n in names if n not in dual]
    if missing:
        yield _f(ERROR, "param.dual_missing", names=", ".join(missing[:4]))
    negative = sorted(n for n, v in dual.items() if v < 0)
    if negative:
        # Weak duality needs y >= 0, so this is not a near miss.
        yield _f(ERROR, "param.negative", names=", ".join(negative[:4]))
    yield _f(NOTE, "param.shape", rows=len(spec.constraints),
             params=", ".join("{} >= {}".format(k, v)
                              for k, v in spec.parameters.items()))
    if not any(dual.get(n) for n in names):
        yield _f(WARN, "param.all_zero")


def _check_eliminate(spec, limits):
    from .polynomials import Poly

    if len(spec.equations) != 2:
        yield _f(ERROR, "eliminate.two_only", n=len(spec.equations))
        return
    if spec.eliminate not in spec.variables:
        yield _f(ERROR, "eliminate.unknown_var", name=spec.eliminate,
                 names=", ".join(spec.variables))
        return
    variables = tuple(spec.variables)
    k = variables.index(spec.eliminate)
    degrees = []
    for e in spec.equations:
        try:
            poly = e if isinstance(e, Poly) else Poly.from_z3(e, variables)
        except Exception as exc:
            yield _f(ERROR, "ideal.not_polynomial", error=str(exc))
            return
        degrees.append(max((m[k] for m in poly.terms), default=0))
    if min(degrees) < 1:
        # The Sylvester matrix is not defined, and the engine refuses -- but
        # comparing two integers here beats finding out after a load.
        yield _f(ERROR, "eliminate.degree_zero", var=spec.eliminate,
                 n=degrees[0], m=degrees[1])
        return
    yield _f(NOTE, "eliminate.sizes", var=spec.eliminate,
             n=degrees[0], m=degrees[1], size=degrees[0] + degrees[1])
    if degrees[0] + degrees[1] > 14:
        yield _f(WARN, "eliminate.big", size=degrees[0] + degrees[1])


def _check_ideal(spec, limits):
    if not spec.equations:
        yield _f(ERROR, "ideal.no_equations")
    if not spec.variables:
        yield _f(ERROR, "ideal.no_variables")


def _check_number(spec, limits):
    if spec.n < 2:
        yield _f(ERROR, "number.too_small", n=spec.n)
    if spec.question == "factor" and spec.n > 2 ** 70:
        # Trial division with a Pratt certificate per factor: the certificate
        # is cheap to check and the factorisation is not.
        yield _f(WARN, "number.big_factor")


def _check_synth(spec, limits):
    if not spec.impl_vars:
        yield _f(ERROR, "synth.no_impl_vars")
    if not spec.input_vars:
        yield _f(WARN, "synth.no_input_vars")
    if spec.correctness is None:
        yield _f(ERROR, "synth.no_correctness")
    if spec.universal is None and spec.universal_behavior is None:
        # `synth` searches a BOUNDED domain. Without one of these there is no
        # universal statement to promote the candidate to, and the verdict
        # stays scoped to that domain -- which is exactly the reading people
        # get wrong.
        yield _f(NOTE, "synth.bounded_only")


def _check_bisect(spec, limits):
    if spec.lo >= spec.hi:
        yield _f(ERROR, "bisect.empty", lo=spec.lo, hi=spec.hi)
    if spec.direction not in ("min_true", "max_true"):
        yield _f(ERROR, "bisect.direction", got=spec.direction)
    if not spec.integer and spec.tol <= 0:
        yield _f(ERROR, "bisect.tol", tol=spec.tol)
    # Monotonicity in t is ASSUMED and never verified. A reader who does not
    # know that reads the threshold as a proved boundary.
    yield _f(NOTE, "bisect.monotone")


def _cardinality_bound(cnf):
    """Does this formula carry an `at_most_k` counter?

    `at_most_k` names its auxiliaries `__count<tag>_<i>_<j>` rather than
    numbering them, so a DRAT proof over the formula can be read -- and that
    naming is what makes the counter visible here too. Derived from the
    encoder, so it cannot drift from it.

    Only `k >= 2` leaves a marker: `k == 1` delegates to the pairwise
    `at_most_one` and `k == 0` becomes unit clauses, neither of which has
    auxiliaries. That is the right side to miss on -- a cardinality bound of
    one is rarely the objective of a search.
    """
    names = getattr(cnf, "_name", None) or []
    return any(isinstance(n, str) and n.startswith("__count") for n in names)


def _check_cnf(spec, limits):
    cnf = getattr(spec, "cnf", spec)
    clauses = getattr(cnf, "clauses", [])
    if not clauses:
        yield _f(ERROR, "cnf.empty")
    else:
        yield _f(NOTE, "cnf.size", clauses=len(clauses),
                 variables=getattr(cnf, "nvars", 0))
    # A counting constraint is what turns `cases` from a decision procedure
    # into an optimiser, and somebody who wrote one is usually asking for the
    # SMALLEST k rather than about one k. The loop they then write reads
    # `unknown_solver` as `unsat` and reports a threshold that is not one --
    # two people wrote exactly that within a day of each other. `bisect` takes
    # a `CNFSpec` from `build(t)` and carries the third state.
    #
    # A NOTE, not a warning: writing `at_most_k` and running `cases` once is a
    # perfectly good thing to do. This is the same shape as `spec.magnitude`,
    # which exists because `order` shipped and the person who needed it did
    # not find it.
    if clauses and _cardinality_bound(cnf):
        yield _f(NOTE, "cnf.cardinality")


CHECKS = {
    "Spec": _check_spec, "MultiSpec": _check_multi, "SweepSpec": _check_sweep,
    "DomainSpec": _check_domain, "LPSpec": _check_lp, "ProofSpec": _check_proof,
    "InductSpec": _check_induct, "BoundSpec": _check_bound,
    "OrderSpec": _check_order, "SOSSpec": _check_sos, "IdealSpec": _check_ideal,
    "NumberSpec": _check_number, "SynthSpec": _check_synth,
    "BisectSpec": _check_bisect, "CNFSpec": _check_cnf, "CNF": _check_cnf,
    "PackingSpec": _check_packing, "EliminateSpec": _check_eliminate,
    "ParametricSpec": _check_parametric,
    "MatrixSpec": _check_matrix,
}
