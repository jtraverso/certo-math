"""The input DSL: Python as the host language.

Design decision: we do not invent a language. A .py file defines a `spec()`
function returning one of the objects below. An LLM writes Python far better
than SMT-LIB, and validation sits on top.
"""
from __future__ import annotations

import hashlib
import os
import sys
import types
from dataclasses import dataclass, field
from pathlib import Path

from .i18n import t


# ---------------------------------------------------------------------------
# prove / check / core
# ---------------------------------------------------------------------------


@dataclass
class Spec:
    """Named hypotheses and one claim.

        s = Spec()
        s.assume("positive", x > 0)
        s.claim(x*x >= 0)
    """

    assumptions: list = field(default_factory=list)  # [(name, expr)]
    goal: object = None
    title: str = ""

    def assume(self, name: str, expr):
        if any(n == name for n, _ in self.assumptions):
            raise ValueError(t("spec.duplicate_hypothesis", name=name))
        self.assumptions.append((name, expr))
        return self

    def claim(self, expr):
        self.goal = expr
        return self

    @property
    def names(self):
        return [n for n, _ in self.assumptions]

    @property
    def formulas(self):
        return [f for _, f in self.assumptions]


# ---------------------------------------------------------------------------
# synth (CEGIS)
# ---------------------------------------------------------------------------


@dataclass
class SynthSpec:
    """There exists an impl. For every input. There exist helpers. All hold.

    impl_vars       what we are looking for (fixed once)
    input_vars      universally quantified (these generate counterexamples)
    helper_vars     existential per input (a fresh copy each round)
    """

    impl_vars: list
    input_vars: list
    helper_vars: list = field(default_factory=list)
    impl_constraints: object = None
    behavior: object = None
    correctness: object = None
    title: str = ""

    # --- universal obligation (for `synth --prove-candidate`) --------------
    # `behavior` is the BOUNDED domain the search runs over. The general
    # statement lives in another domain and often another sort: the search
    # runs over bounded integers, the proof over the reals, which IS
    # decidable for polynomials. So dropping the bounds is not enough.
    #
    #   universal_behavior  expression replacing `behavior`. The simple case.
    #   universal           callable(values: dict) -> Spec. Full control: it
    #                       can change sort and name the hypotheses, so that
    #                       `core` works on them.
    universal_behavior: object = None
    universal: object = None

    def normalized(self):
        import z3

        t = z3.BoolVal(True)
        return (
            self.impl_constraints if self.impl_constraints is not None else t,
            self.behavior if self.behavior is not None else t,
            self.correctness if self.correctness is not None else t,
        )


# ---------------------------------------------------------------------------
# opt (LP / ILP)
# ---------------------------------------------------------------------------


@dataclass
class LPSpec:
    """A linear program in explicit form, so the dual can be emitted.

        lp = LPSpec(sense="max")
        lp.variable("x"); lp.variable("y")
        lp.objective({"x": 3, "y": 5})
        lp.constraint({"x": 1, "y": 1}, "<=", 10, name="capacity")
    """

    sense: str = "max"
    integer: bool = False          # every variable integer; see `kind` below
    title: str = ""
    var_names: list = field(default_factory=list)
    bounds: dict = field(default_factory=dict)
    obj: dict = field(default_factory=dict)
    cons: list = field(default_factory=list)  # [(name, {var: coef}, sense, rhs)]
    kinds: dict = field(default_factory=dict)  # name -> continuous|integer|binary
    target: object = None          # a value `mixed` compares the result against
    # Which constraint names are LOADS rather than resource capacities. Purely
    # informational to the LP -- a row is a row -- and it is what lets the
    # certificate report them separately from the encoding.
    load_names: list = field(default_factory=list)
    # What the rows and columns ARE, when a PackingSpec came from a graph:
    # `PackingSpec.map_payload()`. Carried into the certificate, where
    # `verify` checks the matrix against it.
    meaning: dict = None

    KINDS = ("continuous", "integer", "binary")

    def variable(self, name, lo=0.0, hi=None, kind="continuous"):
        """A variable, and what kind of number it is.

        `integer=True` on the spec makes EVERY variable integer, which is the
        wrong shape for a genuinely mixed problem: a design where the discrete
        part chooses a structure and the continuous part packs inside it has
        both, and forcing the continuous variables to be integers changes the
        problem rather than restricting it.
        """
        if name in self.var_names:
            raise ValueError(t("spec.duplicate_variable", name=name))
        if kind not in LPSpec.KINDS:
            raise ValueError(t("spec.bad_kind", kind=kind,
                               known=", ".join(LPSpec.KINDS)))
        self.var_names.append(name)
        if kind == "binary":
            lo, hi = 0, 1 if hi is None else hi
        self.bounds[name] = (lo, hi)
        self.kinds[name] = kind
        return self

    def kind_of(self, name) -> str:
        """`integer=True` still means what it used to: all of them."""
        if self.integer:
            return "integer"
        return self.kinds.get(name, "continuous")

    @property
    def discrete(self) -> list:
        return [v for v in self.var_names
                if self.kind_of(v) in ("integer", "binary")]

    @property
    def continuous(self) -> list:
        return [v for v in self.var_names if self.kind_of(v) == "continuous"]

    @property
    def is_mixed(self) -> bool:
        return bool(self.discrete) and bool(self.continuous)

    def frozen(self, assignment: dict):
        """The residual LP: the discrete variables fixed, the rest free.

        Returns (LPSpec, constant) where `constant` is the objective the frozen
        variables already contribute. An LPSpec has no constant term, so it
        travels separately rather than being folded in and lost.
        """
        from .exact import to_fraction

        out = LPSpec(sense=self.sense, title=self.title)
        for v in self.continuous:
            lo, hi = self.bounds[v]
            out.variable(v, lo, hi)
        out.objective({v: c for v, c in self.obj.items()
                       if v in set(self.continuous)})
        const = sum((to_fraction(self.obj.get(v, 0)) * to_fraction(assignment[v])
                     for v in self.discrete), to_fraction(0))
        for name, coeffs, sense, rhs in self.cons:
            moved = sum((to_fraction(c) * to_fraction(assignment[v])
                         for v, c in coeffs.items() if v in set(self.discrete)),
                        to_fraction(0))
            rest = {v: c for v, c in coeffs.items()
                    if v not in set(self.discrete)}
            out.constraint(rest, sense, to_fraction(rhs) - moved, name=name)

        # WHICH ROWS ARE LOADS survives a substitution: shifting a right-hand
        # side does not turn an argument about a region into an encoding
        # detail. It used to be dropped, like `PackingSpec.restricted` dropped
        # the loads themselves.
        out.load_names = list(self.load_names)

        # THE TARGET IS SHIFTED, NOT COPIED, and this is the one place in this
        # audit where carrying the field verbatim would have been the WRONG
        # fix. The caller's target is about the whole objective; this spec's
        # objective is missing `const`, the part the frozen variables already
        # contribute. A residual optimum `z` meets the original target `T`
        # exactly when `z + const >= T`, so the residual's target is
        # `T - const`. Copying `T` across would compare a partial sum against
        # a whole one -- a wrong answer rather than a missing one.
        if self.target is not None:
            out.target = to_fraction(self.target) - const

        return out, const

    def relaxed(self):
        """Every variable continuous. The bound over ALL discrete choices.

        THE CONTRACT: a RELAXATION. The feasible set grows, so a maximum
        cannot fall and a minimum cannot rise. Integrality is the only thing
        this drops, and dropping it is the point.

        WHAT TRAVELS, and why it has to. `target` is the question the caller
        asked -- it has nothing to do with integrality, and losing it made
        `meets_target` come back null instead of answered. `load_names` says
        which rows are loads rather than capacities, which is a fact about the
        model and not about whether its variables are whole; losing it stopped
        the certificate pricing them. Both used to be dropped here, found
        while auditing the same defect in `PackingSpec.restricted`.
        """
        out = LPSpec(sense=self.sense, title=self.title)
        for v in self.var_names:
            lo, hi = self.bounds[v]
            out.variable(v, lo, hi)
        out.objective(dict(self.obj))
        for name, coeffs, sense, rhs in self.cons:
            out.constraint(dict(coeffs), sense, rhs, name=name)
        out.target = self.target
        out.load_names = list(self.load_names)
        return out

    def objective(self, coeffs: dict):
        from .exact import to_fraction

        self.obj = {k: to_fraction(v) for k, v in coeffs.items()}
        return self

    def constraint(self, coeffs: dict, sense: str, rhs, name=None):
        """Coefficients and rhs accept int, Fraction, the string '7/12' or float.

        Stored as Fraction: exact in, exact out.
        """
        from .exact import to_fraction

        if sense not in ("<=", ">=", "=="):
            raise ValueError(t("spec.bad_sense", sense=sense))
        name = name or "c{}".format(len(self.cons))
        self.cons.append((name, {k: to_fraction(v) for k, v in coeffs.items()},
                          sense, to_fraction(rhs)))
        return self

    def as_leq_system(self):
        """Normalise to max c.x subject to A x <= b, x >= 0, with A dense.

        Built from `as_leq_sparse`, which is the one definition: two readings
        of the same program are the gap a wrong certificate fits through.
        """
        rows, b, c, names = self.as_leq_sparse()
        from .exact import to_fraction

        Z = to_fraction(0)
        width = len(self.var_names)
        A = []
        for r in rows:
            row = [Z] * width
            for j, v in r.items():
                row[j] = v
            A.append(row)
        return A, b, c, names

    def as_leq_sparse(self):
        """Normalise to max c.x subject to A x <= b, x >= 0.

        Rows are `{column: coefficient}`, non-zeros only. Branch and bound on
        a 1048-column packing spent most of every node materialising the
        dense matrix -- building it, building the solver model from it, and
        checking the answer against it -- for rows that name a handful of
        columns each.

        Variable bounds are materialised as rows of A: otherwise the standard
        dual does not see them and the certificate would be invalid.
        """
        from .exact import to_fraction

        # A name that is not declared would be dropped by `row_of` below --
        # silently, because a missing key is indistinguishable from a zero
        # coefficient once the row is built. That is how one typo turned a
        # certified optimum of 1/3 into a certified 10: the row meant to hold
        # the variable back was not in the program at all, and the certificate
        # was correct about the program that WAS built. Refused here rather
        # than at `constraint()` so declaration order stays free.
        declared = set(self.var_names)
        unknown = {}
        for where, coeffs in ([("objective", self.obj)] +
                              [(name, c) for name, c, _s, _r in self.cons]):
            for key in coeffs:
                if key not in declared:
                    unknown.setdefault(key, []).append(where)
        if unknown:
            raise ValueError(t(
                "spec.undeclared_variable",
                names=", ".join(sorted(unknown)[:4]),
                where=", ".join(sorted({w for ws in unknown.values()
                                        for w in ws})[:4]),
                declared=", ".join(self.var_names[:6]) or "-"))

        A, b, names = [], [], []
        Z = to_fraction(0)
        index = {v: j for j, v in enumerate(self.var_names)}
        def row_of(coeffs):
            row = {}
            for v, c in coeffs.items():
                f = to_fraction(c)
                if f:
                    row[index[v]] = f
            return row

        def neg(row):
            return {j: -x for j, x in row.items()}

        for name, coeffs, sense, rhs in self.cons:
            row = row_of(coeffs)
            if sense == "<=":
                A.append(row); b.append(rhs); names.append(name)
            elif sense == ">=":
                A.append(neg(row)); b.append(-rhs); names.append(name + "_geq")
            else:
                A.append(row); b.append(rhs); names.append(name + "_le")
                A.append(neg(row)); b.append(-rhs); names.append(name + "_ge")

        for v in self.var_names:
            lo, hi = self.bounds.get(v, (0.0, None))
            # Every variable here is x >= 0: the dual certificate is built for
            # that form. `lo=None` -- "free" -- and a negative `lo` were both
            # read as 0 without a word, so `min x` over `x >= -5` with `x`
            # declared free came back "EXACT optimum certified: 0". The
            # certificate was right about the program it solved, and that was
            # not the program written. Refused, and the message says how to
            # write it instead.
            if lo is None or to_fraction(lo) < 0:
                raise ValueError(t("spec.free_variable", var=v,
                                   lo="None" if lo is None else lo))
            if hi is not None:
                A.append(row_of({v: 1})); b.append(to_fraction(hi))
                names.append("bound_{}_hi".format(v))
            if lo is not None and lo > 0:
                A.append(row_of({v: -1})); b.append(-to_fraction(lo))
                names.append("bound_{}_lo".format(v))

        c = [to_fraction(self.obj.get(v, Z)) for v in self.var_names]
        if self.sense == "min":
            c = [-x for x in c]
        return A, b, c, names


# ---------------------------------------------------------------------------
# sweep
# ---------------------------------------------------------------------------


@dataclass
class Outcome:
    """What a sweep predicate may return instead of a bare bool.

        def pred(g):
            ...
            return Outcome(False, cert=dual_cert, detail="ratio 0.9259")

    `ok=None` means "did not conclude": neither true nor false. The sweep
    counts those apart and can no longer claim the property holds family-wide.
    """

    ok: object = None           # True / False / None
    cert: object = None         # the predicate's Certificate, if any
    detail: str = ""
    errored: bool = False
    value: object = None        # value to collect (Fraction, int or float)

    @classmethod
    def clique_partition(cls, graph, parts, at_most=None, max_size=None,
                         limits=None):
        """A predicate's YES, certified in one line: `parts` (vertex sets)
        partition the edges of `graph` into cliques, and -- with `at_most` --
        there are no more than `at_most` of them, and -- with `max_size` --
        none has more than `max_size` vertices. Without `max_size` the ORDER
        of a piece is not bounded: K5 as one part is a partition into one
        clique.

            def pred(g):
                return Outcome.clique_partition(g, my_partition(g), at_most=k)

        `cover` checks it, the certificate travels with the item, and `verify`
        checks it is about THIS graph. A partition that fails -- a part that
        is no clique, an edge missed or doubled, too many parts -- is NOT a
        counterexample: another partition might do, so the answer is "did not
        conclude" (`ok=None`), and the reason is the detail. Only ever a YES:
        a partition bounds the minimum from above and refutes nothing.
        """
        from .engines import algebra

        universe = [tuple(e) for e in graph.edges()]
        spec = CoverSpec(universe=universe, parts=[list(p) for p in parts],
                         cliques=True, exact=True, max_size=max_size)
        res = algebra.cover(spec, limits)
        cert = res.certificate
        if cert is None:
            return cls(None, detail=t("outcome.partition.failed",
                                      detail=res.detail))
        size = cert.payload["size"]
        if at_most is not None:
            cert.payload["at_most"] = int(at_most)
            if size > int(at_most):
                return cls(None, detail=t("outcome.partition.too_many",
                                          size=size, at_most=int(at_most)))
        return cls(True, cert=cert,
                   detail=t("outcome.partition.ok", size=size,
                            bound="" if at_most is None
                            else " <= {}".format(int(at_most))))


@dataclass
class SweepSpec:
    """A predicate and/or a value over an enumerated family of graphs.

    The predicate returns a bool or an `Outcome`. If it returns an Outcome
    carrying a certificate, `sweep` aggregates it and the sweep becomes
    citable.

    CALIBRATION MODE. Often the question is not "does it fail?" but "HOW MUCH
    does it fail, and where is it worst?". For that:

        SweepSpec(n=6, collect=lambda g: ratio(g), worst="min")

    `collect` returns a value per graph (use Fraction so it stays exact) and
    `sweep` reports min, max, mean and the extremes with their graph.
    `predicate` becomes optional: you can calibrate without refuting anything.
    You can also return `Outcome(..., value=...)` from the predicate so
    nothing is computed twice.
    """

    n: int
    predicate: object = None             # callable(Graph) -> bool | Outcome
    filters: list = field(default_factory=list)
    title: str = ""
    describe: object = None              # callable(Graph) -> str, optional
    collect: object = None               # callable(Graph) -> number
    worst: str = "min"                   # which end counts as "worst": min or max
    # `canonicalize(g) -> hashable`, or "auto" for graph isomorphism. The
    # enumerator already returns one graph per isomorphism class, so "auto"
    # buys nothing there -- it is for a FINER symmetry than isomorphism, which
    # is what a coloured, rooted or otherwise decorated sweep has, and for a
    # sweep over a family the enumerator did not produce.
    canonicalize: object = None
    # `labelling(item) -> {source: label}`: the ALTERNATIVE to `canonicalize`,
    # and a different bargain. `canonicalize` hands over a form and asks to be
    # believed; `labelling` hands over the permutation, certo applies it, and
    # the form is what comes out -- so the orbit carries a witness anyone can
    # re-apply instead of a claim. Use it when the canonical labelling comes
    # from a tool built for it: certo's own canonical form refuses outright on
    # a vertex-transitive object. Declaring both is refused.
    labelling: object = None


# ---------------------------------------------------------------------------
# bisect
# ---------------------------------------------------------------------------


@dataclass
class BisectSpec:
    """Find a parameter's threshold.

    `build(t)` returns a Spec (evaluated with prove) or a CNFSpec (with cases,
    where "holds" means UNSAT: no counterexample exists).

    direction:
      "min_true"  the statement holds for LARGE t -> find the smallest t
      "max_true"  it holds for SMALL t -> find the largest t

    Assumes monotonicity in t. That is not verified; if the endpoints do not
    behave as `direction` says, the command says so instead of inventing a
    threshold.
    """

    build: object          # callable(t) -> Spec | CNFSpec
    lo: float
    hi: float
    direction: str = "min_true"
    tol: float = 1e-6
    integer: bool = False
    title: str = ""


# ---------------------------------------------------------------------------
# loading
# ---------------------------------------------------------------------------


def load_spec(path, expected=None, safe=False):
    """Import a .py file and return whatever its `spec()` function returns.

    A `.json` file is read as DATA instead, with nothing executed, and `safe`
    refuses a `.py` outright. The guarantee is exactly "no code from this file
    runs" -- not that the spec means what you think it does, which is what
    `lint` and the scope warnings are for.

    Two things this does NOT do the usual way, both of them on purpose.

    It compiles the source it just read instead of going through the import
    machinery, because that machinery caches bytecode keyed on mtime and size:
    a spec edited within the same second to the same length comes back as the
    OLD code. For a tool whose certificates carry a hash of the spec, running
    something other than the bytes that were hashed is not a performance
    detail -- it is the certificate describing a different program. Verifying
    a sweep by replaying its predicate is exactly where that would bite.

    And it puts the spec's own directory on `sys.path`, the way Python does
    for a script it runs, so a spec can import a helper sitting next to it.
    Without that, splitting a growing spec across two files fails in a way
    that looks like a bug in `certo`.
    """
    p = Path(path).resolve()
    if not p.exists():
        raise FileNotFoundError(t("spec.not_found", path=p))

    # CONFINED, when a root is set: the MCP server sets it to its workspace.
    # The workspace check used to apply to the path a tool was GIVEN, and not
    # to a spec a certificate names inside its payload -- so verifying a
    # certificate inside the workspace ran a spec outside it. Every load goes
    # through here, so every load is confined.
    root = os.environ.get("CERTO_SPEC_ROOT", "").strip()
    if root:
        r = Path(root).resolve()
        if p != r and r not in p.parents:
            raise PermissionError(t("spec.outside_root", path=str(p),
                                    root=str(r)))

    if p.suffix.lower() == ".json":
        from .dataspec import load as _load_data
        return _load_data(p, expected)
    # The environment can force it for a whole process, which is how the MCP
    # server is protected with one line in `.mcp.json` rather than a parameter
    # on each of forty-six tools -- and a setting a caller cannot forget.
    if safe or os.environ.get("CERTO_NO_EXEC", "").strip() not in ("", "0"):
        from .dataspec import BUILDABLE
        raise PermissionError(t("spec.exec_refused", path=p.name,
                                known=", ".join(BUILDABLE)))

    here = str(p.parent)
    if here not in sys.path:
        sys.path.insert(0, here)

    source = p.read_bytes()
    name = "certo_spec_" + hashlib.sha256(str(p).encode()).hexdigest()[:12]
    mod = types.ModuleType(name)
    mod.__file__ = str(p)
    mod.__dict__["__builtins__"] = __builtins__
    sys.modules[name] = mod            # so dataclasses and typing resolve
    try:
        exec(compile(source, str(p), "exec"), mod.__dict__)
    finally:
        sys.modules.pop(name, None)

    if not hasattr(mod, "spec"):
        raise AttributeError(t("spec.no_function", name=p.name))
    obj = mod.spec()
    if expected is not None and not isinstance(obj, expected):
        raise TypeError(t("spec.wrong_type", got=type(obj).__name__,
                          want=expected.__name__))
    return obj


# ---------------------------------------------------------------------------
# sweep over an arbitrary finite domain
# ---------------------------------------------------------------------------


@dataclass
class DomainSpec:
    """A predicate and/or a value over ANY finite domain, not just graphs.

    Graphs are one domain among many. The same exhaustive pattern applies to
    parameter pairs, residue classes, separator sizes, multiplicity vectors --
    anything you can enumerate:

        DomainSpec(
            items=[(s, r) for s in range(2, 8) for r in range(2, 8)],
            predicate=lambda p: bound_holds(*p),
            collect=lambda p: ratio(*p),
            key=lambda p: "s={},r={}".format(*p),
        )

    `key` turns an item into a stable string id: it is what lands in the
    certificate, so it has to identify the item unambiguously.

    `reduce` is what `shrink` needs: given an item, the items one step
    "smaller". Pass a callable, or the name of a standard reducer:

        reduce="auto"          pick from the item's type, or refuse
        reduce="sets"          drop one element
        reduce="sequences"     drop one element of a list or tuple
        reduce="decrement"     lower one integer coordinate by one
        reduce="graphs"        delete one vertex
        reduce="masks"         clear one set bit
        reduce=lambda p: [(p[0] - 1, p[1]), (p[0], p[1] - 1)]

    `auto` refuses on a type it does not recognise instead of inventing a
    reduction: a witness that is minimal for the wrong relation looks exactly
    like one that is minimal for the right one.

    The reduced items do not have to be inside `items`: the sweep domain is
    often a window, and the interesting reduction may leave it.
    """

    # `canonicalize(item) -> hashable`, equal exactly for items in the same
    # orbit of whatever symmetry the domain has. Nothing needs to know the
    # group; it needs to know when two items are the same object relabelled.
    # With it, a sweep reports labelled count, orbit count and a
    # representative per orbit -- and `--by-orbit` will evaluate one item per
    # orbit instead of all of them.
    items: object                        # iterable, or callable() -> iterable
    predicate: object = None             # callable(item) -> bool | Outcome
    collect: object = None               # callable(item) -> number
    key: object = None                   # callable(item) -> str (default: str)
    describe: object = None              # callable(item) -> str, optional
    reduce: object = None                # callable(item) -> iterable, or a name
    canonicalize: object = None          # callable(item) -> hashable orbit key
    # `labelling(item) -> {source: label}`: the ALTERNATIVE to `canonicalize`,
    # and a different bargain. `canonicalize` hands over a form and asks to be
    # believed; `labelling` hands over the permutation, certo applies it, and
    # the form is what comes out -- so the orbit carries a witness anyone can
    # re-apply instead of a claim. Use it when the canonical labelling comes
    # from a tool built for it: certo's own canonical form refuses outright on
    # a vertex-transitive object. Declaring both is refused.
    labelling: object = None
    worst: str = "min"
    title: str = ""

    def enumerate(self):
        it = self.items() if callable(self.items) else self.items
        return list(it)

    def id_of(self, item) -> str:
        """The item's id: the spec's `key`, or the item's own.

        A native type knows how to name itself, so a DomainSpec over one needs
        no `key` at all -- and asking the item beats a registry keyed on type,
        because anyone's class can join by having the method.
        """
        if self.key is not None:
            return str(self.key(item))
        own = getattr(item, "key", None)
        return str(own()) if callable(own) else str(item)

    def reducer(self):
        """The reduce function, resolving a catalogue name if that is what it is."""
        from .reducers import resolve

        return None if self.reduce is None else resolve(self.reduce)


# ---------------------------------------------------------------------------
# core over several goals at once
# ---------------------------------------------------------------------------


@dataclass
class MultiSpec:
    """The same named hypotheses against SEVERAL named goals.

        s = MultiSpec()
        s.assume("r_ge_3", r >= 3)
        s.assume("d_ge_1", d >= 1)
        s.claim("identity",   lhs == rhs)
        s.claim("positivity", lhs >= 0)

    `core` then reports a hypothesis-by-goal table: which hypotheses each goal
    actually needs. A hypothesis irrelevant to the identity but necessary for
    positivity is the kind of thing that decides how small a Lean interface
    can be, and it is invisible when the goals are checked one at a time.
    """

    assumptions: list = field(default_factory=list)   # [(name, expr)]
    goals: list = field(default_factory=list)         # [(name, expr)]
    title: str = ""

    def assume(self, name: str, expr):
        if any(n == name for n, _ in self.assumptions):
            raise ValueError(t("spec.duplicate_hypothesis", name=name))
        self.assumptions.append((name, expr))
        return self

    def claim(self, name: str, expr):
        if any(n == name for n, _ in self.goals):
            raise ValueError(t("spec.duplicate_goal", name=name))
        self.goals.append((name, expr))
        return self

    def single(self, goal_name: str) -> "Spec":
        """The Spec for one goal, so each column is an ordinary `core` run."""
        s = Spec(title="{} [{}]".format(self.title, goal_name))
        for n, f in self.assumptions:
            s.assume(n, f)
        for n, f in self.goals:
            if n == goal_name:
                return s.claim(f)
        raise KeyError("no goal named " + goal_name)

    @property
    def names(self):
        return [n for n, _ in self.assumptions]

    @property
    def goal_names(self):
        return [n for n, _ in self.goals]


# ---------------------------------------------------------------------------
# bounds: a numeric quantity, rigorously enclosed
# ---------------------------------------------------------------------------


@dataclass
class BoundSpec:
    """A real quantity and the bound claimed about it, computed rigorously.

        BoundSpec(
            value=lambda m: m.exp(1) / m.pi,
            claim=("<", "0.866"),
        )

    `value` receives a namespace of RIGOROUS constants and functions: every
    operation returns an enclosure, so an inequality that holds for the whole
    enclosure holds for the number. Python floats raise rather than quietly
    narrowing the claim to a nearby dyadic -- write `m("0.1")`, which is one
    tenth, not `0.1`, which is not.

    `claim` is a relation against an EXACT rational, written as a string:
    ("<", "1/3"), ("<=", "0.5"), (">", "0"), (">=", ...), ("!=", "0") for a
    sign determination, or ("in", lo, hi). Leave it out to measure rather than
    decide: the certificate then records the enclosure that was reached.

    Precision is the work budget here, the way rlimit is for z3: the search
    doubles it until the enclosure settles the claim or `max_prec` is hit, and
    hitting it is reported as "did not settle", never as "false".
    """

    value: object                    # callable(m) -> an enclosure
    claim: object = None             # (rel, rational) | ("in", lo, hi) | None
    prec: int = 128                  # starting precision, in bits
    max_prec: int = 16_384
    describe: str = ""               # what the quantity IS, for the write-up
    title: str = ""


# ---------------------------------------------------------------------------
# compose: lemmas, each backed by a certificate, and the theorem they prove
# ---------------------------------------------------------------------------


@dataclass
class Lemma:
    """One step of a proof, and the certificate that discharges it.

    Either `proves` (a Spec to discharge right now) or `certificate` (a path
    to one already on disk) plus `states` (what it licenses you to assume).
    """

    name: str
    proves: object = None            # a Spec, discharged now
    via: str = "prove"               # "prove" | "farkas" | "nlinarith"
    certificate: str = ""            # a certificate already on disk
    states: object = None            # the formula this lemma contributes
    bridge: str = ""                 # prose: why that certificate says that
    # A CITED lemma: a statement certo cannot recompute -- a section of a
    # paper, a lemma proved elsewhere -- used on the strength of `cited`, which
    # says where it comes from. Recorded and repeated, never checked.
    cited: str = ""
    # WHAT THIS LEMMA IS ABOUT, as (kind, id): ("cone", "sigma_1"), ("graph",
    # "K7"), ("lp", "residual"). Free text, declared and never inferred --
    # guessing the object is the mistake this exists to catch.
    subject: object = None
    # The named map, when this lemma's subject is not the theorem's. certo
    # does not check the map; it refuses to let the change be silent.
    transport: str = ""

    @property
    def is_bridge(self) -> bool:
        return self.proves is None


@dataclass
class ProofSpec:
    """Lemmas, the theorem, and the step that joins them.

        p = ProofSpec(title="...")
        p.assume("x_pos", x > 0)                 # hypothesis of the THEOREM
        p.lemma("amgm", proves=sub_spec)         # discharged now, by `prove`
        p.lemma("tight", proves=other, via="farkas")
        p.lemma("k6", certificate="certs/drat-1a2b.json",
                states=phi,                      # what it licenses
                bridge="every 2-colouring of K6 has a mono triangle")
        p.conclude(theorem)

    The point is not that the lemmas hold -- each certificate already says
    that. It is that **the statement used downstream is the statement the
    certificate establishes**, which is where hand-assembled proofs go wrong:
    a lemma proved under one hypothesis and used under another.

    A lemma given by `certificate=` is a BRIDGE: the certificate is verified,
    but nothing can check that it licenses `states`, because a finite sweep or
    a DRAT proof is not a first-order formula. Bridges are recorded by name
    and reported every time the proof is verified. Making them visible is the
    whole reason they are allowed at all.
    """

    lemmas: list = field(default_factory=list)
    assumptions: list = field(default_factory=list)   # [(name, expr)]
    goal: object = None
    title: str = ""
    # What the THEOREM is about, as (kind, id). A lemma whose subject differs
    # from this one has crossed a level, and must say by which map.
    subject: object = None

    def lemma(self, name, proves=None, via="prove", certificate="",
              states=None, bridge="", subject=None, transport=""):
        if any(l.name == name for l in self.lemmas):
            raise ValueError(t("spec.duplicate_lemma", name=name))
        if proves is None and not certificate:
            raise ValueError(t("spec.lemma_no_source", name=name))
        if proves is None and states is None:
            raise ValueError(t("spec.lemma_no_statement", name=name))
        if subject is not None and (not isinstance(subject, (tuple, list))
                                    or len(subject) != 2):
            raise ValueError(t("spec.bad_subject", name=name))
        self.lemmas.append(Lemma(name=name, proves=proves, via=via,
                                 certificate=certificate, states=states,
                                 bridge=bridge,
                                 subject=tuple(subject) if subject else None,
                                 transport=transport))
        return self

    def assume(self, name: str, expr):
        if any(n == name for n, _ in self.assumptions):
            raise ValueError(t("spec.duplicate_hypothesis", name=name))
        self.assumptions.append((name, expr))
        return self

    def conclude(self, expr):
        self.goal = expr
        return self

    @property
    def names(self):
        return [n for n, _ in self.assumptions]

    def cite(self, name, states, source, subject=None, transport=""):
        """A lemma certo CANNOT recompute, used on the strength of `source`.

        For a chain of bounds that rests on a published section, or on a
        result proved in another tool: the statement enters the final step
        like any lemma, and the proof is then true RELATIVE to it. Nothing
        checks it -- that is the point of saying so -- and every verification
        of the proof lists it, with its source, and says whether the final
        step actually used it.
        """
        if any(l.name == name for l in self.lemmas):
            raise ValueError(t("spec.duplicate_lemma", name=name))
        if states is None:
            raise ValueError(t("spec.lemma_no_statement", name=name))
        if not str(source or "").strip():
            raise ValueError(t("spec.cite_no_source", name=name))
        if subject is not None and (not isinstance(subject, (tuple, list))
                                    or len(subject) != 2):
            raise ValueError(t("spec.bad_subject", name=name))
        self.lemmas.append(Lemma(name=name, states=states,
                                 cited=str(source).strip(),
                                 subject=tuple(subject) if subject else None,
                                 transport=transport))
        return self

    @property
    def lemma_names(self):
        return [l.name for l in self.lemmas]


# ---------------------------------------------------------------------------
# induct: base cases plus a step, and the join between them
# ---------------------------------------------------------------------------


@dataclass
class InductSpec:
    """Finite base cases, an inductive step, and the chain they form.

        p = InductSpec(
            k0=3, base_upto=8,
            base=lambda k: SweepSpec(n=k, predicate=...),   # or a cert path
            step=step_spec,          # assume P(k), k >= step_from; claim P(k+1)
            step_from=3,
            bridge="the sweep checks every graph on k vertices; reading that "
                   "as P(k) is what the encoding means",
        )

    `base` is a callable k -> spec, a dict {k: spec}, or a path to a stored
    certificate. Anything finite -- a sweep, a DRAT proof, a plain `prove`.

    `step` is an ordinary `Spec` over a FREE k. A proof with a free variable
    is a proof for every value of it, which is what the schema needs; there is
    no quantifier to give a solver.

    What this buys over running the two halves separately is the join: that
    the base cases are exactly k0..base_upto with no gap, and that the step
    starts no later than the base ends. A base covering 3..8 with a step valid
    only from k >= 10 proves nothing, and reads identically in prose.
    """

    k0: int
    base_upto: int
    base: object                     # callable(k) -> spec | {k: spec} | path
    step: object                     # a Spec over a free k
    step_from: object = None         # defaults to k0
    # The induction variable, when the step's goal mentions more than one
    # integer: `P(k)` is read off the goal `P(k+1)` by substituting k -> k-1,
    # so the step certo proves is exactly (k >= step_from and P(k)) -> P(k+1).
    k: object = None
    bridge: str = ""                 # how a finite check becomes P(k)
    describe: str = ""               # the conclusion, in words
    title: str = ""


# ---------------------------------------------------------------------------
# polynomial ideals, sums of squares, and integers
# ---------------------------------------------------------------------------


@dataclass
class IdealSpec:
    """Polynomial equations, and what follows from them.

        IdealSpec(
            variables=["x", "y"],
            equations=[x*x + y*y - 1, x - 2],     # z3 terms, or Poly
            claim=None,                           # None = "no solution at all"
        )

    With `claim=None` the question is whether the system is INCONSISTENT, and
    the certificate is cofactors with `1 = sum h_i g_i`. With a claim `f`, the
    question is whether `f` vanishes on every common root, certified the same
    way: `f = sum h_i g_i`.

    The field matters and the certificate says so. `1 = sum h_i g_i` refutes
    solutions over the COMPLEX numbers, hence over the reals, the rationals
    and the integers. The converse does not hold: a proper ideal does not mean
    a real solution exists, only that a complex one might.
    """

    variables: list
    equations: list                  # z3 terms or Poly, each meaning "= 0"
    claim: object = None             # a z3 term or Poly, or None
    max_pairs: int = 20_000
    title: str = ""


@dataclass
class CoverSpec:
    """A universe, and parts that are supposed to cover it exactly once each.

        CoverSpec(universe=edges, parts=[[e1, e2, e3], [e4, e5]])

    For a CLIQUE PARTITION of a graph, give the graph's edges as the universe
    and the parts as VERTEX SETS, with `cliques=True`: each one is then
    expanded to its own edges and refused unless every pair really is present.
    A part that is not a clique would still cover edges, and the cover would
    verify, and the object would not be what it claims.

        CoverSpec(universe=edges, parts=[[0,1,2], [3,4]], cliques=True)

    `exact=False` asks only that every element is covered at least once, which
    is a weaker and different claim; the certificate records which one was
    made rather than letting a reader assume.

    This certifies a cover you have. Finding a minimum one is NP-hard and not
    this command's job -- pair it with `opt` on the same universe for the
    lower bound, the way `opt --gap` pairs the two sides for a packing.
    """

    universe: object                 # iterable of hashable elements
    parts: list                      # iterable of parts, or of vertex sets
    cliques: bool = False            # parts are vertex sets of a graph
    exact: bool = True               # exactly once, rather than at least once
    max_size: object = None          # optional cap on a part's vertex count
    title: str = ""
    # The pool `parts` was chosen from: every part you would ALLOW. Needed by
    # `--optimize` and by nothing else, because "minimum" only means anything
    # relative to what was available. There is no sensible default -- the set
    # of all cliques is usually enormous and rarely what anyone meant -- so it
    # is refused rather than guessed.
    candidates: object = None

    def to_lp(self, integral: bool = False):
        """The exact-cover LP: choose the fewest candidates covering everything.

        One variable per candidate, one row per universe element, and the row
        is an EQUALITY when `exact` -- which is the whole difference between a
        partition and a cover, and the thing a relaxation written by hand gets
        wrong.
        """
        from .cover import _key, edges_of
        from .spec import LPSpec

        if not self.candidates:
            raise ValueError(t("cover.no_candidates"))

        pool = list(self.candidates)
        if self.cliques:
            pool = [edges_of(vs) for vs in pool]

        lp = LPSpec(sense="min", title=self.title or "minimum exact cover")
        for i, _ in enumerate(pool):
            lp.variable("part{}".format(i), 0, 1,
                        kind="binary" if integral else "continuous")
        lp.objective({"part{}".format(i): 1 for i in range(len(pool))})

        covers: dict = {}
        for i, part in enumerate(pool):
            for elem in part:
                covers.setdefault(_key(elem), []).append(i)
        for elem in self.universe:
            k = _key(elem)
            lp.constraint({"part{}".format(i): 1 for i in covers.get(k, ())},
                          "==" if self.exact else ">=", 1, name=str(k))
        return lp


@dataclass
class ParametricSpec:
    """An LP whose data are POLYNOMIALS in a parameter, and a dual to check.

        from certo.polynomials import Poly

        RING = ("p",)
        p = Poly.var(RING, "p")
        K = lambda c: Poly.const(RING, c)      # a constant IN THE RING

        ParametricSpec(
            parameters={"p": 10},              # name -> lower bound
            objective={"x": K(1), "y": p - K(5)},
            constraints=[("cap", {"x": K(1), "y": K(1)}, "<=", p * p)],
            dual={"cap": Fraction(1, 3)},
        )

    Coefficients are `Poly` over the parameter ring, or z3 terms in the
    parameter symbols. A bare `z3.RealVal(3)` is neither and raises: it has no
    ring to live in, and guessing one would be guessing which parameters the
    problem has.

    Certifies `opt(p) <= b(p).y` for EVERY `p` at or above the bound, which is
    the jump a finite sweep cannot make. Coefficients are z3 terms in the
    parameter symbols, or `Poly` over the same ring.

    The dual is an INPUT, not something this searches for. Solve one instance
    with `opt`, read the dual off, hand it over. Finding a `y` can be as
    numeric as it likes; checking one is arithmetic, and that split is the
    whole design -- the same one `farkas` makes with its multipliers.

    TWO SHAPES. `sense="max"` wants `<=` rows and certifies `opt(p) <= b(p).y`
    -- a packing, bounded from above. `sense="min"` wants `>=` rows and
    certifies `opt(p) >= b(p).y` -- a symmetrised COVER program, bounded from
    below by a feasible packing. Mixing the rows of one shape into the other is
    refused rather than silently reinterpreted.

    A dual entry may be a `Poly` rather than a rational. It usually has to be
    in the cover shape: the dual there is a packing, and a packing of a growing
    object grows with it. `y >= 0` is then the same shift test as everything
    else.

    `region` widens what a certificate can cover past a BOX. The shift test
    proves non-negativity on `p >= p0`, so a branch has to be re-coordinatised
    into a corner -- and a branch cut out by a curve, `q d + d r >=
    d(d-1) + r(r-1)` say, has no such coordinates. Declaring it

        region=[("separated_wins", q*d + d*r - d*(d-one) - r*(r-one))]

    puts `g >= 0` in the certificate's SCOPE: the bound is claimed where the
    box AND the region hold, and `verify` repeats both every time. Nothing
    here proves `g >= 0`; it is a statement about which instances are meant,
    the way the floors already are.

    What certo does find is the MULTIPLIERS -- non-negative `lambda` with
    `residual - sum(lambda_k g_k)` non-negative by shift -- because that
    search is a linear program, which is the one kind of search this project
    does on its own. Pairwise products of the declared conditions are derived
    rather than assumed.

    EQUALITY ROWS AND FREE VARIABLES. A `"=="` row has a dual of either sign,
    so its `y >= 0` is not asked. A variable named in `free` has no sign, so
    its column must balance exactly -- the residual identically zero -- rather
    than be non-negative. Neither needs a variable split into `p - n`.

    `claim=T` states the bound you want: the certificate then proves
    `b(p).y <= T(p)` too (`>=` for a minimisation), by the same shift test.

    `primal={var: x(p)}` instead of `dual` proves the OTHER direction: every
    row holds and every non-free `x >= 0` for all p in the region, so the
    optimum is at least `c(p).x(p)` for a maximisation and at most it for a
    minimisation. Any row sense is allowed there, since feasibility is all
    that is checked.

    `box={p: (lo, hi)}` claims the bound on a BOX, and decides every
    non-negativity by Bernstein coefficients there -- no reparametrisation of
    a bounded interval into a ray. `subdivide=d` lets a box be halved up to d
    times where the coefficients are not all >= 0, and the certificate
    records the splits. `dual="bernstein"` has certo find a polynomial dual of
    degree `dual_degree` per parameter, by ONE exact LP over its Bernstein
    coefficients; it is checked like any other dual.
    """

    parameters: dict                 # name -> lower bound (a number)
    objective: dict                  # variable -> coefficient polynomial
    constraints: list                # [(name, {var: coef}, "<=", rhs)]
    dual: dict = None                # constraint name -> non-negative rational
    sense: str = "max"
    region: list = None              # [(name, g)] meaning `g(p) >= 0`, SCOPE
    title: str = ""
    # Variables with no sign: their column must BALANCE, `A^T y = c`
    # identically, instead of `A^T y >= c`. Saves splitting each into p - n.
    free: list = None
    # A target `T(p)`: the certificate then also proves `bound <= T` on the
    # region (`>=` for a minimisation), by the same shift test, instead of the
    # target being encoded as a variable and two rows.
    claim: object = None
    # A PRIMAL instead of a dual: `x(p)` feasible for every p, which bounds
    # the other way -- a minimisation from ABOVE, a maximisation from below.
    primal: dict = None
    # A BOX, {p: (lo, hi)}: every non-negativity is then decided by Bernstein
    # coefficients on it instead of the shift test on p >= p0, and
    # `dual="bernstein"` has certo FIND a polynomial dual of `dual_degree`.
    box: dict = None
    subdivide: int = 0               # how many times a box may be halved
    dual_degree: int = 1


@dataclass
class EntrySpec:
    """The first index where a sequence crosses a threshold, and the window.

        EntrySpec(
            values=[Fraction(i, 10) for i in range(20)],
            threshold=Fraction(1, 2),
            step_bound=Fraction(1, 10),      # optional
        )

    Two claims, and the second is the one that carries the weight: it crosses
    at `k`, and it had NOT crossed at any `j < k`. An off-by-one, or a `<=`
    where the argument needed `<`, and the "first" index is not first.

    The certificate carries `a_0 .. a_k` and nothing past it, because nothing
    past it is part of either claim -- and the tail is usually where the
    length is.

    `step_bound` buys the WINDOW. With `|a_{j+1} - a_j| <= delta` the crossing
    lands inside `[threshold, threshold + delta)`, because the step before it
    was on the near side. Only the last step is used for that, though `delta`
    is checked against every step of the prefix: a bound that fails earlier is
    a bound somebody got wrong.

    `direction` is `"up"` or `"down"`; `strict` picks `>` over `>=`.
    """

    values: object                   # iterable of rationals, or callable()
    threshold: object
    direction: str = "up"            # "up" crosses from below
    strict: bool = False             # `>` rather than `>=`
    step_bound: object = None        # |a_{j+1} - a_j| <= this
    title: str = ""




@dataclass
class ParametricSymmetrySpec:
    """A symmetric FAMILY: orbits with polynomial multiplicities, and rows
    that exist only where they exist.

        RING = ("p", "q")
        p, q = Poly.var(RING, "p"), Poly.var(RING, "q")
        K = lambda c: Poly.const(RING, c)

        ParametricSymmetrySpec(
            parameters=("p", "q"),
            orbits={"clique": (p*p - p).scaled(Fraction(1, 2)),
                    "cross": p * q},
            rows=[("KKK", {"clique": K(3)}, ">=", K(1), [p - K(3)]),
                  ("KKI", {"clique": K(1), "cross": K(2)}, ">=", K(1),
                   [p - K(2), q - K(1)])],
            sense="min",
            instance=lambda p, q: (cover_lp(p, q), generators(p, q)),
            window=[(a, b) for a in range(2, 7) for b in range(0, 7)],
        )

    `reduce` closes the averaging bridge on ONE program. This closes it for a
    family: a write-up does not symmetrise `S(6,3)`, it symmetrises `S(p,q)`
    and writes the answer as a formula.

    THE OBJECTIVE IS NOT DECLARED. Substituting one variable per orbit into
    `sum_e z_e` gives `sum_o |o| . x_o`, so the objective IS the
    multiplicities. Declaring it separately would let it disagree with them.

    A ROW CONDITION is a polynomial meant to be `>= 0` -- "present only when
    p >= 3" is `p - 3`. An orbit is present exactly where its multiplicity is
    positive, and a row is dropped when its conditions fail OR when every
    orbit it mentions has vanished.

    `instance` returns `(LPSpec, generators)` at a parameter point, built from
    the OBJECTS rather than from the declaration -- that is what makes the
    declaration falsifiable, and it is refused without one. `window` is where
    the two are compared; the step from the window to the whole region is
    named in the certificate and is not claimed to be proved.
    """

    parameters: tuple                # ("p", "q")
    orbits: dict                     # name -> multiplicity polynomial
    rows: list                       # (name, {orbit: coef}, sense, rhs, [when])
    sense: str = "min"
    instance: object = None          # callable(**values) -> (LPSpec, gens)
    window: object = ()              # [(p, q), ...] or [{"p": .., "q": ..}]
    title: str = ""


@dataclass
class LinearSystemSpec:
    """`A x = b`, solved exactly, with a witness either way.

        LinearSystemSpec(
            matrix=[[2, 1], [1, 3]],
            rhs=[5, 10],
        )

        LinearSystemSpec(matrix=A, rhs=b, domain="integer")

    Entries are integers or `Fraction`; a float is refused rather than
    converted, because a system read from floating point is a different
    system. Over `domain="integer"` the Smith normal form decides it, and
    "no integer solution" is a different answer from "no solution".

    Three outcomes, kept apart. A UNIQUE solution. UNDERDETERMINED, reported
    as a particular solution plus a basis of the kernel -- the solution SET,
    because reporting one point of an affine subspace as though it were the
    answer is how a free parameter disappears from a write-up. And NONE, with
    `y` such that `y.A = 0` and `y.b != 0`, so a negative result is checkable
    too.

    IT ESTABLISHES NEITHER NON-NEGATIVITY NOR, over the rationals,
    INTEGRALITY, and `verify` says so every time. A rational solution to the
    equations of a packing is not a packing.
    """

    matrix: object                   # list of lists of int or Fraction
    rhs: object                      # list of int or Fraction
    domain: str = "rational"         # rational | integer
    title: str = ""


@dataclass
class EquitableQuotientSpec:
    """A program, a partition of its rows and columns, and the equivalence.

        EquitableQuotientSpec(
            lp=physical,
            rows={"e_A0_B0": "AB", ...},        # resource -> class
            columns={"x_A0_B0_C0": "k3_111000", ...},   # object -> class
        )

    `reduce` certifies a symmetry argument and then compares optima. Comparing
    two computed optima does not show a reduction is correct -- it shows two
    numbers agreed, which a wrong reduction with a compensating error also
    does. This certifies the stronger and easier statement instead: the
    physical program and the quotient have the SAME SET of attainable values,
    by an explicit projection and lifting. Equality of optima is a corollary.

    THE PARTITION IS AN INPUT. A group action produces one -- that is what
    `reduce` is -- and so does a colour refinement, or a person who knows what
    the classes are. Separating the finite-sum core from the group theory is
    what a proof assistant wants anyway, and it means a partition nobody can
    name a group for is still certifiable.

    WHAT IS CHECKED, against the matrix and not assumed: that the classes are
    a partition with no empty fibre; that capacities and senses are constant
    on row classes and weights and bounds on column classes; and REGULARITY
    in both directions -- every resource of a class is used by the same amount
    of every object class, and every object of a class uses the same amount of
    every resource class. The double count `N_i H_ij = M_j B_ij` ties the two
    and is checked as well.

    A partition failing any of them is refused, naming the two rows that
    disagree. That is not a formality: one edge given capacity zero among
    capacity-one edges breaks it, and the aggregated program would otherwise
    report an optimum the physical program cannot attain.
    """

    lp: object                       # an LPSpec, or anything with `to_lp`
    rows: dict                       # physical row name -> class name
    columns: dict                    # physical column name -> class name
    title: str = ""


@dataclass
class ConeSpec:
    """A local toric cone, and the numbers two geometric theorems consume.

        ConeSpec(
            rays={"v0": (4,0,0,0), "m01": (2,2,0,0),
                  "m02": (2,0,2,0), "b": (1,1,1,1)},
            lattice=[[4,0,0,0], [2,2,0,0], [2,0,2,0], [1,1,1,1]],
            subdivision={"bary": (1,1,1,1)},
        )

    Computes, exactly and without a solver: whether each generator is
    PRIMITIVE, the MULTIPLICITY (the index of the sublattice they span), the
    HEIGHT functional `u` with `<u, v> = 1` on every generator, and the
    DISCREPANCY `<u, w> - 1` of any ray you name.

    THE LATTICE IS DECLARED, NEVER GUESSED, and it changes the answer rather
    than the error message. One real cell has multiplicity 16 read in `Z^4`
    and 1 read in the lattice its generators are primitive in. Omit `lattice`
    and the ambient `Z^n` is used and said so.

    `subdivision` names rays that are not generators -- the barycentre is the
    usual one -- and asks for their height and discrepancy. Zero is crepant.

    IT DOES NOT PROVE THE GEOMETRY. That multiplicity one gives a smooth
    chart, that discrepancy zero gives a crepant modification, that the fibre
    is SNC or reduced: those are the theorems, and they are why the proof
    assistant is there. This is the data they consume, stopped from being
    assumed.
    """

    rays: dict                       # name -> integer coordinates
    lattice: object = None           # a basis, as rows; None means Z^n
    subdivision: dict = None         # name -> coordinates, for discrepancies
    order: object = None             # the order the generators are read in
    title: str = ""


@dataclass
class CliqueLPSpec:
    """An LP over EVERY clique of a graph, one row per edge, solved without
    listing the cliques.

        CliqueLPSpec(
            edges=[(0, 1), (0, 2), (1, 2), (2, 3)],
            problem="partition",           # packing | cover | partition
            weight={"constant": 1},        # w(Q) = a|E(Q)| + b|Q| + c
            min_size=2,
        )

    `packing` maximises `sum w(Q) x_Q` with each edge's load at most `rhs`;
    `cover` minimises with each at least `rhs`; `partition` minimises with each
    exactly `rhs`. `weight` takes `edges`, `vertices` and `constant`, so
    `{"edges": 1, "constant": -1}` is "edges covered minus one per clique" and
    `{"constant": 1}` counts cliques. `rhs` is one number for every edge, or a
    dict keyed `"u-v"`.

    The columns are generated, not listed: the cliques that enter the LP are
    the ones an exact pricing search finds with positive reduced cost, and the
    certificate proves no other clique has one -- by a search the verifier
    runs again, not by a claim. `vertices` fixes their order; by default it is
    every endpoint, integers read as integers.
    """

    edges: object
    problem: str = "packing"
    weight: object = None
    min_size: int = 2
    rhs: object = 1
    vertices: object = None
    title: str = ""
    # The family bounded from above too -- only edges and triangles, say.
    max_size: object = None


@dataclass
class AtlasSpec:
    """A parameter domain covered by boxes, each certified on its own, and
    ONE statement for the whole.

        AtlasSpec(domain={"p": (0, 1), "q": (0, 1)},
                  region=[("below", p - q)],
                  claim=T,
                  pieces=["out/box1.json", ParametricSpec(...), ...])

    `pieces` are parametric certificates: paths (referenced by digest, so a
    large atlas need not carry them), Certificates or ParametricSpecs (run
    and embedded). `cited` covers boxes by an external result instead:
    `[({"p": (a, b), ...}, "source"), ...]`, and makes the statement relative.
    """

    domain: dict
    pieces: list = field(default_factory=list)
    region: list = field(default_factory=list)
    claim: object = None
    cited: list = field(default_factory=list)
    title: str = ""


@dataclass
class ProfileSpec:
    """How an optimum responds to ONE capacity, as a certified function.

        ProfileSpec(
            columns={"012": {"01": 1, "02": 1, "12": 1}, ...},
            gain={"012": 2, ...},
            capacity={"02": 1, "12": 1, ...},     # every row EXCEPT the one below
            parameter="01",
            domain=(0, 1),
            segments=[{"from": 0, "to": "1/2", "dual": {"01": 3, ...}},
                      {"from": "1/2", "to": 1, "dual": {"01": 1, ...}}],
            sources={0: {"023": 1, ...}, "1/2": {...}, 1: {...}},
        )

    NOT `ParametricSpec`. That one certifies a BOUND for a whole family, with
    the parameter in the data. This certifies a FUNCTION -- concave, piecewise
    affine -- of one capacity, and the answer has breakpoints.

    WHAT IT DECIDES. `f(t) = alpha + beta t` on each segment, and hence on all
    of `[lo, hi]`. Three finite facts give a statement about a continuum: a
    dual bounds EVERY `t` at once, because its feasibility `A^T y >= c` never
    mentions the capacities; two sources at a segment's ends attain the whole
    segment, because interpolating them is feasible at the interpolated
    capacity with the interpolated value; and sorted segments sharing their
    endpoints tile the domain.

    EVERYTHING IS SUPPLIED AND EVERYTHING IS CHECKED. Breakpoints, duals and
    sources are input -- finding them is parametric programming, and any
    solver may do it. `alpha`, `beta` and every value are recomputed from the
    columns; nothing stated is believed.

    A PROFILE IS ABOUT ITS COLUMN SET. That the columns are all the columns,
    or that the rows mean what their names suggest, is a separate obligation
    and this does not discharge it.
    """

    columns: dict                    # name -> {row: coefficient}
    gain: dict                       # name -> objective coefficient
    capacity: dict                   # row -> capacity, for every row but one
    parameter: str = ""              # the row whose capacity is `t`
    domain: object = None            # (lo, hi); default (0, 1)
    segments: object = None          # [{from, to, dual}]
    sources: object = None           # {t: {column: mass}}
    title: str = ""


@dataclass
class SemigroupSpec:
    """An affine semigroup `S = N.a_1 + ... + N.a_k`, and the finite questions
    about it.

        SemigroupSpec(
            generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            points={"w": (1, 2)},
        )

    THE GAP IT FILLS. `cone` answers questions about the RATIONAL cone over
    these generators. A semigroup is what you can actually reach by ADDING
    them, and the difference is where normality lives: `w` above is in the
    cone, and in the group generated by `a`, `b`, `c`, and is not a
    non-negative integer combination of them. That single point refutes
    normality, and every part of it is checkable arithmetic.

    WHAT COMES BACK. Whether the semigroup is POINTED, with the grading that
    proves it; whether the generating set is MINIMAL, naming any generator
    that lies in the semigroup generated by the others; and for each named
    point, whether it is in the cone (with coefficients, or a separating
    functional), in the group (with integer coefficients), and in the
    semigroup (with non-negative integer coefficients, or the bound that makes
    their absence a proof).

    WHY IT TERMINATES. A pointed semigroup has a functional `u` with
    `<u, a_i> >= 1`, so any representation of `v` uses at most `<u, v>`
    generators in total. The bound is computed and travels in the certificate.
    Without such a functional nothing here searches, and it says so.

    `hilbert` PROPOSES a minimal generating set and has it checked. Unlike
    normality this one is DECIDED rather than only refuted: for a pointed
    semigroup the minimal generating set is unique and is exactly the set of
    irreducible non-zero elements, so three bounded questions settle it --
    each `h` is in S, each `h` is irreducible, and every generator is in
    `N.H`. Computing such a set is Normaliz's job; checking one is
    arithmetic.

    IT NEVER CLAIMS S IS NORMAL. A witness refutes normality; establishing it
    means deciding membership for every lattice point of the cone, which is
    what Normaliz is for. Asking gets an honest "not mine".
    """

    generators: dict                 # name -> integer coordinates
    points: dict = None              # name -> coordinates, to be decided
    hilbert: object = None           # a PROPOSED minimal generating set
    order: object = None             # the order the generators are read in
    title: str = ""


@dataclass
class CycleSpec:
    """A parameter that depends on itself, and the loop that has to close.

        CycleSpec(
            parameter="delta",
            edges=[{"from": "delta", "to": "k", "rel": ">=",
                    "fn": "tower", "of": "reciprocal"},
                   {"from": "k", "to": "rho", "rel": "<=",
                    "fn": "poly", "degree": -2}],
            closes=("delta", "<=", "rho"),
        )

    Each edge says how one quantity bounds the next, as a GROWTH CLASS rather
    than a function: `poly` with a degree, `exp`, or `tower`. `of="reciprocal"`
    applies it to `1/source`, which is how a regularity bound in `1/delta` is
    written. `closes` is the constraint that brings the chain back.

    certo composes the classes once and compares the two ends. When the
    comparison is STRICT in the direction that refutes the closing constraint,
    the regime is empty for every positive value of the parameter -- and the
    certificate is the chain, the classes and that one comparison.

    MONOTONICITY IS TRACKED. A lower bound pushed through a decreasing map
    becomes an upper bound; an edge whose available side does not support the
    direction needed is REFUSED rather than composed anyway, because composing
    it could declare a live regime empty.

    IT DOES NOT CHECK YOUR CLASSES. That `k` really grows like a tower is what
    the lemma says, and it is the spec's claim -- the same division as `reduce`
    taking a group and `parametric` taking a dual.
    """

    parameter: str                   # the quantity going to zero
    edges: list                      # dicts: from, to, rel, fn, degree, of
    closes: object = None            # (left, "<=" | ">=", right)
    title: str = ""


@dataclass
class BindSpec:
    """A certificate, the Lean declaration meant to justify it, and the check.

        BindSpec(
            certificate="out/second_moment_rho.json",
            declaration="PaperIV.MomentErrors.N1_from_counting",
            discharges="fine_count",
            provides=(count <= dens**3 * n**4),
        )

    certo reads the certificate's provenance, loads the spec it came from,
    finds the hypothesis named in `discharges`, and asks whether what you say
    the declaration PROVIDES is strong enough for it. A packaged lemma that
    uses density `<= 1` where the certificate assumed the fine count does not
    cover it, and that is reported at BIND time rather than three modules
    later.

    IT IS A BRIDGE. Nobody here reads Mathlib: that `provides` renders the
    declaration faithfully is your claim. What changes is when it bites, and
    that `status` can count it.
    """

    certificate: str                 # path to the certificate being justified
    declaration: str = ""            # the Lean declaration's full name
    discharges: str = ""             # the hypothesis it is meant to supply
    provides: object = None          # a z3 formula: what the lemma gives
    title: str = ""


@dataclass
class MatrixSpec:
    """An integer matrix, and which exact question to ask of it.

        MatrixSpec(
            matrix=[[2, 4, 4], [-6, 6, 12], [10, -4, -16]],
            question="smith",
        )

    Four questions, one shape of evidence: `det`, `rank`, `hermite`, `smith`.
    All four are answered by unimodular transforms carried alongside their
    inverses, so checking is integer matrix multiplication and not a second
    elimination.

    `rows` and `cols` select a submatrix before anything else happens, which
    is how a MINOR is asked for: the same four questions, on the rows and
    columns you name. Indices are 0-based and may repeat nothing.

    Entries must be integers -- `Fraction(4, 2)` is accepted, `2.5` is
    refused rather than rounded, because a matrix quietly rounded is a
    different matrix.

    `inertia` and `psd` take a SYMMETRIC matrix of exact RATIONALS --
    integers, `Fraction`, or strings like "3/7" -- and answer by a congruence
    `S A S^T = D` with `S`'s inverse: the signs of `D` are the inertia, by
    Sylvester's law. `psd` is REFUTED with a vector `x` where `x^T A x < 0`.
    `rows` selects a principal submatrix. For tens of thousands of matrices,
    `certo.inertia.signature(rows)` gives the same three numbers exactly and
    fast, without the certificate.
    """

    matrix: object                   # a list of lists of integers
    question: str = "hermite"        # det|rank|hermite|smith|inertia|psd
    rows: object = None              # a sub-selection, 0-based
    cols: object = None
    title: str = ""


@dataclass
class SymmetrySpec:
    """A program, and a group acting on it, to be reduced to one variable per
    orbit.

        SymmetrySpec(
            lp=my_lp,                                  # an LPSpec
            generators={"swap": {"x1": "x2", "x2": "x1"}},
        )

    The sentence "averaging over the automorphism group, an optimal solution
    may be assumed constant on each orbit" is a bridge in every write-up that
    uses it. Its three hypotheses are finite checks given a generating set:
    the action permutes the variables, the constraint set is invariant, and
    the objective is invariant. With those, the quotient is arithmetic.

    WHERE THE GROUP COMES FROM is not certo's problem. nauty computes it; this
    CHECKS it. A generator that is not an automorphism is refused by name,
    because a wrong group does not give a weaker reduction -- it gives a wrong
    one.

    Each generator is a dict mapping variable to variable; it must be a
    bijection of the whole variable set. The identity may be omitted.
    """

    lp: object                       # an LPSpec, or anything with `to_lp`
    generators: dict                 # name -> {var: var}
    title: str = ""


@dataclass
class MomentSpec:
    """The first moment, exactly, and the existence it buys.

        MomentSpec(                        # by event: linearity, no independence
            events=[("mono_K4_on_{}".format(i), Fraction(1, 64))
                    for i in range(35)],
            counts=True,
        )

        MomentSpec(                        # by tail: P(X>=1), P(X>=2), ...
            tails=[Fraction(1, 2), Fraction(1, 8), Fraction(1, 64)],
            counts=True,
        )

    `events` gives the expected count as a sum of probabilities, which is
    linearity of expectation and needs NO independence -- the reason the method
    is usable at all. `tails` gives a distribution by `P(X >= k)`; the masses
    are the successive differences and `E[X]` is the sum of the tails. Exactly
    one of the two.

    `counts=True` says the quantity is a COUNT: non-negative and integer
    valued. Only then does `E[X] < 1` give the existence conclusion -- some
    outcome has none of the bad events -- because a quantity that could be one
    half everywhere has a mean below one with no outcome at zero. Without it,
    or with a threshold other than one, what comes back is a bound on a mean,
    which is a smaller and still useful statement.
    """

    events: list = None              # [(name, probability)]
    tails: list = None               # [P(X>=1), P(X>=2), ...]
    threshold: object = 1
    relation: str = "<"              # "<" or "<="
    counts: bool = True              # the quantity is a non-negative integer count
    title: str = ""


@dataclass
class RatioSpec:
    """A rational-function inequality, claimed for every parameter at once.

        from certo.polynomials import Poly

        RING = ("n",)
        n = Poly.var(RING, "n")
        K = lambda c: Poly.const(RING, c)

        RatioSpec(
            parameters={"n": 2},           # name -> lower bound
            left=(n - K(2), n * n),        # (numerator, denominator)
            right=(K(1), n),
        )                                  # (n-2)/n^2 <= 1/n for all n >= 2

    A side may be a `Poly` or a number, in which case the denominator is one.
    `relation` is `"<="` or `"<"`; anything else is refused, because `>=` is
    the same claim with the sides swapped and two spellings of one statement
    is how a sign error hides.

    Both denominators are CHECKED POSITIVE on the ray. Clearing them preserves
    the direction only when they are, and a denominator not shown positive is
    a refusal rather than an assumption -- if one were negative the inequality
    would flip and the certificate would be exactly backwards.

    `region` takes declared side conditions `g(p) >= 0`, with the same
    standing they have in `ParametricSpec`: scope, not content.
    """

    parameters: dict                 # name -> lower bound (a number)
    left: object                     # Poly, number, or (numerator, denominator)
    right: object
    relation: str = "<="             # "<=" or "<"
    region: list = None              # [(name, g)] meaning `g(p) >= 0`, SCOPE
    title: str = ""


@dataclass
class FamilySpec:
    """A finite family of linear programs, and the largest of them.

        FamilySpec(
            items=all_bipartitions,          # iterable, or callable() -> iterable
            lp=lambda z: lp_for(z),          # callable(item) -> LPSpec, sense max
            key=lambda z: "z={}".format(z),  # callable(item) -> str
        )

    Certifies `max over the family = V`, which is two claims and they are not
    symmetric: the winner ATTAINS `V` (an exact primal and dual that meet), and
    every other item is BOUNDED by it (a feasible dual with `b.y <= V`). A dual
    does not have to be optimal to bound, so the expensive half of the search
    never has to be exact -- only the checking does.

    Nothing stores an LP. Each item's program is rebuilt from `lp(item)` at
    verification, so a dual belonging to a different item does not fit, and
    `verify` NEEDS the spec file -- saying so when it does not have it rather
    than checking less while looking the same.

    Every item program must be a maximisation; a `min` is refused rather than
    reinterpreted, because bounding a minimum from above needs a primal point
    and not a dual, which is a different certificate.
    """

    items: object                    # iterable, or callable() -> iterable
    lp: object                       # callable(item) -> LPSpec
    key: object = None               # callable(item) -> str (default: str)
    title: str = ""


@dataclass
class PeakSpec:
    """A concave quadratic in one INTEGER variable, and where it peaks.

        from certo.polynomials import Poly

        RING = ("m", "x")
        m, x = Poly.var(RING, "m"), Poly.var(RING, "x")
        K = lambda c: Poly.const(RING, c)

        PeakSpec(
            parameters={"m": 0},           # the parameters, and their floors
            variable="x",                  # the one that must be an integer
            objective=x * (m * K(6) + K(1) - x * K(3)) * K(Fraction(1, 2)),
            argmax=Poly.var(("m",), "m"),  # over the PARAMETERS alone
        )

    Certifies that no integer beats `argmax`, for every parameter value at or
    above the floor at once -- and, because `argmax` is an integer, that the
    value there IS the integer maximum rather than an upper bound on it.

    `objective` is a `Poly` over the parameters AND the variable, of degree at
    most two in the variable; `argmax` is a `Poly` over the parameters only,
    with INTEGER coefficients, since a maximiser that is not an integer at
    integer parameters is not a maximiser of anything here.

    Which integer is nearest the real vertex depends on the parameter modulo
    something, so a family splits into residue classes and each class is its
    own spec with its own `argmax`. They are different claims; one certificate
    covering all of them would be hiding the split rather than proving it.

    `region` takes declared side conditions `g(p) >= 0`, exactly as
    `ParametricSpec` does and with exactly the same standing: scope, not
    content, repeated by `verify` and proved by nothing.
    """

    parameters: dict                 # name -> lower bound (a number)
    variable: str                    # the integer variable
    objective: object                # Poly over parameters + variable
    argmax: object                   # Poly over the parameters alone
    region: list = None              # [(name, g)] meaning `g(p) >= 0`, SCOPE
    title: str = ""


@dataclass
class EliminateSpec:
    """Two polynomials and the variable to get rid of.

        EliminateSpec(
            variables=["s", "t"],
            equations=[t ** 3 + s * t + 1, t ** 2 - s],
            eliminate="t",
        )

    The answer is the RESULTANT: a polynomial in the remaining variables that
    vanishes exactly when the two share a root in `t`. So "these two equations
    have a common solution" becomes a condition on `s` alone, which is the
    step people do by hand while setting a problem up.

    EXACTLY TWO equations, because that is what a resultant is. Iterating it
    pairwise over more introduces extraneous factors that nothing here could
    certify away; for a larger system `ideal` is the right command, and it
    says what follows rather than what eliminates.

    Both must have degree at least 1 in `eliminate` -- there is nothing to
    eliminate otherwise, and the Sylvester matrix is not defined.
    """

    variables: list
    equations: list                  # exactly two: z3 terms or Poly
    eliminate: str                   # the variable to remove
    title: str = ""


@dataclass
class SOSSpec:
    """A polynomial claimed non-negative everywhere, certified as a sum of
    squares.

        SOSSpec(variables=["x", "y"], poly=x**4 + y**4 - x**2 * y**2)

    The search is numeric and the certificate is exact: rational coefficients
    and rational linear forms, checked by expanding. Nothing approximate
    survives into the certificate.

    Incomplete, and in a way worth knowing: every sum of squares is
    non-negative, but from degree 4 in 3 variables there are non-negative
    polynomials that are not sums of squares (Motzkin's is the standard one).
    So no certificate found is `unknown_solver`, never "it goes negative".
    """

    variables: list
    poly: object                     # a z3 term or Poly
    half_degree: object = None       # default: deg(p)/2
    iterations: int = 600
    title: str = ""


@dataclass
class NumberSpec:
    """An integer question with a certificate anyone can redo by hand.

        NumberSpec(n=2 ** 31 - 1, question="prime")
        NumberSpec(n=600851475143, question="factor")

    `prime` emits a Pratt certificate: a witness generating (Z/n)^*, plus a
    certificate for each prime factor of n-1, recursively. Checking it is
    modular exponentiation. `factor` emits the factors, each with its own
    primality certificate, so "and these are prime" is not left hanging.
    """

    n: int
    question: str = "prime"          # "prime" | "factor"
    title: str = ""


# ---------------------------------------------------------------------------
# orders of magnitude
# ---------------------------------------------------------------------------


@dataclass
class OrderSpec:
    """A term, an assignment of magnitudes, and what you claim about it.

        OrderSpec(
            expression=5 * k * W * C * C / (u ** 3 * d ** 2 * p ** 10),
            orders={"k": 0, "W": 2, "C": 1, "u": 0, "d": 2, "p": 0},
            expect="decays",
        )

    `orders` gives each symbol its exponent: 2 for "about n^2", 0 for "about a
    constant", `Fraction(1, 2)` for a square root. A symbol with no entry is an
    ERROR, not an assumption -- the whole value here is that the substitution
    is written down instead of done in someone's head.

    `expect` is "decays", "constant" or "grows", and leaving it out measures
    rather than decides. The case worth naming is `constant`: a term that is
    Theta(1) is not infeasible, so a solver asked "is this satisfiable" says
    yes forever and correctly, while the bound it sits in never improves with
    `n`. That question is invisible to `prove` and to a proof assistant alike.
    """

    expression: object               # a z3 arithmetic term
    orders: dict                     # symbol -> exponent of `var`
    relations: object = None         # ["E ~ n**2", "Lmass >= E * tC", ...]
    var: str = "n"
    expect: object = None            # "decays" | "constant" | "grows" | None
    title: str = ""
