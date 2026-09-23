# The forty-eight commands

Grouped by the question they answer, in the same order and the same words as
`certo commands` prints in your terminal. If the two ever disagree, the
terminal is right — it is generated from the routing table.

Every entry has the same five fields, always in this order:

| Field | Means |
|---|---|
| **Question** | what you are actually asking. Read this, not the name |
| **Spec** | the type your `spec()` function must return — see [SPECS.md](SPECS.md) |
| **Answers** | what comes back on the conclusive path |
| **Certificate** | the kind written to disk, and whether re-checking it needs a solver |
| **Not established** | what a reader must *not* conclude from it. The tool repeats these in `verify`; they are not disclaimers, they are the boundary of the claim |

Jump: [Is it true?](#is-it-true) · [Is my setup sane?](#is-my-setup-sane) ·
[How big, how small, how many?](#how-big-how-small-how-many) ·
[Every case?](#does-it-hold-for-every-case) ·
[Algebra and numbers](#algebra-numbers-and-structures) ·
[Build and assemble](#build-it-assemble-it-keep-it) ·
[Entry points](#entry-points-and-bookkeeping)

---

## Is it true?

### `certo prove`

**Question** — Is this claim true under these hypotheses?
**Spec** — `Spec`
**Answers** — a proof, or a **counterexample with concrete values**
**Certificate** — `unsat_core`, solver-free whenever the core is linear
arithmetic; or `model`, always solver-free
**Not established** — that the hypotheses are satisfiable. A proof from
contradictory hypotheses is valid and says nothing, so vacuity is checked on
every success and reported by name.

A refutation is the useful half more often than people expect, because it
comes with values. A user's density constraint was claimed to force `G`
almost complete; `prove` refuted it in 15 ms with `dens = 27/32` feasible —
nowhere near "almost complete", and that number says which way to fix the
statement.

```
$ certo prove examples/refute_density.py
REFUTED  [sat]
  the counterexample:
    dens = 7/8
    kappa = 4
  certificate: model (no solver needed, id 1a76b821f2cafa42)
```

### `certo core`

**Question** — Which of my hypotheses does it actually need?
**Spec** — `Spec`, or `MultiSpec` for several goals at once
**Answers** — the minimal unsatisfiable subset, and which hypotheses were
redundant
**Certificate** — `mus` / `unsat_core`, solver-free when the core is linear
**Not established** — that the hypothesis set is minimal *jointly*. A pair can
be redundant together with neither redundant alone.

```
$ certo core examples/amgm.py
PROVED -- symbolic and universal under the hypotheses  [unsat]
  hypotheses needed: a_pos, b_pos, c_pos | redundant: noise
```

On a `MultiSpec` the answer is a table, and the table is the point: a
hypothesis irrelevant to one goal and necessary for another is invisible when
the goals are looked at one at a time.

```
$ certo core examples/core_matrix.py
  hypothesis  identity  positivi  ordering
  r_ge_3            no       yes        no
  d_ge_1            no        no        no
  d_le_r            no        no       yes
  never used by any goal: d_ge_1
```

`verify` also checks that **the table says exactly what the cores say**.

### `certo farkas`

**Question** — Is this inequality true, with the multipliers shown?
**Spec** — `Spec`
**Answers** — the non-negative rational multipliers that combine the
hypotheses with the negated goal until everything cancels, plus the
`linarith` / `nlinarith` call to paste
**Certificate** — `farkas`, **solver-free**: checking it is adding fractions
**Not established** — anything, when it finds nothing. `farkas` is incomplete
on purpose in both modes, so "no certificate" means *this search did not close
it*, never *false*.

```
$ certo farkas examples/farkas_linear.py
PROVED  [unsat]
  multipliers:
    x_ge_1                 1
    y_ge_1                 1
    __goal__               1
  Lean: linarith [x_ge_1, y_ge_1]
```

A hypothesis with multiplier 0 is absent from the list, so the certificate
says which hypotheses the proof actually uses — `core` for free, and exactly
what keeps a Lean interface small.

`--nonlinear` is `nlinarith`, faithfully: multiply pairs of hypotheses, throw
in some squares, treat each monomial as a fresh variable, run the linear
search on that. The rows it derived are flagged in the certificate, because a
reader should know which rows were not hypotheses.

> **`prove` to know. `farkas` to certify.** Z3's `nlsat` is complete for real
> arithmetic; this is not, and it hands you the reason instead.

### `certo induct`

**Question** — Does this hold for every `n ≥ n₀`?
**Spec** — `InductSpec`
**Answers** — the base cases, the step, **and the check that the chain joins**
**Certificate** — `induction`; re-solves, so not solver-free
**Not established** — nothing by a solver: there is no induction schema in an
SMT solver. The principle is applied *here*, and `verify` says so every time.

The join is the reason this is a command. A base covering 3..8 with a step
valid only from `k ≥ 10` proves **nothing** about `n = 9`, and the sentence
"and from there by induction" reads exactly the same either way.

```
$ certo induct examples/induct_sum.py
PROVED  [unsat]
  6 base cases k=3..8, step from k=3, chained by induction
```

Set `step_from=10` and it refuses at build time — no certificate is written.
Forge one afterwards and verification catches it again:

```
[XX] the step starts no later than the base ends  (step from k=10, base reaches 8)
```

The step is proved with the index **free**, which is what makes it universally
valid: a proof with a free variable is a proof for every value of it.

---

## Is my setup sane?

### `certo check`

**Question** — Is my regime non-empty — do these hypotheses have a model at
all?
**Spec** — `Spec`
**Answers** — with `--hypotheses-only`, a **model** if the regime is
inhabited, the **minimal clash** if it is not
**Certificate** — `model`, **solver-free**: non-emptiness re-checks by
evaluation alone
**Not established** — anything about the hypotheses, if you ask without
`--hypotheses-only` and your claim is the literal `False`.

That last line is the trap, and it is signposted. `check` decides
`hypotheses AND claim`, so a claim of `False` reports UNSATISFIABLE whatever
the hypotheses are. A user asked exactly that on a system that has models and
was told "no model exists".

```
$ certo check regime.py
UNSATISFIABLE  [unsat]
  no model exists -- but the claim is the literal False, so this says nothing
  about the hypotheses. Ask with `--hypotheses-only`.
```

```
$ certo check regime.py --hypotheses-only
SATISFIABLE  [sat]
  the regime is NON-EMPTY: all 3 hypotheses hold together, and here is a
  point where they do
```

### `certo lint`

**Question** — Is this spec well-posed, before I spend the compute?
**Spec** — any of them
**Answers** — contradictory hypotheses, an empty family, a 10⁹ domain, a
predicate that returns `bool`, an inductive step that starts after the base
ends
**Certificate** — none, and none claimed
**Not established** — that the spec is *right*. It checks the shape of the
question, not the mathematics.

The cheapest thing in the tool. Run it on every spec before running the spec.

```
$ certo lint examples/lint_vacuous_regime.py
Spec -- for `certo prove / check / core`
  [XX] the hypotheses contradict each other, so any proof will be VACUOUS --
       valid and about nothing. The clash is: kappa_large, density_high, sparse
  1 errors, 0 warnings, 0 notes
```

Four findings that pay for themselves:

| Finding | Why it matters |
|---|---|
| the claim is a univariate polynomial of degree ≥ 11 | `prove` closes degree 10 in 12 ms and does not close degree 11 in 20 s, measured on a statement that is trivially true. A user spent 71 minutes on a degree-63 schedule polynomial and got `INCONCLUSIVE [timeout]`; substituting `t = s³` by hand let certo close it in 4.3 ms |
| the inductive step starts after the base cases end | `induct` refuses this too — after discharging every base case, which is where the hours go. Here it is a comparison of two integers |
| the predicate returns `bool` | then the sweep will be `reproducible`, not `certified`. People who wrote the predicate themselves have read that difference wrong |
| `integer=True` makes **all** variables integer | a user read it as "there are integers in here" and got a design worth nothing, every weight rounded to zero |

It counts a domain without building it — `items=lambda: iter(range(10**7))` is
peeked at, never materialised — and reads the size of a graph family from a
table, so linting an 11-vertex sweep costs the time to read the file.

Loading a spec **executes** it; that is how specs work here. Beyond that, lint
calls the predicate at most once and never runs the solver on the goal.

Exit codes: `0` clean or notes only, `1` errors, `2` warnings.

### `certo audit`

**Question** — Does every hypothesis earn its place, or is my theorem
overstated?
**Spec** — any spec with named hypotheses
**Answers** — one of four verdicts per hypothesis — `needed`, `redundant`,
`domain`, `unknown` — and for `needed`, **the assignment that breaks the claim
without it**
**Certificate** — `hypothesis_audit`; re-checking substitutes each witness and
re-decides the result, so it needs a solver — but not the search that found it
**Not established** — that the hypothesis set is minimal. Hypotheses are
dropped one at a time.

`core` catches a theorem stated with slack. This catches the opposite and more
expensive mistake: a theorem stated **too strongly**, formalised, and only then
found to be about a smaller class than the paper claims.

```
$ certo audit examples/hypothesis_audit.py
SATISFIABLE  [sat]
  2 hypotheses are REDUNDANT (n_large, connected): the claim still follows
  without them, so the theorem is weaker than it looks. 1 are needed
  [REDUNDANT]  n_large
  [needed]     m_bounded   without it: connected=True, m=6, n=5
```

`connected` was planted as an obvious red herring. `n_large` was not — `n ≥ 5`
reads like it must matter, and it does not, because `m ≤ n − 2` already gives
`m ≤ n`. The hypothesis doing no work is rarely the one anybody suspected.

**The witness is the content, not the verdict.** Knowing `m_bounded` is needed
is worth little; knowing that `n = 5, m = 6` breaks it is what tells you
whether you wrote the hypothesis you meant.

**`domain` exists because division is total in SMT.** `n/0` is not an error in
Z3; it is some fixed value the solver invents. Dropping a hypothesis that
guards a denominator used to yield an instant "counterexample" at `d = 0`, and
the hypothesis then read `needed` for a reason about the solver rather than
about the theorem. Every divisor that could vanish is collected up front and
every search is guarded by it:

```
$ certo audit guarded.py
  1 hypotheses are DOMAIN obligations (d_nonzero): dropping one does not
  make the claim false, it makes it meaningless
  [DOMAIN]     d_nonzero   holds up: d != 0
```

Not `needed`, because the claim does not become false without it; and
emphatically not `redundant`, because removing it gives a statement about a
value nobody defined. A `domain` hypothesis must **not** be dropped —
discharge it as a side condition in the proof assistant. The distinction is
asked rather than read off the formula's shape: put `d >= 1` beside `d != 0`
and the same `d != 0` becomes genuinely `redundant`.

### `certo status`

**Question** — Where does my whole project stand?
**Spec** — none; it reads a directory of certificates
**Answers** — four sections: RESULTS, STILL OWED, HOLLOW, STALE
**Certificate** — **none, deliberately.** A report that certified itself would
be the one artefact here that nobody had checked
**Not established** — that the certificates verify. `status` reads the claims
other commands made; `certo status --verify` re-checks every one.

```
$ certo status out/
19 certificates under out
  sweep 6   unsat_core 4   proof 3   farkas 2   gap 1   induction 1   sos 1

  RESULTS -- 9 certificates nothing else here builds on
  STILL OWED -- 3 assumptions these results rest on
  HOLLOW -- 1 claims that are valid and say less than they look like
  STALE -- 2 certificates whose spec has moved
```

**RESULTS** are the certificates nothing else in the directory builds on. A
lemma's certificate is not a result; the proof standing on it is.

**STILL OWED** is every bridge and every unclaimed optimality, including ones
reached three levels down. Bridges are legitimate and often unavoidable;
losing count of them is not, and they are easy to lose precisely because
everything around them verifies.

**HOLLOW** is what is valid and says less than it looks like: a vacuous proof
with its clash named, a sweep whose predicate nothing certified, an optimum
that is a value reached rather than a maximum proved. It also scans `.lean`
files for statements of the shape `theorem foo : True := by`, skipping
`.lake` and `lake-packages`.

**STALE** is a certificate whose spec changed since it was issued. It is not
wrong — it verifies on its own — but it no longer describes the file next to
it, and six months later nobody remembers which.

`certo status <dir> --manifest` answers a different question: *did I certify
every one, exactly once?* A count is not that guarantee -- two runs over 71
cells with one duplicate also count 72.

The manifest gives the set in a canonical order -- **by digest, not by
filename**, so two people who produced it in a different order get the same
number -- with one aggregate fingerprint on the same Horner recipe as
`matrix`, and both kinds of duplicate reported rather than collapsed: the same
artefact at two paths, and two different certificates about the same subject.

Omission needs a declared set to be detectable at all, which is the honest
limit. `--expect FILE` takes the headlines that were meant to be produced and
names what is missing; without it the manifest says only what is present, and
says nothing it cannot know.

It also reports the relations it can **derive**, and derives rather than reads
them: a cone declares a lattice, a Smith certificate is about a matrix, and
the edge is a fingerprint match. Neither certificate mentions the other, so
there is nothing to forge. An edge says *these two are about the same matrix*
-- not that one depends on the other. A cone's regularity is established by
its own `multiplicity == 1`; a Smith certificate over the same lattice
corroborates it and does not carry it.


### `certo doctor`

**Question** — Can this install do what I need?
**Spec** — none
**Answers** — every capability, present or absent, and **what each gap costs**
**Certificate** — none
**Not established** — nothing; it makes no mathematical claim.

```
$ certo doctor
  capability   present   what for
  z3           [ok]      prove, check, core, synth, compose
  nauty        [--]      fast graph enumeration for enum and sweep

  optional pieces missing, each with a fallback:
    nauty        the built-in Python engine, comfortable to n=8
```

Every row says three things, and the third is the one that matters. A missing
optional tool is almost never fatal here, and a checklist of red crosses that
does not say so reads as a broken install.

It also reports interpreter **startup hooks** (a `.pth` file that runs on
every interpreter start costs real time on every invocation), a **partial
install** left behind when a file could not be replaced, and a mismatch
between `certo --version` and the version `pip` has recorded.

`certo doctor --register-mcp` registers the MCP server in `.mcp.json`, merging
rather than replacing, and checks that it starts.

---

## How big, how small, how many?

`certo doctor --repair` lists what an interrupted install left behind, and
`--repair --apply` removes it. **Preview is the default** and applying is a
second decision, because the target is inside site-packages: a wrong guess
there breaks an environment rather than a file.

pip leaves two markers, and both are recognised. `~`-something is a rename it
did not finish -- on Windows a held-open `certo-mcp.exe` stops it between the
rename and the cleanup, and the package is then present twice under two names,
one of them unimportable. `something.deleteme` is a launcher it could not
replace, beside an orphaned `.exe`. Nothing without a `~` or a `.deleteme` is
touched, and the orphan `.exe` is left alone: it is not pip's marker.

It does **not** reinstall. Running pip from inside the tool would hide which of
the two failed, and the reason the install broke is usually still running --
`--repair` names what is holding certo's scripts before listing anything.

### `certo opt`

**Question** — What is the optimum, exactly?
**Spec** — `LPSpec`, or `PackingSpec`
**Answers** — the optimum in exact rationals, and the **dual**, which for a
packing reads as the load on each resource
**Certificate** — `lp_dual`, **solver-free**: rational arithmetic
**Not established** — integer optimality. For an ILP the dual certifies the
**relaxation bound**. With `integer={"K3"}` — whole in one kind, fractional in
another — `opt` reports only the relaxation bound and says so.

CBC works in floating point and returns `10.66666656003499` where the answer
is `32/3`. certo solves in floating point, **reconstructs rationals and
verifies in `Fraction`**, accepting only if the exact check passes, so a bad
reconstruction rejects itself.

```
$ certo verify out/lp.json
VALID  lp_dual certificate (verified without a solver)
  [ok] exact strong duality (c.x == b.y)  (c.x=25/2 | b.y=25/2)
  EXACT rational arithmetic, no tolerances
```

`--no-exact` skips the reconstruction; the certificate stays in floating point
and `verify` flags it as **not citable**.

`--target` answers the question an existence proof actually has — *is this
bound reached* — and the target travels in the certificate, so `verify`
repeats the comparison. Falling short is a **warning on a valid certificate**,
not invalidity: the certificate is correct and the bound is insufficient, and
those are different statements.

`loads=[...]` declares named regions the design must respect, and the dual
prices them: see [Local loads](CASES.md#local-loads).

`--gap` on a `PackingSpec` reports `mu*` (the relaxation), `nu` (the integer
value achieved), and the distance between them, as **one** artefact rather
than two runs to subtract -- two files in a folder cannot claim to be about
the same packing.

Both halves are constructed by `--gap` itself, whatever the spec's `integer`
flag says, because that is what a gap IS. A spec that declares itself integer
gets its fractional half built anyway, and `relaxed_for_gap` in the result
says so rather than doing it quietly. (Until 0.11.6 the fractional half was
inherited from the spec, so `integer=True` compared the integer optimum
against itself and reported **gap 0** -- the strongest conclusion available in
this domain, from a flag combination.)

With `--target`, the number is compared against `nu` and the result carries
`reached` and `deficit`. A target that is not reached **refutes** only when the
integer optimum is global; below that, `nu` is a point somebody found, and "we
did not get there" is not "it cannot be got to". The verdict distinguishes the
two.

`meta.objective` carries the optimum under the same name `opt` uses for the
same number, so one script reads both paths.


### `certo mixed`

**Question** — …and is it really optimal over the integers?
**Spec** — `LPSpec` with variables carrying `kind="binary"` or `kind="integer"`
**Answers** — a discrete skeleton from a search, a residual LP over the
continuous part certified exactly, and three numbers kept apart
**Certificate** — `mixed_design`, **solver-free**: exact arithmetic
**Not established** — that the discrete choice was optimal, unless `achieved`
meets `bound`. When it does not, the banner says **GLOBAL OPTIMALITY IS NOT
CLAIMED**.

| | What it is |
|---|---|
| **achieved** | what this construction attains. Exact, and a genuine **lower** bound on the true optimum, because the thing exists |
| **conditional** | the best the continuous part can do **with this skeleton**, from the residual LP's exact dual |
| **bound** | the relaxation over **all** skeletons: an **upper** bound |

When `achieved` meets `bound`, global MILP optimality is certified for free.

Three levels travel with the certificate, named: `feasible`,
`conditional_optimum`, `global_optimum`.

`--freeze my_solution.json` takes a skeleton from HiGHS, Gurobi, something
bespoke or a person. It is rounded and checked exactly like any other, so
where it came from changes nothing about what is certified — and that it came
from elsewhere is recorded. Requiring certo's own CBC to reproduce a
construction that already exists would put certo's limits in front of it.

Full treatment in [Worked cases](CASES.md#mixed-designs).

### `certo bisect`

**Question** — Where is the threshold for this constant?
**Spec** — `BisectSpec`
**Answers** — the pair that brackets the threshold, each side certified
**Certificate** — `bisect`; solver-freedom depends on its children
**Not established** — monotonicity in the parameter. It is **assumed**; the
endpoints are checked and a warning is issued if they misbehave, but
monotonicity itself is not proved.

`build(t)` may return a **`CNFSpec`**, not only a `Spec`, and that is how
`bisect` answers *"what is the smallest set that fixes this?"* — the fewest
vertices to delete, clauses to drop, edges to remove. For a `CNFSpec` "holds"
means **UNSAT**: no object of that size exists. See
[**The smallest set that fixes this**](CASES.md#the-smallest-set-that-fixes-this).

Use it rather than a loop over `cases`. A `for k in ...` that stops at the
first SAT reads `unknown_solver` as `unsat` and reports a threshold that is not
one; two people wrote exactly that within a day of each other and both got a
wrong number. `bisect` carries three states and stops on the inconclusive
probe instead of picking a side.

### `certo bounds`

**Question** — Is this numeric inequality true? (`e`, `log`, `π`, `ζ`)
**Spec** — `BoundSpec`
**Answers** — a rigorous enclosure in exact rationals, and whether it settles
the claim
**Certificate** — `ball`, **solver-free for the claim**; the interval itself
needs the spec and the same backend
**Not established** — non-zero-ness of a quantity that is in fact zero. No
enclosure will ever prove that, and running out of precision is reported as
`resource_exhausted`, not as a refutation.

`prove` and `farkas` are exact but algebraic. The moment a proof says "this
constant is below 0.4" and the constant involves `e` or `ζ`, neither can see
it, and "I computed it and it came out 0.397" is not a claim about anything.
An enclosure is.

```
$ certo bounds examples/bounds_constant.py
PROVED  [unsat]
  the value is < 0.866 -- established rigorously at 64 bits
  enclosure: [0.8652559794322651, 0.8652559794322651]  width 3.062e-19
```

**Precision is the work budget**, exactly as `rlimit` is for Z3: the search
starts at `prec` bits and doubles until the enclosure settles the claim. Ball
arithmetic loses accuracy at cancellations, so how much precision an
expression needs is a property of the expression, not of the answer.

**Floats are refused.** `0.1` is not one tenth, it is `3602879701896397/2^55`,
and an enclosure built from it would be perfectly rigorous about the wrong
number. So `value=lambda m: m.pi * 0.5` raises and `m.pi * m("1/2")` is fine.
It is the one way the guarantee could quietly be lost, so it is the one thing
that stops the run.

| Backend | Covers |
|---|---|
| `python-flint` (Arb) | everything below, plus `gamma`, `lgamma`, `digamma`, `zeta`, `erf`, `erfc`, the inverse and hyperbolic functions |
| `mpmath.iv` | `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `gamma` |

The backend is recorded, because a bound is only as good as what produced it.
Asking `mpmath.iv` for `zeta` says so rather than falling back to a
non-rigorous evaluation.

Leave `claim` out to **measure** instead of decide.

### `certo order`

**Question** — Does this term DECAY in `n`, or is it Θ(1)?
**Spec** — `OrderSpec`
**Answers** — the leading exponent, and the terms collected by exponent
**Certificate** — `asymptotic`, **solver-free**: exact arithmetic
**Not established** — the constant. `≍` hides a factor, so a Θ(1) term with a
coefficient of 1e-9 may be perfectly fine in practice.

Some bugs are not infeasibilities. A user had `5|k| W C² / (u³ d² p¹⁰)` with
`d ≍ n²`, `C ≍ n`, `|W| ≍ n²`, and asked whether it decays. It does not — it
is **Θ(1)** — and that bug was invisible to Lean *and* to `certo prove`, for
the same reason: it is a feasibility that does not improve with `n`, so a
solver asked "is this satisfiable" says yes forever, correctly, while the
bound it sits in never gets better.

```
$ certo order examples/order_decay.py --expect decays
REFUTED  [sat]
  REFUTED: you claimed it decays, and it is Theta(1) -- the leading exponent
  in n is 0
```

What makes it a certificate rather than a calculation is that **the
substitution is written down** instead of done in someone's head, and that the
collection is exact: two terms sharing the top exponent whose coefficients
cancel really do cancel.

You cannot divide by a sum — `1/(x + y)` has an order that depends on which
dominates — and a symbol with no entry in `orders` is an **error**, not an
assumption.

**`relations=` derives the exponents instead of asking for them.** Six
numbers worked out mentally from `|E| <= Lmass`, `C >= n`, `d' >= C(n,2)` is
six chances to be wrong, and one wrong entry gives a clean false answer:

```python
OrderSpec(expression=..., orders={},
          relations=["E ~ n**2", "tC ~ 1", "Lmass ~ E * tC",
                     "C ~ n", "dp ~ C**2"])
```

Every relation is **linear in the exponents** — `E ~ n**2` is `exp(E) = 2`,
`Lmass ~ E * tC` is `exp(Lmass) = exp(E) + exp(tC)` — so the system is a linear
program, solved exactly. The growth variable is pinned at one: it is the scale,
not an unknown.

It **refuses rather than guesses**. The Laurent core needs a number per symbol
and an interval is not one, so relations that leave a symbol one-sided are
refused with the interval named — `Lmass in [1, +inf)` says which bound is
missing, and *cannot infer* does not.

Aliases: `certo asymptotics`, `certo decays`.

### `certo reduce`

**Question** — This is symmetric. Can I solve one variable per orbit instead?
**Spec** — `SymmetrySpec`
**Answers** — the three hypotheses of the averaging argument, checked, plus
the quotient program
**Certificate** — `symmetry_reduction`, **solver-free**
**Not established** — where the group came from. nauty computes it, a paper
states it, you write it down.

Five examples in this repository begin with a symmetrised program, and the step
that gets them there is always some version of *"averaging over the
automorphism group, an optimal solution may be assumed constant on each
orbit"*. Everything downstream is certified; that sentence was not, and it is
load-bearing — **if the group is wrong, the reduced program is a different
program** and every number after it is about something else.

The argument has exactly three hypotheses, and given a generating set all three
are finite checks:

| Hypothesis | The check | Why it is needed |
|---|---|---|
| the action permutes the variables | each generator is a bijection | otherwise there is no group |
| the constraint set is invariant | σ(row) is a row, same sense, same right-hand side, same bounds | so every image of a feasible point is feasible |
| the objective is invariant | `c[σ(v)] = c[v]` | so the average has the same value |

A generator that fails any of them is **refused by name**. A wrong group does
not give a weaker reduction, it gives a wrong one. A *smaller* group is always
sound and only less useful.

`--parametric` asks the same question about a **family**: orbits whose
multiplicities are polynomials, rows that exist only under stated conditions,
and regimes derived rather than listed. See
[Parametric symmetry](CASES.md#parametric-symmetry).

### `certo quotient`

**Question** — I have a partition of this program. Does the quotient have the
same attainable values?
**Spec** — `EquitableQuotientSpec`
**Answers** — the class data, both regularities, and the two maps
**Certificate** — `equitable_quotient`, **solver-free**: exact counting
**Not established** — that the partition is the one your argument uses. That
is the spec's claim.

Where `reduce` checks an averaging argument, this checks a *constructive
equivalence*: `Proj` maps a point of the physical program to the quotient and
`Lift` maps back, and the certificate carries both regularities —
`N_i · H_ij = M_j · B_ij` — rather than one, because they are different
numbers and confusing them gives a confidently wrong answer.

### `certo matrix`

**Question** — What is the rank, the determinant, or the Smith form of this
integer matrix — exactly?
**Spec** — `MatrixSpec`
**Answers** — rank, determinant, Hermite or Smith normal form, with the
unimodular transforms **and their inverses**
**Certificate** — `integer_matrix`, **solver-free**: integer matrix
multiplication
**Not established** — that the matrix you wrote down is the matrix your paper
is about. The right incidence matrix, the right basis, the right orientation:
that is the spec's claim, and it is exactly where a computation stops being
about the mathematics.

```
U · A = H          U unimodular, H in Hermite normal form
U · A · V = S      U, V unimodular, S the Smith normal form
```

Every claim becomes a multiplication:

| From | Follows |
|---|---|
| `U · U_inv = I` | det(U) is +1 or −1, and nothing else |
| `U · A = H` | A and H span the same row lattice |
| H echelon with r pivots | rank(A) = r, since U is invertible over ℤ |
| the diagonal of H | \|det A\|, and with the sign of det(U), det A |
| S diagonal, sᵢ \| sᵢ₊₁ | the invariant factors, so the torsion of ℤⁿ / A ℤᵐ |

**The sign is the interesting part.** `U · U_inv = I` pins the magnitude of
det(U) and says nothing about which sign — and that sign *is* the sign of
det(A). Recomputing it over ℤ would cost what the elimination costs. It does
not have to: det(U) was already known to be ±1, and those two are distinct
modulo any odd prime, so one determinant of U mod a word-sized prime settles
it. Not probably — **exactly**, because there were only ever two candidates.

`rows` and `cols` select a submatrix first, so a **minor** is the same question
with no separate machinery. Entries must be integers: `2.5` is refused rather
than rounded. Rank is decided by counting pivots, not by comparing a singular
value against an epsilon — over ℤ there is no epsilon to choose and none to
defend.

`certo lint` warns before Smith runs: 10,000 entries is a note, 40,000 a
warning. A 64×64 Smith takes about 2 seconds, an 80×80 about 6.

### `certo cone`

**Question** — Is this cone regular, at height one, and is subdividing it
crepant?
**Spec** — `ConeSpec`
**Answers** — primitivity per generator, the multiplicity, the height
functional `u` with `⟨u,v⟩ = 1`, and the discrepancy `⟨u,w⟩ − 1` of any ray you
name
**Certificate** — `toric_cone`, **solver-free**: exact determinant and solve
**Not established** — the geometry. That multiplicity one gives a smooth
chart, that discrepancy zero gives a crepant modification, that a fibre is SNC
or reduced: those are theorems about varieties, and a certificate that quietly
asserted them would be the substitution this project exists to refuse.

**The lattice is declared, never guessed, and it changes the answer.** A real
cell with generators `(4,0,0,0)`, `(2,2,0,0)`, `(2,0,2,0)`, `(1,1,1,1)` has
multiplicity **16** read in `ℤ⁴` and **1** read in the lattice its generators
are primitive in. Neither is an error. A multiplicity read without its lattice
is half a sentence, and `verify` says so every time.

**`crepant` is a question about what a subdivision adds.** A generator's
discrepancy is zero *by construction* wherever a height functional exists —
that is what `⟨u,v⟩ = 1` says. With no subdivision named the answer is `None`
rather than a vacuous `True`.

A non-simplicial cone still gets an answer: the missing multiplicity is
recorded with the reason, rather than refusing the certificate and losing the
other three quantities.

### `certo profile`

**Question** — How does the optimum respond as ONE capacity runs from `lo` to
`hi` — the whole function, not one value?
**Spec** — `ProfileSpec`
**Answers** — the piecewise-affine `f(t)`, its breakpoints, the dual that
bounds each segment and the source that attains each breakpoint
**Certificate** — `capacity_profile`, **solver-free**: exact rational
arithmetic
**Not established** — that the columns are all the columns, or that the rows
mean what they are called. A profile is a statement about the column set it
declares; if those came from a graph, that translation is a separate
obligation this does not discharge.

**Not `parametric`.** That certifies a *bound* for a family whose parameter
sits in the data, `A(p)`, `b(p)`, `c(p)`. This certifies a *function* of one
capacity, and the answer is concave, piecewise affine, with breakpoints.

**Why it decides rather than bounds.** Three finite facts give a statement
about a continuum. A dual's feasibility is `Aᵀy ≥ c`, which never mentions a
capacity — so **one dual bounds every `t` in its segment at once**. Two sources
at a segment's ends attain the whole segment, because interpolating them is
feasible at the interpolated capacity and its value is the interpolation. And
sorted segments sharing their endpoints tile the domain. Bound plus attainment
plus coverage is an equality.

**What it is for.** `f(1)` is the ordinary optimum; the shape near `t = 0` is
what a single optimum throws away. Two chordal pieces can be the same graph
with the same gap, and repeating one along an interface leaves the gap bounded
while repeating the other makes it grow — the difference is in the profile,
not in the value.

**You supply the breakpoints, the duals and the sources.** Finding them is
parametric programming and any solver may do it; `α`, `β` and every value are
recomputed here from the columns. A profile whose segments leave a gap, whose
dual misses a column, whose source overloads a row, or whose bound never meets
its source is **refused with no certificate** — a profile that does not hold is
not a smaller profile.

### `certo semigroup`

**Question** — Is this lattice point a non-negative integer combination of
these generators, and is the semigroup normal?
**Spec** — `SemigroupSpec`
**Answers** — whether the semigroup is pointed, with the grading that proves
it; whether the generating set is minimal, naming any redundant generator; and
per point, membership of the cone, of the group and of the semigroup itself
**Certificate** — `affine_semigroup`, **solver-free**: exact integer and
rational arithmetic
**Not established** — that the semigroup **is** normal. A witness refutes
normality; establishing it means deciding membership for every lattice point
of the cone, which is what Normaliz is for. `normal` is null by construction.

**The gap this fills.** `cone` answers questions about the *rational* cone
over a set of generators. A semigroup is what you can actually reach by
*adding* them, and the difference between the two is exactly where normality
lives. For `S = ℕ(1,0) + ℕ(1,1) + ℕ(1,3)`, the point `(1,2)` is in the cone,
is in the group — which is all of `ℤ²` — and is **not** in the semigroup. Those
three facts together refute normality, and each of them is arithmetic.

**Why every search terminates.** A pointed semigroup carries a grading: a
functional `u` with `⟨u,aᵢ⟩ ≥ 1` on every generator. Then any representation
`v = Σ cᵢaᵢ` with `cᵢ ≥ 0` satisfies `Σ cᵢ ≤ ⟨u,v⟩`, so the search is over a
finite set whose size is **computed, not guessed**, and the bound travels in
the certificate. `verify` redoes the search rather than believing it — which
is what a negative answer costs, and why it means something.

**A point outside the cone carries a separating functional**, not a promise.
`y` with `⟨y,aᵢ⟩ ≤ 0` for every generator and `⟨y,v⟩ > 0` is one vector,
checked by `k+1` dot products, instead of a claim that some search was
exhaustive.

**Not pointed is an answer, not a failure.** With no grading no search here is
finite, so the command says so and returns `out_of_theory` — with the
certificate it *can* establish, since the generators, the rank and the cone
answers are all still exact.

**A proposed minimal generating set is *decided*, not merely refuted.** Give
`hilbert` a set and certo settles whether it is the minimal generating system
of `S` — the one positive assertion in this command. For a pointed semigroup
that set is unique and is exactly the irreducible non-zero elements, so three
bounded questions settle it: every element is in `S`, every element is
irreducible, and every generator is reachable from the proposed set. The two
inclusions are the equality. `h` is reducible exactly when some generator `a`
has `h − a ∈ S` and `h − a ≠ 0`, which is `k` membership questions one rung
down in the grading — and a reducible element comes back with the
decomposition, because "not irreducible" is a claim.

**Unreachable and undecided are different answers.** A zero in the proposed
set breaks the grading and nothing below it terminates; that is reported as
`None`, never as "does not generate".

### `certo range`

**Question** — How far can this variable go — the whole interval, not one
point?
**Spec** — `Spec`, with `--var` naming the variable
**Answers** — the exact rational `min` and `max` over the regime, each with the
non-negative combination of hypotheses that yields it
**Certificate** — `variable_range`, **solver-free**: adding fractions
**Not established** — anything about the spec's **claim**, which is never read.
This bounds the variable over the hypotheses — the regime, not the theorem.

`check --hypotheses-only` exhibits a *point*. That answers whether the regime
is inhabited and nothing else, and a user who needed `a <= 1/3` got `a = 0` and
derived the rest by hand.

```
$ certo range examples/variable_range.py --var a
SATISFIABLE  [sat]
  a ranges over [0, 1/3], and that is the whole interval -- not one point of it
  a <= 1/3
    cheb x 1/3
  a >= 0
    a_nonneg x 1
```

The multipliers **are** the proof: `1/3` times the row `3a - 1 <= 0` gives
`a <= 1/3`, and LP duality says no combination gives a tighter one.

**The variables are free.** A regime is not a packing — `a` may be negative,
and a dual derived under `x >= 0` would certify a bound that does not hold. The
dual constraint here is an equality for exactly that reason.

**An unbounded end carries a ray, or it is not established.** `max x` over a
polyhedron is unbounded exactly when the polyhedron is non-empty *and* some
direction `d` has `A d <= 0` with `d[x] > 0`: from any feasible point you may
walk along `d` forever. That `d` travels in the certificate and `verify` walks
it against every row.

Without it, `unbounded` is a word rather than a claim — and that is what it
was until 0.11.2. A payload edited to say `unbounded` verified happily, and
`[0, 1]` came back as `[0, +inf)`: the one end with no evidence attached was
the one end nothing looked at. A certificate issued before 0.11.2 with an
unbounded end does not verify, because it asserts something it never carried
the evidence for.

**An empty regime is its own answer, not an infinite interval.** Over an empty
regime every direction is unbounded, and reading that as *the variable ranges
over everything* is the permissive-looking mistake, so inhabitation is asked
first — and a ray over an empty polyhedron establishes nothing, which is why
both halves are checked.

**A strict binding row leaves the endpoint open**: `a < 1/3` and `a <= 1/3`
have the same supremum and only one contains it.

Linear hypotheses only. A non-linear one is refused by name rather than
dropped, because dropping it would *widen* the range — wrong in the direction
that looks safe.

### `certo cycle`

**Question** — Does this parameter depend on itself — and can the loop close at
all?
**Spec** — `CycleSpec`
**Answers** — the chain, the growth class of every step, and the one comparison
that closes it
**Certificate** — `dependency_cycle`, **solver-free**: class arithmetic
**Not established** — that your growth classes are the real ones. That `k`
grows like a tower is what your lemma says; this checks what follows from it.
And a loop this route does not refute comes back *not established*, never
*there is no cycle*.

Three innocent lines, none of which mentions a cycle:

```
k     >= tower(1/delta)        the regularity lemma's bound
rho   <= K / (3 k**2)          what the crude count leaves
delta <= rho                   Chebyshev
```

There is one — `delta -> k -> rho -> delta` — and composing the bounds gives
`delta <= K/(3 tower(1/delta)**2)`, whose right-hand side vanishes faster than
any power of delta.

```
$ certo cycle examples/dependency_cycle.py
PROVED  [unsat]
  the cycle delta -> k -> rho -> delta cannot close: no positive delta survives it
  delta      >= tower      -> tower(u)^1
  k          <= poly ^-2   -> tower(u)^-2
  closes: delta (u^-1) <= rho (tower(u)^-2)
```

**The class is the argument, not a substitute for it.** Finding this by hand
means inventing a stand-in a solver can see — `k >= 1/delta` was the one
actually used — which proves something strictly weaker and leaves the tower
carried in prose.

**Monotonicity is tracked.** `rho <= K/(3k**2)` bounds rho from above only
because the map *decreases* in `k`, and a lower bound on `k` is what is
available. An edge whose available side does not support the direction needed
is **refused by name**: composing it anyway could declare a live regime empty,
which is the one error this must not make.

The ladder is `const < poly(d) < exp < tower`, and `exp` of a *vanishing*
argument is a constant rather than growth — claiming a tier there would close a
loop that does not close.

### `certo solve`

**Question** — What exactly solves this linear system — and if nothing does,
why not?
**Spec** — `LinearSystemSpec`
**Answers** — the solution over ℚ or ℤ, a kernel basis when it is
underdetermined, or an obstruction when there is none
**Certificate** — `linear_system`, **solver-free**: one matrix-vector product
**Not established** — that the solution is **non-negative**, or over ℚ that it
is **integral**. A rational solution to the equations of a packing is not a
packing.

The certificate is almost embarrassing: it is the solution, and checking it is
one product. That is the point. A number from a numerical library is a number
to be *trusted*; `x` with `A` and `b` beside it is a number to be
**multiplied** — and against the system that was *stated*, rather than the one
somebody remembers stating.

**Unsolvable is certified too:** `y` with `y·A = 0` and `y·b ≠ 0`, which is a
row operation the elimination already performed, kept instead of thrown away.

**Underdetermined is not rounded to "a solution".** A particular solution plus
a basis of the kernel says what the solution *set* is. Reporting one point of
an affine subspace as though it were the answer is how a free parameter
disappears from a write-up.

**Over ℤ the Smith normal form decides it**, and "no integer solution" is a
different answer from "no solution". The edge-by-triangle incidence matrix of
`K₄` with `y` all ones gives `(½,½,½,½)` over ℚ and *nothing* over ℤ, blocked
by the last invariant factor.

### `certo parametric`

**Question** — I checked it for `p = 5..12`. Does it hold for EVERY `p`?
**Spec** — `ParametricSpec`
**Answers** — a bound proved for the whole family, from one dual
**Certificate** — `parametric_bound`, **solver-free**: expand and read signs
**Not established** — anything below the floor, anything about an integer
optimum, and nothing at all on failure. The shift test is **sufficient and not
necessary**, so a failure means *not established by this route*, never
*false* — and **no certificate is emitted**, because a route that did not work
is not a bound.

For a linear program whose data are polynomials in a parameter, weak duality
is available symbolically: any `y ≥ 0` with `A(p)ᵀy ≥ c(p)` gives
`opt(p) ≤ b(p)·y` for every `p` at once.

```
$ certo parametric examples/parametric_bound.py
PROVED  [unsat]
  for all p >= 10, the optimum is at most 1/6*p^2 + 1/6*p - 2/3
  and that is every value with p >= 10 -- not a sample of them
```

And it is not loose — at `p` = 10, 11, 15, 30 the bound equals the optimum.
**One dual, read off one solved instance at `p = 10`, gives the exact optimum
for every `p` above it.**

certo does not search for `y`. `certo opt` on a single instance hands you one;
what this checks is that the `y` you already have works for the whole family,
and that check is arithmetic: substitute `p = p₀ + u`, expand, read the signs.

`sense="min"` with `≥` rows is the **cover** shape, bounding from below out of
a feasible packing. Two things change and both are forced: a cover's dual is
itself a packing, so a dual entry may be a polynomial; and a threshold in the
value function *is* the dual's feasibility running out. See
[Where parametric came from](CASES.md#where-parametric-came-from).

### `certo peak`

**Question** — I solved it for `n = 1..40`. Which integer is best for EVERY
`n`?
**Spec** — `PeakSpec`
**Answers** — the integer maximiser and the value there, for the whole family
**Certificate** — `integer_peak`, **solver-free**: expand and read signs
**Not established** — anything for a maximiser with non-integer coefficients,
which is **refused** rather than assumed integral. An argument about a point
that does not exist proves nothing.

A write-up reaches the answer like this: complete the square, observe the
objective is an integer at integer argument, conclude the maximum is the
**floor** of the continuous peak. Every step is right and none is checkable,
because the floor of a parametric expression is not a polynomial — there is
nothing to expand.

Move the origin to the claimed maximiser `x*` instead. For any integer step
`t`, `q(x* + t) − q(x*) = A t² + q'(x*) t`, which for `A < 0` is `≤ 0` for
every non-zero integer `t` **exactly when** `A ≤ q'(x*) ≤ −A`. Two polynomial
inequalities, checked by the same shift `parametric` uses. No floor anywhere.

`x*` is an integer, so the value **is attained**: the certificate says no
integer does better *and* that this integer does that well.

### `certo entry`

**Question** — Where does this first cross the line — and by how little?
**Spec** — `EntrySpec`
**Answers** — the index of the first crossing, the value there, and the two
terms that bracket it
**Certificate** — `first_entry`, **solver-free**: exact rationals
**Not established** — that the sequence is the one you meant. The prefix
carries the values up to the crossing and nothing past it, because nothing
past it is part of the claim.

```
$ certo entry examples/first_entry.py
PROVED  [unsat]
  first crosses 1/2 at index 9, where the value is 3/5 -- and by at most the
  step bound, so inside [1/2, 7/10)
```

### `certo moment`

**Question** — Is the expected number of bad events below one — so one good
object exists?
**Spec** — `MomentSpec`
**Answers** — the expectation, and the mass it leaves over
**Certificate** — `first_moment`, **solver-free**: re-add exact rationals and
compare
**Not established** — that the probabilities describe the experiment you
meant. What is checked is that they *are* probabilities, that the sum is the
sum, and that the comparison holds.

```
$ certo moment examples/first_moment.py
PROVED  [unsat]
  E[X] = 15/32 < 1, so SOME OUTCOME HAS NONE of them: an object avoiding
  every one of these 15 events exists
```

### `certo ratio`

**Question** — Is this fraction inequality true for EVERY `n`, without a
solver?
**Spec** — `RatioSpec`
**Answers** — the cleared numerator and the sign of the denominator
**Certificate** — `ratio_bound`, **solver-free**: cross-multiply, expand, read
signs
**Not established** — anything below the floor. It holds for every parameter
value at or above it and says nothing beneath.

```
$ certo ratio examples/ratio_window.py
PROVED  [unsat]
  for all n >= 2: (n - 2) / (n^2) <= (1) / (n)
  difference: 2*n
```

### `certo family`

**Question** — What is the largest of these ten thousand LPs — and can nothing
beat it?
**Spec** — `FamilySpec`
**Answers** — the winner, its value, and a dual certifying that nothing else
reaches it
**Certificate** — `family_extremum`; verification rebuilds each item's program
from the spec
**Not established** — that the family is the one you meant. Completeness of
`items` is the spec's claim, the way a sweep's domain is.

### `certo exists`

**Question** — Does one exist at all — and if not, can you prove it?
**Spec** — `CoverSpec`
**Answers** — a model, or a DRAT refutation
**Certificate** — `cnf_model` or `drat`, both **solver-free**
**Not established** — anything outside the candidate set you supplied.

```
$ certo exists examples/no_decomposition.py
PROVED  [unsat]
  NO exact cover exists over these 9 candidate parts, for a universe of 15.
  The DRAT refutation says so; it needs no solver to re-check
```

---

## Does it hold for every case?

### `certo sweep`

**Question** — Does it hold for every graph on `n` vertices?
**Spec** — `SweepSpec` for graphs, `DomainSpec` for any finite domain
**Answers** — the verdict over the family, **and which of three levels was
established about the predicate**
**Certificate** — `sweep` / `domain_sweep`; solver-freedom depends on the
predicate
**Not established** — the theorem. A finite domain was checked, not every `n`.
And separately: nothing says the predicate answered correctly, unless it
returned certificates.

Those two caveats are independent, and the banner names which level you got:

| Level | What holds | When |
|---|---|---|
| **certified** | every evaluation carries its own certificate; the predicate is not trusted at all | the predicate returns `Outcome(ok, cert=...)` **and** `--cert-all` stores them |
| **reproducible** | the domain, its hash, and a verdict vector: re-running the predicate gives the same answers | a bare `bool` predicate — the common case |
| **recorded** | only the domain and its hash | the spec is gone, moved, or was never stamped |

A green banner over eleven thousand unchecked booleans is where the old
phrasing did the most damage: there is no counterexample to go and look at.

`--witnesses` decomposes the counterexamples into orbits under a symmetry you
declare. `--collect` measures instead of refuting, in exact rationals.
`--n-range 3..8 --stop-on-first` gives one sub-certificate per size plus the
claim that nothing failed below the first failure. Full treatment in
[What a sweep establishes](CASES.md#what-a-sweep-establishes).

### `certo cases`

**Question** — For every item of a finite domain / is this CNF unsat?
**Spec** — `CNFSpec`, or `DomainSpec`
**Answers** — satisfiability, with a **DRAT proof** when unsatisfiable
**Certificate** — `drat`, **solver-free**: RUP/RAT checking
**Not established** — the theorem. It settles the **finite case**.

The built-in CDCL is Python and slow. It exists because pysat's proof logging
does not work on Windows, and without a proof there is no certificate. For
large instances: `certo cases spec.py --solver-binary /path/to/cadical`.

You do not have to trust that CDCL. A malformed proof is rejected by the DRUP
checker and you get `ERROR`, not `PROVED`. **The checker audits the solver.**

### `certo shrink`

**Question** — My counterexample is huge — what is the real one?
**Spec** — `SweepSpec` or `DomainSpec`, with a `reduce`
**Answers** — a minimal witness, with the descent recorded
**Certificate** — `shrink_graph` / `mus`; needs the spec module
**Not established** — minimum-ness. It gives a **1-minimal**, not minimum,
counterexample.

It has to know what "one step smaller" means. The shapes that keep coming back
have names:

| `reduce=` | Does |
|---|---|
| `"auto"` | picks from the item's type, or **refuses** |
| `"sets"` | drop one element |
| `"sequences"` | drop one element of a list or tuple |
| `"decrement"` | lower one integer coordinate by one |
| `"graphs"` | delete one vertex |
| `"masks"` | clear one set bit |
| a callable | whatever you wrote — untouched |

`auto` treats a tuple of integers as a **parameter point**, not a collection:
`(3, 1)` reduces to `(2, 1)` and `(3, 0)`, not to `(1,)` and `(3,)`. And it
refuses on a type it does not recognise rather than inventing something — a
witness that is minimal for the wrong relation looks exactly like one that is
minimal for the right one.

The trace records the **index** taken into `reduce()` at each step, not just
the resulting id, which is what lets verification replay the exact descent
instead of re-running the search.

### `certo sweep --witnesses`

**Question** — A thousand failures — how many objects is that?
**Spec** — `SweepSpec` or `DomainSpec` with `canonicalize=` or `labelling=`
**Answers** — the orbits of the counterexamples, and one minimal witness per
orbit
**Certificate** — `sweep` carrying the orbit decomposition
**Not established** — that two items sharing a canonical form really are in
the same orbit, when you pass `canonicalize`. That is the spec's claim.
Passing `labelling` instead moves it to the checked side.

A sweep reporting 1,400 counterexamples where there are four structural ones
has not told you four things and buried them — it has told you one thing 1,400
times and left the reading to you.

```
$ certo sweep examples/sweep_orbits.py
REFUTED  [sat]
  REFUTED: 10 counterexamples out of 64 examined -- 10 labelled, 3 up to symmetry
  orbits (of the counterexamples):
    (1,2,3)   x6   (1,2,3), (1,3,2), (2,1,3)
    (1,1,4)   x3   (1,1,4), (1,4,1), (4,1,1)
    (2,2,2)   x1   (2,2,2)
```

Nothing here knows what the group is, and it does not need to — it needs to
know when two items are equal. The representative is the one with the smallest
id: arbitrary, but **deterministic**, so two runs never produce certificates
that look contradictory while saying the same thing.

The honest line, and the alternative that moves it, are in
[Orbits you can check](CASES.md#orbits-you-can-check).

### `certo enum`

**Question** — Which graphs on `n` vertices are there, up to isomorphism?
**Spec** — `SweepSpec`, or flags
**Answers** — the canonical list and its hash
**Certificate** — `graph_set`, **solver-free**
**Not established** — **completeness**. The certificate verifies
non-isomorphism and the filters, not that the family is all of them.

`filters` accepts callables alongside the named ones. The counts stay separate
(`enumerated` before filtering, `in_family` after), and `verify` says plainly
that a programmable filter cannot be re-checked from the certificate alone,
because it lives in the spec.

---

## Algebra, numbers and structures

### `certo ideal`

**Question** — Do these polynomial equations have a solution?
**Spec** — `IdealSpec`
**Answers** — the Gröbner cofactors showing `1 ∈ I`, or certifying
`f = Σ hᵢgᵢ`
**Certificate** — `ideal`, **solver-free**: expand a product and compare
coefficients
**Not established** — anything about **real** roots. The field is ℂ. `1 ∈ I`
refutes solutions over ℂ, hence over ℝ, ℚ and ℤ; the converse does not hold.

```
$ certo ideal examples/ideal_inconsistent.py
PROVED  [unsat]
  the system has NO common solution: 1 is in the ideal, and the cofactors prove it
  cofactors:
    g0 * (2/7)
    g1 * (2/7*y - 3/7)
    g2 * (-2/7*x - 3/7)
```

Multiply that out and you get `1`. That is the whole proof. Finding the
cofactors is a Gröbner basis computation; a library that merely says "yes,
it's in the ideal" leaves you with nothing but its word.

**It decides.** Gröbner basis membership is decidable, so a negative answer is
`REFUTED`, not `unknown_solver`. That is rare in this tool and worth using:
`prove` on a system of polynomial equalities can grind where this answers.

### `certo eliminate`

**Question** — Get rid of `t` and tell me the condition on `s`
**Spec** — `EliminateSpec`
**Answers** — the resultant, with the Bézout identity `Res = A·f + B·g`
attached
**Certificate** — `resultant`, **solver-free**: expand two products and
subtract
**Not established** — sufficiency over ℝ. `Res = 0` is **necessary** for a
common root over any field, **sufficient** over an algebraically closed one,
and only where the leading coefficients do not both vanish. `verify` names
that locus specifically.

```
$ certo eliminate examples/eliminate_parameter.py
SATISFIABLE  [sat]
  eliminated t. A common root exists only where this vanishes: -4*s^3 + 1
```

That example is chosen so you can check it by hand: substitute `t² = s` into
`t³ + st + 1` to get `2st + 1`, so `t = −1/(2s)`, and back into `t² = s` gives
`4s³ = 1`.

Computing a resultant is a determinant over a polynomial ring; checking one is
expanding two products. The determinant is Bareiss — fraction-free, where every
division is a polynomial division whose remainder is **asserted to be zero**
rather than assumed.

A non-zero constant resultant is a refutation, conclusive in the strong
direction and costing one determinant.

**Two definitions of the same quantity are this question.** A first moment
fixing `A m = P6 t^4` and a second fixing `A^2 m = P11 t^6` are two equations
for one `A`, and whether they agree is the resultant of the pair in `A`:

```
$ certo eliminate examples/overdetermined.py
  eliminated A. A common root exists only where this vanishes:
  m*P6^2*t^8 - m^2*P11*t^6
```

which factors as `m t^6 (P6^2 t^2 - m P11)`, so away from the degenerate cases
the compatibility condition is `P6^2 / P11 = m / t^2` -- the identity a
doubling argument produces, recovered rather than assumed. An incompatibility
found this way is found now, not when the formalisation refuses to close.

**Exactly two polynomials**, because that is what a resultant is. Iterating
pairwise over a larger system introduces extraneous factors that nothing here
could certify away; three definitions of one quantity is an ideal membership
question, and `ideal` is the command for it.

### `certo sos`

**Question** — Is this polynomial non-negative everywhere?
**Spec** — `SOSSpec`
**Answers** — exact rational squares
**Certificate** — `sos`, **solver-free**: expand a product
**Not established** — negativity, ever. From degree 4 in 3 variables there are
non-negative polynomials that are not sums of squares — Motzkin's is the
standard one — and `certo sos` comes back `unknown_solver` on it, never "the
polynomial goes negative".

The pipeline: write `p = zᵀGz` (a linear condition on `G`), find a numeric `G`
by alternating projections onto that subspace and the PSD cone, round it,
**project back onto the subspace exactly in `Fraction`**, then do an exact
LDLᵀ. If every pivot is non-negative the decomposition *is* the sum of squares.
The floats were the search; they never reach the certificate.

For degree 2, `farkas --nonlinear` is cheaper and gets there first.

### `certo number`

**Question** — Is this integer prime?
**Spec** — `NumberSpec`, or `--n`
**Answers** — a Pratt certificate, or a factorisation with `--question factor`
**Certificate** — `number`, **solver-free**: modular exponentiation
**Not established** — nothing beyond primality of what you asked about.

`n.is_prime()` is true, fast and uncitable. A Pratt certificate is the same
fact with the evidence attached: `n` is prime exactly when some `a` generates
`(ℤ/n)*`, and those prime factors of `n−1` need certificates too, so the thing
is a **tree** recursing down to 2.

Three details that separate a certificate from a test:

* **The factor list must be complete.** Missing one prime factor of `n−1`
  would let a composite through, so `verify` checks the factors multiply back
  to `n−1` before it looks at the witness.
* **Carmichael numbers.** 561 passes the Fermat condition for most bases; the
  order condition catches it, and `certo number --n 561` comes back `REFUTED`
  with no certificate.
* **The witness is reproducible.** Small bases are tried in order rather than
  randomly, so the same `n` gives the same certificate — and the same digest —
  on every machine.

### `certo cover`

**Question** — Is this really a clique partition, and how large?
**Spec** — `CoverSpec`
**Answers** — every part checked to be a clique, every element counted exactly
once, and with `--optimize --prove-optimal`, how far that is from the minimum
**Certificate** — `exact_cover`, **solver-free**: counting
**Not established** — minimality, unless you ask for it. A cover certificate
is an **upper bound**.

That last line cost somebody real work: a user read one as an optimum,
reported a construction of 780 parts where the obvious one uses about 41, and
called the difference a property of the graph rather than a fact about their
construction. Nothing in the certificate was wrong; the missing half was the
lower bound.

```
$ certo cover examples/cover_optimize.py --optimize --prove-optimal
  and how close that is to the minimum:
    your cover      21 parts   (an UPPER bound, certified above)
    relaxation      7   (a LOWER bound, exact rational dual -- fractional,
                         so not a cover you can build)
    integer optimum 7   (PROVED by branch and bound)
```

Three numbers, three statuses, and the labels travel with them.
`CoverSpec(candidates=...)` is **required** for this and refused rather than
guessed: a cover is only minimal relative to what you were willing to use.

Three ways it goes wrong, reported as three different things:

| What is wrong | What comes back |
|---|---|
| a part is not a clique | **inconclusive**, with the offending pairs named — that is a statement about the graph, not about the cover, and no certificate is written |
| an edge is covered twice | **REFUTED**, naming the edges, and pointing out that `exact=False` would make the same data a valid cover |
| an edge is covered zero times | **REFUTED**, naming the edges |

Finding a minimum clique partition is NP-hard and deliberately not what this
does. Bring your own, from whatever found it.

---

## Build it, assemble it, keep it

### `certo synth`

**Question** — Does an object with these properties exist?
**Spec** — `SynthSpec`
**Answers** — the object, plus the counterexamples that forced it
**Certificate** — `cegis`; re-solves
**Not established** — a theorem. `synth` searches a **bounded** domain, the
banner says `CANDIDATE SYNTHESISED -- BOUNDED search`, and that is a discovery.

`--prove-candidate` chains the general statement onto it:

```
$ certo synth examples/synth_prove_identity.py --prove-candidate
CANDIDATE SYNTHESISED -- BOUNDED search  [sat]
    A = 2
    B = -2
UNIVERSAL SYMBOLIC PROOF: PASS  [unsat]
```

The combined certificate carries both halves and `verify` checks each
separately, because they say different things. The spec has to **declare**
what the general statement is, because it is not derivable: it usually changes
the domain *and the sort*. The search runs over bounded integers and the proof
over the reals, which is where polynomial arithmetic is decidable.

### `certo compose`

**Question** — How do I assemble my lemmas into one proof?
**Spec** — `ProofSpec`
**Answers** — the theorem, with every lemma either **linked** or named as a
**bridge**
**Certificate** — `proof`; re-solves
**Not established** — any bridge. A bridge is asserted, not derived, and it is
reported by name **every single time the proof is verified**.

A lemma given by `proves=` is discharged and **linked**: what its certificate
really closes *entails* the statement handed to the final step. A lemma proved
for `x ≥ 1` and declared as `x ≥ 2` is refused by name, at the point of
assembly, and nothing is emitted.

A lemma given by `certificate=` is a **bridge**. A DRAT proof talks about
propositional variables called `e0_1`; it does not talk about a Ramsey number.
The step from "this encoding is unsatisfiable" to "R(3,3) ≤ 6" is the
encoding's *meaning*, and no checker can confirm it. So bridges are not
refused — they are made visible.

```
$ certo verify out/proof.json
  [ok] the final step uses only the lemmas and the theorem's own hypotheses
  [ok] nothing entered the proof undeclared
  WARNING: BRIDGE: upper is asserted, not derived -- the DRAT proof closes...
  WARNING: lemmas the theorem does not need: spare
```

The bridge is in the author's head either way. The difference is whether the
reader can see it and weigh it.

"NOT needed" comes from the final step's own unsat core, not from a guess.
Expect it to catch more than you think: over linear real arithmetic Z3
rederives most auxiliary lemmas by itself, and the ones that survive as
*needed* are precisely those carrying something the theory cannot reach.

Two *derived* lemmas can never contradict each other — both are true. Only
**bridges** can, and two bridges that clash make the whole theorem vacuous,
which is reported by name.

### `certo verify`

**Question** — Is this stored certificate still good?
**Spec** — none; it takes a certificate path
**Answers** — every check, passed or failed, plus **the warnings repeated**
**Certificate** — none
**Not established** — that the spec still matches. If the file changed since
the certificate was issued, `verify` accepts the certificate and warns: it is
still valid on its own, but it no longer corresponds to what is there now.

The warnings are the part that ages well. A vacuous proof keeps saying it is
vacuous; a sweep keeps saying what it did not certify; a multiplicity keeps
naming its lattice. Months later, on the artefact alone.

### `certo bind`

**Question** — Does the Lean lemma actually give what my certificate assumed?
**Spec** — `BindSpec`
**Answers** — whether what you say the declaration **provides** entails the
hypothesis the certificate rests on
**Certificate** — `lean_binding`; re-asks the entailment, so not solver-free
**Not established** — that your rendering of the declaration is faithful.
Nothing here reads Mathlib. It is a **bridge**, and `verify` says so every
time.

The failure this exists for: a bound certified *assuming* the fine counting
estimate, and a packaged `patCount_K4_le` that uses density `<= 1` and gives
something useless — found three modules later, by going to read the statement.

```
$ certo bind examples/lean_binding.py
REFUTED  [sat]
  PaperIV.MomentErrors.N1_from_counting does NOT provide what fine_count
  assumed: the certificate rests on something stronger than the declaration gives
```

certo reads the certificate's provenance, loads the spec it came from, finds
the hypothesis named in `discharges`, and asks the entailment. What changes is
**when** it bites — at bind time, while you are looking at the statement — and
that `status` can count it.

**A spec that has moved is reported stale** rather than read as if it had not.
The certificate carries the hash of the file it was made from, and a binding
checked against a statement that has since changed would be worse than none.

### `certo export`

**Question** — Get this into Lean
**Spec** — none; it takes a certificate or a spec
**Answers** — a spec as SMT-LIB2 or DIMACS; a **linear Farkas certificate** as
a runnable `linarith` example
**Certificate** — none
**Not established** — anything else. `--lean` emits **one** thing, on purpose.

```lean
theorem from_core (x y : ℝ)
    (x_ge_1 : 1 - x ≤ 0)
    (y_ge_1 : 1 - y ≤ 0)
    : -2 + x + y ≥ 0 := by
  linarith [x_ge_1, y_ge_1]
```

Everything else certo used to emit was scaffolding that did not compile, and
a Lean file that does not compile is worse than no Lean file: it costs a build
to discover. Where the multipliers are already verified and `linarith` decides
the fragment the goal lives in, the export is trustworthy; everywhere else the
certificate is the deliverable, and what a formalisation needs from it is the
numbers and the statement, which are both in there.

`certo status` scans a directory for Lean statements of the shape
`theorem foo : True := by`, so a hollow file left behind by an older workflow
is found rather than assumed gone.

### `certo ledger`

**Question** — What did I run last month?
**Spec** — none
**Answers** — an append-only log, re-verifiable
**Certificate** — none
**Not established** — nothing; it stores paths and digests, never copies.

```bash
certo opt spec.py --cert c.json --log --note "K6 bound" --tag paper
certo ledger verify
```

```
  [ok] 2026-09-16T00:45:23  core     core of 4 formulas
  [!!] 2026-09-16T00:45:25  opt      digest 3653579e... != logged 681631ea...
  2 entries: 1 verified, 0 FAILED, 1 changed since logged
```

**Append-only**: a later run that contradicts an earlier one is a new line, not
an edit. **No copies**: only each certificate's path and digest, so a tampered
or missing certificate shows up as a failure rather than being quietly
duplicated into the log.

---

## Entry points and bookkeeping

### `certo ask`

**Question** — Just run whatever this spec asks for
**Spec** — any of them
**Answers** — whatever the routed command produces
**Certificate** — whatever the routed command produces
**Not established** — nothing extra; routing changes who answers, not what the
answer means.

One entry point that loads a spec, reads its type, and runs the command that
type belongs to. `certo what` is the same command.

### `certo commands`

**Question** — Which command answers which question?
**Spec** — none
**Answers** — this page, in your terminal, in your language
**Certificate** — none
**Not established** — that a listed command can answer *your* instance. It
routes by the shape of the question, not by whether the problem is in range.

```
$ certo commands
  HOW BIG, HOW SMALL, HOW MANY?
    certo opt                          What is the optimum, exactly?
    certo order                        Does this term DECAY in n, or is it Theta(1)?
```

This exists because of a failure worth recording. `certo order` shipped in
0.5.0 with its own section, example and two table rows. A user spent a session
writing it by hand in Python three times, then asked for it as *the one
function I would want in 0.7*. They had searched for "asymptotic" and
"decays"; the command is called `order`.

So `certo asymptotics` and `certo decays` now run it, the help line leads with
*"does this term DECAY in n"* rather than with the exponent, and `lint` names
the command when a claim divides by a product of symbols — the shape of a
magnitude question, which `prove` cannot answer. That trigger is deliberately
narrow: **two or more** distinct symbols at negative exponent, because one is
far too common to mean anything. Across the shipped examples it fires zero
times.

`certo what <command>` asks the same question about one command: its spec,
engine, certificate kind and tier.


### `certo repro`

**Question** — What does a referee need to redo this?
**Spec** — none
**Answers** — a bundle: spec, certificates, versions and hashes
**Certificate** — the bundle itself
**Not established** — that the referee's machine will agree. It will, for our
engines; a `sweep` predicate calling scipy is outside that guarantee.
