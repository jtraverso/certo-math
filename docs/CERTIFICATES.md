# Certificates

With an LLM in the loop the dominant risk is not a shortage of ideas, it is
**plausibility without verification**. One design rule follows:

> The LLM proposes, the engine certifies, and the certificate survives without
> the LLM.

A verdict you cannot re-check is a rumour. Every command here produces an
artefact instead, and most of them re-check with nothing but arithmetic.

## What "solver-free" buys

A certificate marked *solver-free* is checked with arithmetic, evaluation,
counting or unit propagation. You need trust neither Z3 nor CBC — and neither
does the person reading your paper, which is the actual point. A Z3 `unsat` is
an assertion; a verified DRAT proof is something a referee checks on their own
machine without running your code.

It is also a safety net. If the solver had a bug, the certificate would not
verify and you would get `ERROR`, not `PROVED`.

**`verify`'s own header is authoritative.** It says how that particular
certificate was checked — *"verified without a solver"*, *"checked by
counting, no solver"*, *"by re-running the spec, not by trusting its
answers"*. The table below is the map; the header is the territory.

## The forty-seven kinds

| Kind | What it attests | Solver-free? |
|---|---|---|
| `model` | a `prove` counterexample, or a non-empty regime | **yes**, substitute and simplify |
| `cnf_model` | an assignment satisfies the CNF | **yes**, evaluation |
| `unsat_core` | the hypotheses are contradictory | **yes** when the core is linear (Farkas multipliers travel); otherwise re-solves the core alone |
| `mus` | unsatisfiability **and** minimality | **yes** |
| `core_matrix` | one core per goal, and that the table says what the cores say | as `unsat_core`, per goal |
| `farkas` | a combination of the hypotheses that closes the system | **yes**, adding fractions |
| `farkas_ray` | infeasibility of an LP | **yes**, adding fractions |
| `lp_dual` | exact optimality of an LP | **yes**, rational arithmetic |
| `branch_bound` | an integer optimum, every leaf closed by its own certificate | **yes**, exact arithmetic |
| `mixed_design` | a construction exists and attains a value; **not** that it is optimal | **yes**, exact arithmetic |
| `gap` | an upper and a lower bound, and the distance between them | no: the integer side re-solves |
| `drat` | unsatisfiability of a CNF | **yes**, RUP/RAT |
| `graph_set` | a non-isomorphic family passing the filters | **yes** |
| `sweep` | family + predicate certificates | depends on the predicate |
| `domain_sweep` | domain, verdict vector, and the predicate replayed | re-runs the spec |
| `sweep_range` | one sub-certificate per size, and the order | as its children |
| `orbit_witnesses` | each member is the representative relabelled | **yes**, re-apply the permutation |
| `shrink_graph` | the counterexample is 1-minimal | yes, needs the spec module |
| `shrink_domain` | the descent, replayed by index | yes, needs the spec module |
| `bisect` | the pair bracketing the threshold | depends on its children |
| `ideal` | `f = Σ hᵢgᵢ`, or `1 ∈ I` | **yes**, expand a product |
| `resultant` | `Res = A·f + B·g` | **yes**, expand two products |
| `sos` | `p = Σ dᵢqᵢ²` in exact rationals | **yes**, expand a product |
| `number` | primality, or a factorisation | **yes**, modular exponentiation |
| `asymptotic` | the exponent of a parameter in a term | **yes**, exact arithmetic |
| `ball` | a real quantity lies in an interval, and that settles the claim | **yes** for the claim; the interval needs the spec |
| `parametric_bound` | `opt(p) ≤ b(p)·y` for all p, or `≥` for a cover | **yes**, expand and read signs |
| `parametric_symmetry` | the symbolic quotient of a family, and its regimes | **yes**, symbolically; the window needs instances |
| `integer_peak` | no integer beats `x*`, and `x*` attains the value | **yes**, expand and read signs |
| `ratio_bound` | a fraction inequality above a floor | **yes**, cross-multiply and read signs |
| `first_entry` | where a sequence first crosses a line | **yes**, re-find it in exact rationals |
| `first_moment` | `E[X] < 1`, so a good object exists | **yes**, re-add and compare |
| `exact_cover` | every element in exactly one part | **yes**, counting |
| `symmetry_reduction` | the three hypotheses of the averaging argument | **yes**, the quotient is rebuilt |
| `equitable_quotient` | the partition, both regularities, and the two maps | **yes**, exact counting |
| `integer_matrix` | rank, determinant, Hermite, Smith, with the transforms | **yes**, matrix multiplication |
| `linear_system` | `A x = b`, or an obstruction `y·A = 0`, `y·b ≠ 0` | **yes**, one product |
| `toric_cone` | primitivity, multiplicity, height, discrepancies | **yes**, exact determinant and solve |
| `family_extremum` | the largest of a family, and a dual for the rest | rebuilds each item's program |
| `hypothesis_audit` | a verdict per hypothesis, with the breaking assignment | no — substituting a witness leaves a ground formula, and deciding that is still a solver call |
| `variable_range` | the interval a variable may take: a Farkas combination at a bounded end, a feasible ray at an unbounded one | **yes**, adding fractions and walking the ray |
| `dependency_cycle` | a cycle in a parameter's own dependencies, and the comparison that closes it | **yes**, class arithmetic |
| `lean_binding` | what a certificate assumed, against what a declaration provides | no, re-asks the entailment |
| `cegis` | the object has no counterexamples in the bounded domain | no, re-solves |
| `synth_proved` | the bounded discovery **and** the universal statement | no, re-solves |
| `proof` | the lemmas, **and** that each is used as its certificate allows | no, re-solves |
| `induction` | the base cases, the step, **and** that they chain without a gap | no, re-solves |

## They are tamper-evident

Edit a dual's objective by hand and `verify` catches it. Touch a step of a
DRAT proof and it stops being RUP. Change a multiplicity in a cone certificate
and it no longer matches what the generators give.

This is not incidental — it is why quantities are **recomputed** during
verification rather than read back. A branch-and-bound node derives its own
linear program from the root system and its own fixings; a symmetry quotient
is rebuilt from the generators; a cone's every number is redone from the rays.
A payload nobody recomputes is a payload anybody can edit.

One real instance of that going wrong, before it was fixed: a dual for a
node's relaxation is a valid dual for **some** linear program, and nothing in
it says which node it came from. A tree that stored one per node and checked
each on its own terms accepted two of them **exchanged**, and an expensive
subtree closed by a cheap one's certificate read exactly like a complete proof.

## Which way is up: the frame of an `lp_dual`

`A`, `b`, `c`, `primal`, `dual` and `objective` are stored in the internal
**maximised** system, because that is the only frame where `c.x == b.y` closes.
A spec written `sense="min"` is solved as `max -c.x`, so those numbers are the
negation of the ones you asked for.

The payload never said so. A minimisation whose answer was `3/2` was archived
as `"sense": "min", "objective": "-3/2"` and **verified** — consistent with
itself in a frame it did not name. The screen said `3/2` and the file said
`-3/2`, and nothing said which was which.

So the artefact carries both:

```json
"sense": "min",
"objective": "-3/2",            // the internal system, where c.x == b.y
"declared": {"objective": "3/2"}   // the sense you asked for
```

`declared` is **optional**, the way `loads` is: a certificate written before it
existed verifies exactly as before, and the schema stays at 4. It is derived
when the certificate is built and **recomputed** by `verify` — edit it and the
certificate is rejected, like every other number here.

## A pointer is not a check

`verify` takes **one certificate and no filesystem**. That is deliberate -- an
artefact somebody has to hold a directory to check is an artefact nobody
checks -- and it has a consequence worth stating plainly: **a stored path or
digest is a field nothing can ever recompute.**

`lean_binding` had one. It says *this is what THAT certificate assumed, and
this Lean declaration provides it*, and what tied the two was the string
`"certificate": "out/counting_bound.json"`:

```
honest  : VALID | certificate = out/counting_bound.json
forged  : VALID | certificate = out/a_file_that_does_not_exist.json
```

Same verdict, a file that is not there, a kind it never was. The entailment
was re-asked correctly from the formulas in the payload; it was the *link*
that nothing checked.

The certificate travels inside the binding now. `verify` re-checks the link
with no disk: the embedded source has to verify on its own terms, be the kind
claimed, and carry the provenance of the spec whose hash the binding recorded.
The guarantee is **exactly as strong as the inner verifier and no stronger** --
tampering with an `unsat_core`'s `core_smt2` is caught, tampering with a field
that `unsat_core` does not check is not.

The same reasoning is why the manifest's relations are **computed from
content** rather than declared. A digest stored in a parent would have been
this defect added on purpose.

## The Lean certo emits is checked before it leaves

*Can we certify that generated Lean is syntactically valid, without building
it?* Not as asked, and the reason is worth knowing: **Lean 4's grammar is
extensible, so what parses depends on what is imported.** `!![1, 2; 3, 4]`
without `Mathlib.LinearAlgebra.Matrix.Notation` fails with `unexpected token
';'` -- a parse error caused by a missing import. There is no
import-independent notion of "syntactically valid Lean", and `lean` has no
parse-only mode: it parses and elaborates together.

What is decidable without a toolchain is narrower and useful: the invariants
certo's own emission must satisfy. `check_emission` checks them in
milliseconds -- balanced namespaces, every declaration reaching its `:=`, a
`/--` attached to a declaration, `sorry` present exactly when the header says
so, imports matching what the exporter declares.

Measured against the only exporter that ever had bugs: adding the Smith one
took four rounds against a real Mathlib and produced five emission faults.
These rules catch three. The other two were a module path that had moved and
an absent import, and nothing without Mathlib on disk can know either.

That ratio is the point. `tests/run_lean.py` cannot be a release gate --
minutes per file, a toolchain dependency, failures that say nothing about
whether certo's mathematics is right -- so nothing checked an emission between
one of those runs and a release. This does, for every registered exporter, on
every suite run.

## A search that ran out of budget

`branch_bound` claims an optimum, and pays for it: every leaf closed, every
branch covered. Branch and bound is exponential, so a real run often does not
finish -- and until 0.12.1 a stopped one returned `resource_exhausted` with
**no certificate at all**. Its own status report said so: *"Not a certificate
-- a status report"*. It also dropped the stack of nodes it had not opened.
Hours of search left nothing that could be verified, archived or combined.

`branch_frontier` is that run as an artefact. It claims an INTERVAL:

```
the optimum lies in [incumbent, bound]
this design attains the lower end
these OPEN subproblems are everything that remains
```

The third clause is what makes it a certificate rather than a log, and it is
checked the way a closed tree's completeness is checked: every branching node
has all its children, and every child is closed, branching, or declared open.
A frontier that quietly dropped a subtree fails exactly as a tree that dropped
one does.

**An open node carries its parent's dual, and its parent's fixings with it.**
A child's feasible set is a subset of its parent's, so the parent's dual
bounds the child too -- and both halves are checked: the dual against the
parent's derived program, and that the child really does extend the parent.
Inheriting only the number would have been free and would have inherited
something nothing checks, because a branching node's bound is verified nowhere
in a closed tree: no claim rests on it there. Here one does.

**What it does not claim: that the incumbent is optimal.** That is the point.
`verify` says so as a warning on every one of them.


## The warnings are part of the artefact

A certificate carries what it does *not* establish, and `verify` repeats it
every time — months later, when only the artefact remains and the run is long
forgotten.

```
WARNING: VACUOUS: the hypotheses contradict each other, so this proof holds
for any goal. The minimal clash is: dens_high, kappa_small
```

A vacuous proof keeps saying it is vacuous. A sweep keeps saying what it did
not certify. A multiplicity keeps naming the lattice it is about. A bridge
keeps being named.

This is the half that ages. The verdict is easy to remember wrongly; the
warning is the thing that stops a bounded synthesis being cited as a theorem
two years later.

## Provenance

Every certificate carries the `certo` version that issued it and, when it came
from the CLI, the path and `sha256` of the spec. If the file changes later,
`verify` warns: the certificate is still valid on its own, but it no longer
corresponds to the file that is there now. `certo status` calls that **stale**
and lists it.

## Vacuity is checked, not assumed

`prove` succeeds when `hypotheses ∧ ¬goal` is unsatisfiable. If the hypotheses
are already unsatisfiable *by themselves*, that happens for **every** goal. The
proof is valid — anything follows from a contradiction — and it says nothing.

This is the most embarrassing way to be wrong and the easiest to miss, because
the output looks exactly like success. So it is checked on every successful
`prove`, `core`, `farkas` and `compose`.

```
$ certo prove vacuous.py
PROVED -- symbolic and universal under the hypotheses  [unsat]
  VACUOUS: the hypotheses contradict each other, so this goal -- and every
  other goal -- follows. The proof is valid and says nothing.
  The clash is: dens_high, kappa_small
```

The verdict does not change, because the verdict is not wrong. What changes is
that you are told, **and told which hypotheses clash**, minimally, so the next
question is already answered.

### Why this is the check a proof assistant cannot do for you

Lean will prove that theorem, report no `sorry`, and audit clean on
`#print axioms`. None of that tells you the hypotheses were satisfiable.

A user put it exactly right: `#print axioms` certifies *"I did not cheat"*. It
says nothing about *"this is not hollow"*. They had two Lean modules — no
`sorry`, axioms `[propext, Classical.choice, Quot.sound]`, everything a
formalisation is supposed to look like — and **both had an empty regime**. The
theorems were true, valid, and about nothing. Another line had produced four.

### Two details

* **It costs one extra solver call, on the successful path only**, and that
  call is on a strictly easier problem than the one just solved — the
  hypotheses without the goal.
* **In `farkas` it cannot be read off the multipliers.** A zero multiplier on
  the negated goal would suggest vacuity, but the LP is free to give that row a
  non-zero weight even when it is not needed, and usually does. So the question
  is asked directly: drop the goal row (and, in `--nonlinear` mode, every row
  derived from it) and search again.

In `compose` the check lands where it matters most. Two *derived* lemmas can
never contradict each other — both are true. Only **bridges** can, because a
bridge is asserted rather than derived, and two bridges that clash make the
whole theorem vacuous.

## Scope shows up on screen

A bare `PROVED` invites reading a bounded synthesis as a theorem. Each command
says which scope it is talking about:

```
CANDIDATE SYNTHESISED -- BOUNDED search
FINITE CASE VERIFIED -- not the theorem
FINITE SWEEP REPRODUCIBLE -- the predicate is NOT certified
PROVED -- symbolic and universal under the hypotheses
```

## Keeping them: `status` and `ledger`

[`certo status`](COMMANDS.md#certo-status) reads a directory and sorts it into
RESULTS, STILL OWED, HOLLOW and STALE. It emits no certificate, deliberately:
a report that certified itself would be the one artefact here that nobody had
checked.

[`certo ledger`](COMMANDS.md#certo-ledger) is the append-only log. It stores
paths and digests, never copies, so a tampered or missing certificate shows up
as a failure rather than being quietly duplicated into the log.

[`certo repro`](COMMANDS.md#certo-repro) bundles spec, certificates, versions
and hashes for a referee.
