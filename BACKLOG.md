# certo — backlog

One file, so nothing is tracked in three places. Priorities are **P0** (blocks
a release), **P1** (the next thing worth doing), **P2** (real value, more
work), **P3** (worth keeping, nobody is waiting), **Blocked**, **Won't do**.

Items marked *(user feedback)* come from an external user's report after real
use; those carry more weight than anything on this list that was invented in
the abstract.

Last updated: 2026-09-23, at **0.16.0**.

**This file went stale and it cost somebody a review.** A competent reader
worked through the repository at 0.10.0, found this list still saying "at
0.9.1", and recommended as their third priority a piece of work that had
shipped in 0.9.2 -- local toric data as a checker, measured against the T1
cells. They were right about everything they could check and wrong about this,
because the document that ranks the work was two releases behind the work.

That is the same failure as a README table nobody recomputes, on the one
surface where being wrong redirects effort rather than confusing a reader. The
rule this project applies everywhere else applies here: **an item leaves this
list in the same commit that ships it.**

It then went stale again one release later -- this file said 0.10.0 while the
tool said 0.11.0 -- which is the argument for the rule rather than against it.
Unlike the command tables, there is no test that can enforce it: what belongs
on a backlog is a judgement, and a judgement cannot be recomputed. It is the
one surface here still held together by remembering.

**And then by nine.** This file said 0.11.1 through the whole of 0.11.2 to
0.12.1 -- nine releases in three days, most of them fixing defects a user
reported, none of them touching the document that says what is worth doing
next. The rule was written here and broken here, by the largest margin yet,
which is worth recording rather than quietly correcting: a list of priorities
that is nine releases behind does not merely go unread, it redirects whoever
does read it.

The releases that caused it were reactive -- feedback arrived, a defect was
real, it shipped. That is the right order. What it does not excuse is leaving
the ranking untouched while the ground under it moved: three separate asks
were settled by work done for other reasons, and nobody noticed until this
was read end to end.

---


## Who calls certo, and what that changes

This was never written down here, and ranking without it has been wrong.

There are two consumers and they want different things. A **referee** brings
one finished argument and needs a single certificate to be airtight: value is
DEPTH on a fixed object. A **language model exploring** brings a route space
and needs many cheap conclusive answers to decide what to abandon: value is
BREADTH -- how much of that space certo can settle at all.

The second is the one this tool was built for, and the code says so where the
backlog never did. `status.py` opens by explaining why there are six result
states rather than three: *"an LLM that reads 'unknown' writes 'no solution
exists'; you have to distinguish why."* Six states, an MCP server exposing
every command, `out_of_theory` as a first-class verdict, a work budget, an
in-process API -- all of it is machinery for a caller that asks hundreds of
questions unattended and must be able to trust a negative. None of that is
referee machinery.

**What follows from it, and what does not.**

*Coverage stops being a nice-to-have.* Under the referee model, a domain certo
cannot touch is a gap in polish -- the referee simply checks that part by
hand. Under the explorer model it is a region of route space where the caller
goes back to guessing, which is the exact failure this project exists to
remove. A route certo cannot speak about is not neutral; it is a route that
gets pursued on a hunch.

*But breadth beats depth, and they are not the same ask.* One more KIND of
question that can be settled conclusively opens a new region. More power
inside a domain certo already reaches makes big instances tractable. For
discarding routes the first dominates, because **routes are usually killed by
a cheap fact, not a hard one** -- if settling it needs a serious computation,
the route was being pursued rather than discarded. That is an argument for the
rule this file already states, applied much harder: take the object as INPUT
and CHECK it. A checker over a new domain is S-M and opens the region; an
engine that computes the object is L and mostly serves depth.

*Discoverability is coverage.* Three asks this cycle were answered by
documentation rather than code -- the capability existed and could not be
found. For a human that is a papercut. For a caller that can only see what
`commands`, `what` and `dsl_guide` tell it, **a capability it cannot discover
has coverage zero**. Those surfaces are not docs, they are the coverage
surface, and they should be ranked as such.

*And the one thing coverage must never buy.* The moment certo returns
something that looks conclusive over a domain it half-supports, the explorer
model fails worse than with no coverage at all: the caller discards a live
route and never revisits it. A wrong `unsat` is not a bug here, it is the
whole edifice. New domains enter as checkers with an honest `out_of_theory`,
or they do not enter.

---

## What is open, in one screen

**Effort** is calibrated against work that actually landed here, not against a
feeling. **Confidence** is the part worth reading twice: an estimate made from
a specification rather than from an instance somebody measured has been wrong
every time this project checked one -- coset pruning, the canonical form, and
the shape of the corpus LPs all changed the moment they were measured.
**Radius** is what else moves if this lands.

| | Item | Effort | Confidence | Radius | Unblocks |
|---|---|---|---|---|---|
| **P1** | Branch and bound SPARSE end to end: the node's system, the model build and the exact check from non-zeros only | **M** | med | med | the 1048-column instance still does not finish in 20 minutes (90 nodes, ~13 s each): the matrix is still materialised densely per node. The certificate per node is gone already |
| **P1** | Bernstein subdivision with ONE DUAL PER LEAF, and the leaves aggregated into one statement | **M** | med | **high** | `subdivide` checks one dual on every leaf; a user's workflow is a dual per box, and joining them is the covering row below |
| **P2** | `box` together with `region`: multipliers for Bernstein coefficients | **M** | **low** | med | refused for now; the region's multipliers are found for the shift test on a ray |
| **P2** | `claim=` as a CONSTRAINT when certo finds the dual, not only checked afterwards | **S** | **high** | low | today the Bernstein LP minimises the bound and the claim is checked on what it found |
| **P2** | Covering a parameter domain: N boxes cover a semialgebraic set, and N parametric certificates aggregate into one statement | **L** | **low** | med | coverage is audited by a user's own script today, across SEVERAL coordinate charts. `CoverSpec` for parameter domains, with the charts as part of what is checked |
| **P2** | Cite a lemma the certificate cannot recompute, in `compose` | **M** | med | med | **unblocked**: it was waiting for a second instance, and a user's chain of bounds resting on an external section is it. `compose` already takes certificates as lemmas; what is missing is the cited one |
| **P2** | A `sweep` predicate certified in one line: a partition returned by the predicate, checked by `cover`, and `predicate_certified` set | **M** | med | med | a user covered the predicate with another tool because building the certificate by hand was too much |
| **P2** | Parametric certificates: size and verification time | **M** | **low** | med | ~6 MB of JSON per box, reported twice; `verify` about 5 s per box of ~3 600 control points in one report and minutes for one box in the other -- which one dominates needs the instance before sizing. Storing Bernstein coefficients instead of expanded polynomials may be most of it |
| **P2** | Choosing, on a degenerate LP, the optimal dual that maximises a given direction | **S-M** | med | low | the duals a solver's marginals give are not maximal |
| **P2** | Column generation beyond cliques: other implicit families, and a Farkas certificate for an infeasible partition | **L** | **low** | med | `columns` shipped for cliques; the pricing is the part that has to be exact for each family |
| **P2** | Certify the MAP: which clique a row is, which edge a capacity is | **M** | med | med | a perfectly certified LP that was badly translated leaves the original problem unproven. NOT the users' physical auditor — see below |
| **P2** | A certified integer UPPER bound for packings -- **re-measure first** | **L** | **low** | med | branch and bound became 40 to 60 times faster on a user's instances; it may already be the answer |
| **P2** | LP bounds to Lean: weak duality instantiated, closed by `linarith` | **S** | **high** | low | fits the export rule exactly. Trees are the row below |
| **P2** | Branch-and-bound trees to Lean; a small finite `sweep` to Lean by `decide` | **L** | **low** | med | two users asked. The risk is the scaffolding, which is what removed the last structured exporter |
| **P2** | Chvatal-Gomory cuts with their multipliers in the certificate; symmetry in branching; warm start | **L** | med | med | on small instances a node now costs ~30 ms; this is what is left of the throughput gap after the P1 row above |
| **P2** | The coverage map, read again once `why` has accumulated | **S** | **high** | low | the first reading found the instrument could not say which gap; it now records the message key |
| **P2** | Chow ring and toric intersection | **L** | **low** | none | route space, but depth-shaped: an engine, not a checker. See the breadth/depth split above |
| **P3** | Semialgebraic regions: polynomial multipliers (bounded Putinar), equality constraints, and boxes whose boundary is a curve | **L** | **low** | med | `region` multipliers are constants and products of pairs. A user's parameters live on a surface and needed three rational charts found by hand; boxes cut by a curve (`k1 = 0`, `x1 = 0`) end up left as frontier |
| **P3** | The minimum over a family of an arbitrary certified leaf -- an LP, an inertia, a count | **M-L** | **low** | med | `family` maximises over explicit LPs only |
| **P3** | Multi-capacity profiles: `profile` in more than one parameter | **M-L** | med | med | the regions and their duals, not only breakpoints |
| **P3** | A canonical form that scales, isomorphism in `enum`, and pynauty behind it | **L** | med | **high** | pynauty has no Windows wheel |
| **P3** | Rational SOS certificates on a lower-rank sub-face (rank reduction) | **L** | **low** | med | research-grade. Facial reduction was tried and rescued 0 of 5 -- see below |
| **P3** | Split `cli.py` and `spec.py` the way `certificate.py` was split | **M** | high | med | **demoted from P1**, see below |
| **P3** | Content-addressed certificate cache for `compose` / `status` | **M** | med | med | nobody has measured these as slow; it also adds a staleness surface |
| **P3** | `commands` / `what` / `dsl_guide` as a measured coverage surface | **S** | med | low | three asks this cycle were reachability, not capability |
| **P3** | `certo report`, phase 2: `--redact` that checks the bug survives, and a minimiser that shrinks the spec | **M** | med | low | phase 1 writes the folder and decides whose bug it is |
| **P3** | `certo report --submit`, opt-in | **S** | med | low | phase 1 sends nothing, deliberately |
| **P3** | PyNormaliz as a proposer for `semigroup --hilbert` | **S** | med | low | Linux-only, no Windows wheel; Normaliz computes, `check_hilbert` already decides. Optional backend like `geng` |
| **P3** | PySCIPOpt's exact mode and VIPR certificates | **M** | low | **high** | unverified that the wheel ships exact SCIP at all. Check that first, before sizing |
| **P3** | cypari2 / fpylll: number fields, primality, lattice reduction | **L** | low | med | no Windows wheels. A new domain for cypari2; fpylll proposes what `matrix` already checks |
| **P3** | `in_cone: false` with no separator is not re-checked by `verify` | **S** | med | low | only without cddlib, when Caratheodory exhausts and the subset search finds no separator. Redo it in the verifier or require the separator |

**Not planned: an adapter that runs another tool's operations inside certo.**
Asked for so that a second checker costs no start-up per call. It is a
reasonable thing to want and the wrong place to put it: certo's argument is
that nothing it reports rests on a tool it does not check, and a second
opinion is most useful when it shares nothing with the first. `certo.api`
already runs certo in-process for the reverse direction.

### Blocked, and on whom

Kept separate because "not done" and "cannot be done yet" are different facts,
and a list that mixes them makes the second look like neglect.

| Item | Waiting on | What unblocks it |
|---|---|---|
| The three quarantined payloads | a user | the files themselves. Three claims of certificates that verify and should not could not be reproduced; the reconstructions all came back INVALID, which means they differ from the originals |
| A resume protocol for `branch_frontier` | a decision nobody has stated | what is GUARANTEED when two partial runs are recombined. Emitting a frontier is not retaking one, and 0.12.1 deliberately stopped at the first |
| Recorded machine profiles for the `doctor` fixtures | access to varied machines | a Linux box, a venv, an editable install and a deliberately broken one. The code is S; what is missing is the machines, which is CI rather than a person |
| A required reviewer on the `pypi` environment | the repository owner | one setting. Nine versions have reached the index in three days with nobody approving the step, and a version on PyPI cannot be replaced |

**The coverage map, and why the row that shipped said *record* rather
than *map*.** *(the recording landed in 0.13.0; reading it is still open)*

The idea first: **every `out_of_theory` is a recorded instance of a question
certo was asked and could not settle** -- a route whose caller had to abandon
it or pursue it without help. Counting those by command and by domain turns
"which mathematics should certo cover next" from a judgement into a
measurement, which matters because the rows below were ranked from two users'
written reports, and this file has said for three releases that every estimate
made from a specification rather than an instance was wrong on contact.

**This item was itself written that way, and it was wrong on contact.** It
first went into this table as "a coverage map derived from the ledger, effort
S, the data is already on disk". Then somebody ran `wc -l` on the ledger:
**two lines, both conclusive.** The ledger is opt-in -- `--ledger` per run --
so nothing accumulates unless a person remembers a flag, and nobody does. The
instrument was assumed, not checked, in the row arguing for checking rather
than assuming. It is left here in full rather than quietly rewritten, because
this is the third time in one file that an estimate made from a specification
collapsed the moment an instance was looked at, and the pattern is worth more
than the embarrassment.

What survives is the precondition. Recording a non-conclusive verdict by
default -- command, status, the shape of what was asked, no payload -- is S,
and it is the only version of this that can start today. It has a real cost
the map did not: **writing to disk that the caller did not ask for.** That
needs an explicit opt-out, a bounded file, and nothing in it that a spec would
not already reveal. A tool whose whole argument is honesty does not get to
start logging quietly.

And it pays off later rather than now. Until it has run for a while, the
question "where is the coverage thin" still has no measured answer, which is
why the breadth-shaped P2 below it is the thing to build in the meantime
rather than after.

One caveat that will keep applying once data exists: this records only what
somebody thought to ask. A domain nobody attempted because it obviously would
not work leaves no trace, and that silence is the most expensive kind of gap.

**The budget that stops at z3.** *(the unbounded call was fixed in 0.13.0;
the rest of this still stands)* `Limits` carries a timeout, an rlimit and a
memory cap, and `apply_to` hands all three to a z3 solver. No other backend
reads any of them. Every subprocess certo runs carries a constant instead --
5 s for `git`, 20 s and 60 s in `doctor`, 900 s for `lake env lean` -- and
`graphs.enumerate_graphs` runs `geng` with **no timeout and no cap at all**,
buffering the whole of stdout, on an `n` the caller chose. At n=12 that is
more graphs than the machine has memory for, and the only thing that ends the
run is the operating system.

This is not a hypothetical: it is four lines of `grep` against the tree. What
makes it P1 is the gap between what the flag promises and what it does -- a
user who sets a budget and watches it be ignored has been told something
false, which is the one failure mode this project is supposed not to have.

**And it is worse for the caller this tool was built for.** A person watching
a run that will not end notices, gets bored, and presses Ctrl-C. A model
sweeping a route space unattended does not: it blocks on a question that was
supposed to cost ten seconds, and the exploration stops. An unenforced budget
is not only a dishonest flag, it is a throughput bug in the one workflow that
depends on asking many cheap questions and abandoning the expensive ones
quickly. Discarding a route requires being ABLE TO STOP.

Two shapes are worth separating: *honouring* `Limits` in the out-of-process
backends, and *bounding* the one call that honours nothing. The second is
small and can land alone.

**Facial reduction for `sos`, built, measured, and not shipped.** Clarabel
took `sos` from 6 to 26 of 30 random sums of squares. The four it misses are
sums of FEW squares with GENERIC coefficients, whose Gram matrices are all
singular. Facial reduction was the textbook answer and it rescued none of the
five cases it was built for, for two reasons worth keeping so nobody repeats
the attempt:

  * the minimal face containing EVERY Gram matrix is spanned by the
    polynomial's algebraic common zeros, so its projector is irrational and
    rational reconstruction cannot recover it;
  * where reconstruction did return an exact rational projector of the right
    rank, the reduced problem came back with a NEGATIVE margin -- infeasible.
    The acceptance test proved it was a face and not that it was the face.

The rational certificate exists -- `q1 q1^T + q2 q2^T`, rank 2 -- on a sub-face
of lower rank than the one the interior point sits in. Recovering it is rank
reduction toward a rational Gram matrix, which is a research problem and not an
engineering step. Two facts keep it at P3 rather than higher: the inequalities
people actually bring -- the ones with equality cases -- already certify, all
seven that were measured; and no wrong face produced a wrong certificate,
because the exact expansion that decides never changed.

**The doctor item that measuring dissolved.** This list carried "derived
expectations for the seams `doctor` reads, not hand-built fixtures", sized M,
on the strength of three tests that had agreed with a bug. Before paying for
it, the seams were instrumented -- which is cheap, and which this project has
started doing before believing itself.

The first instrument counted syscalls and said eleven of twenty-three tests
read the real machine. It was the wrong instrument: `Path.resolve` on a
directory the test just created is a real call that reads nothing of anybody's
machine. Counting only reads that LEAVE the fixture -- the same distinction
the `--repair --apply` near-miss was about -- said **eighteen of twenty-three
are hermetic**, and every one of the five that are not reads the real machine
deliberately, asserting properties that hold whatever it looks like.

So the item as written was aimed at a problem that 0.11.7 had already fixed
one test at a time. The historical defect was never "the test touched the real
machine"; it was "the test patched one seam while the code read another". What
was missing was something that notices a NEW test quietly joining the
non-hermetic group, and that is what shipped: a guard with a five-name
allowlist, each with a reason, that fails in both directions -- a test that
leaves its fixture without saying so, and a name whose reason no longer
describes anything.

**An M-sized refactor of the file with the subtlest bugs in the repository,
avoided by an afternoon of measurement.** Recording real machine profiles --
the other half of the original idea -- moves to Blocked: the code is S and the
obstacle is access to a Linux machine, a venv, an editable install and a
broken one, which is CI rather than anybody here.

**Certifying the map, and why NOT the whole auditor.** A group using 0.13.0
asked for native certificates of physical resources: cliques, loads,
partitions reconstructed from the graph, so that a repeated radial or a
non-existent clique is refused. The need is real -- certo accepts rows and has
no idea where they came from, and a perfectly certified LP that was badly
translated leaves the original problem unproven.

But they also wrote, in the same report, that their separate auditor imports
neither certo nor the generator nor NetworkX, and that **the two coverages
should be kept apart rather than added together**. Absorbing their auditor
into certo would delete the only check that does not share certo's
assumptions, which is precisely the check that has been catching things all
year. So the item is the narrow half: a declarative contract tying each row to
the clique it is, and each capacity to the edge it is, so certo can refuse a
translation error WITHOUT replacing the independent reconstruction. Agreed in
shape, not yet in detail.

**The half `opt --gap` leaves open.** *(still open)* A packing question has two sides. The
lower one is solved and exact: a feasible packing is its own witness, and
`opt` certifies it. The upper one -- *no packing does better than k* -- comes
today from the LP relaxation, which is a rational and usually not tight; when
the relaxation gives 5 and the answer is 4, certo can say "at most 5" and
nothing sharper. A user asked for a certified INTEGER upper bound on their own
instance and there is no honest way to give one yet.

Confidence is low deliberately. The obvious routes are a rounding argument
that needs a side condition certo cannot check in general, a counting argument
that is instance-specific, and exhausting the branch tree -- which is exactly
what `branch_frontier` now records the state of. That last one is the reason
this sits at P2 rather than P3: the machinery to say "these are all the
remaining cases" landed in 0.12.1, and an upper bound is what you get when
that list is empty. The item may turn out to be a report over work already
done rather than new mathematics. Nobody has measured it, which is why the
confidence column says so.

**Demoting the split.** It sat at P1 on the strength of one measurement: three
commands in 0.10.0 each touching seven files. That measurement still holds.
What changed is thirty-odd defects later, across 0.11.2 to 0.12.1, **not one
of them came from file size** -- they came from an absent field, a sign, a
comparison against an unresolved path, a text sort, a pointer nothing checked.
Hygiene is real and this is hygiene; it stops being P1 when the evidence says
the cost is being paid somewhere else.

### Shipped, and removed from this list

| Item | Where |
|---|---|
| Local toric geometry: cone, multiplicity, height, discrepancy | `certo cone`, **0.9.2** — measured against the T1 cells below |
| The transcription point between Lean data and a Python matrix | `certo.interchange`, **0.9.2** — canonical JSON with a fingerprint both sides recompute |
| Circularity detection in a parameter's own dependencies | `certo cycle`, **0.10.0** |
| Growth classes beyond polynomial | the ladder behind `cycle`, **0.10.0** |
| Exponent inference from relations | `order(relations=)`, **0.10.0** |
| The admissible range of a variable, not one witness | `certo range`, **0.10.0** |
| Certificate ↔ Lean declaration binding | `certo bind`, **0.10.0** |
| Overdetermination: compatibility of two definitions | already `eliminate`; documented in **0.10.0** |
| One derived table behind every documented count | `certo commands --table`, **0.11.0** |
| A spec mode that executes nothing | `--safe` / `CERTO_NO_EXEC`, **0.11.0** |
| `certo-math` on PyPI, import package unchanged | **0.11.0** |
| Trusted Publishing, with the tag checked against the version | `publish.yml`, **0.11.0** |
| `determinism` in CI, plus macOS and 3.13 | **0.11.0** |
| A job that tests the install carrying only z3 and pulp | `minimal`, **0.11.1** |
| A channel for a certificate that verifies and should not | `SECURITY.md`, **0.11.1** |
| `variable_range` refusing an unbounded end with no ray behind it | **0.11.2** — a certificate that verified and was wrong |
| The tier a command delivers, derived rather than hand-written | `routing.TIER`, **0.11.2** — the old set understated six commands |
| The exact simplex reachable when no rounded primal is | `exact.certify`, **0.11.3** — it sat inside the loop it was written to replace |
| An absent dual is not a zero dual | **0.11.3** |
| `opt` never writing a certificate its own verifier rejects | **0.11.3** |
| `bb` no longer reading "no certificate" as "empty subtree" | **0.11.3** |
| **An in-process API**: `run` / `runnable` / `options` | `certo.api`, **0.11.4** — 1.2 s of interpreter per question, gone |
| `lint` warning at the degree where `prove` falls off | **0.11.4** — measured at 11, not guessed |
| Minimisations reported in the sense they were asked | **0.11.4** — and `declared` in the payload |
| The generators in the lattice's own coordinates | `toric_cone.relative`, **0.11.5** |
| The fingerprint's residue convention, travelling with the recipe | **0.11.5** |
| Lean export for a Smith normal form | **0.11.5** — compiled against Mathlib before it was registered |
| `certo status --manifest`, with relations derived from content | **0.11.5** / **0.12.1** |
| `certo doctor --repair`, preview by default | **0.11.5** |
| A structural check on every Lean file certo emits | `check_emission`, **0.11.5** — the gate `run_lean.py` cannot be |
| `--gap` no longer reporting ZERO from a flag combination | **0.11.6** |
| `--target` compared rather than dropped, with `reached` | **0.11.6** |
| `certo what <command>` | **0.11.6** |
| `doctor` telling an install from a source tree from a leftover | **0.11.7** / **0.12.1** |
| A binding carrying the certificate it is about | **0.11.7** — it named a path and checked nothing |
| Integer labels ordered as integers | **0.12.0** — `10` sorted before `2` |
| **A stopped search leaving an artefact** | `branch_frontier`, **0.12.1** — the 48th kind |
| A nested sweep inheriting the spec it came from | **0.12.1** — one field, two symptoms |
| `--brief`: the certificate summarised in `--json` | **0.12.1** — 94 KB became 0.5 KB |
| `exists` answering the empty universe that `cover` certified | **0.12.1** |
| **`certo semigroup`**: affine semigroups as a CHECKER | `affine_semigroup`, **0.13.0** — the 49th kind. Refutes normality with a witness, never asserts it |
| A search whose bound is computed and travels with the answer | **0.13.0** — the grading turns "not in the semigroup" from a conjecture into a certificate |
| **The questions certo could not settle, recorded** | **0.13.0** — on by default, sizes only, `CERTO_NO_COVERAGE=1` to stop |
| An enumeration that could not run forever | **0.13.0** — `geng` had no clock and no memory cap at all |
| **`certo profile`**: a certificate whose subject is a FUNCTION | `capacity_profile`, **0.14.0** — the 50th kind. Bound + attainment + coverage is an equality on an interval |
| The forgery battery as a tool, and ONE implementation of it | `certo verify --tamper`, **0.14.0** — the adversarial suite now imports it |
| `verify` accepting the dict it serialises to | **0.14.0** — an adapter's `AttributeError` was certo's bug, not theirs |
| **An interior-point SDP behind `sos`** | Clarabel, **0.16.0** -- 26 of 30 random sums of squares against 6, and every tight inequality measured |
| What every verdict means, on one page, and `opt` naming `--prove-optimal` at a gap | `docs/VERDICTS.md`, **0.17.0** |
| Inertia and PSD in `matrix`, by congruence | `symmetric_inertia`, **0.17.0** -- the 51st kind; `inertia.signature` for loops, 3.5 ms at 20x20 |
| The budget reaching every backend a question runs | **0.17.0** -- `drat-trim`, Clarabel, `geng` and the Lean check, each with a flag |
| Branch and bound at a user's scale | **0.17.0** -- 47 s to 0.8 s on their K4: duals lost to PuLP's renaming, a dense exact check, a dense model build |
| The coverage log, read, and able to say which gap | **0.17.0** -- `why`, the message key, never its values |
| **`certo columns`**: an LP over every clique, without listing them | `clique_lp`, **0.17.0** -- the 50th command and 52nd kind; the pricing search is rerun by `verify` |
| `LPSpec` refusing a free or negative lower bound instead of reading it as 0 | **0.17.0** -- it had certified 0 for a program whose optimum was -5 |
| `doctor` recognising a user-site install; `--register-mcp --mcp-path` | **0.17.0** |
| Branch and bound without a certificate per node; `sweep` filters pushed into `geng`, edge ranges | **0.17.0** |
| The degenerate sizes: n=0 as the empty graph, vacuity named per size, `lint` below the swept n | **0.17.0** |
| Free variables in `LPSpec`; `==` rows, `free`, `claim=` and a primal witness in `ParametricSpec` | **0.17.0** |
| **`parametric` on a box**: Bernstein coefficients, subdivision, and the dual found by one exact LP | **0.17.0** |
| A GitHub Release per tag, from `publish.yml` | **0.15.0** -- the release job, and the ten missing ones created by hand |
| The project page stating its version and naming new commands | **0.15.0** -- tied to `__version__` by a test |
| **The facets of a cone behind `semigroup`** | pycddlib, `certo[polyhedra]`, **0.17.0** -- gradings for 140 of 140 pointed cones against 77, and `pointed: false` now needs a zero combination |
| **HiGHS for every continuous solve** | highspy in `numerics`, **0.17.0** -- 1.3 ms against 258 per LP; CBC kept for MILPs, where HiGHS measured slower |
| **gmpy2, measured and not adopted** | **0.17.0** -- `Fraction` is 2% of the examples' time; the one hot path was fixed by removing the arithmetic, 17.2 s to 0.29 s |
| **Transformation contracts**: equivalent / restriction / relaxation, and what travels | **0.15.0** — found 3 of 6 transformations losing fields silently |
| **Finding a profile**, not only checking one | `profile.discover`, **0.15.0** — exact, no sampling; the breakpoints come from two lines meeting |
| A guard that keeps the `doctor` tests hermetic | **0.15.0** — and the measurement that made the refactor unnecessary |
| `restricted()` keeping its loads, `relaxed`/`frozen` keeping what is theirs | **0.15.0** — a soundness defect a user reported, plus two found auditing for it |
| The smallest-set recipe, documented and exercised | `docs/CASES.md` + `examples/smallest_deletion.py`, **0.11.4** |

**Three items left this list without being worked on**, which is the part
worth noticing. A *colourability defect* command was asked for and is not
needed: `cases` with a counting constraint answers it, `bisect` sweeps it, and
the encoding is now documented -- the gap was discoverability, not capability.
A *certified frontier for weighted packings* turned out to need no packing
work at all, because the weights were already there and only the frontier was
missing. And *citing a fact* turned out to be unnecessary for the case that
prompted it, because the cone already recomputes what the citation would have
asserted.

**Modularisation moved to the top, and it is the first item here ranked from
a measurement of this repository rather than of a problem.** Adding `range`,
`cycle` and `bind` in 0.10.0 touched `spec.py`, `certificate.py`,
`engines/algebra.py`, `cli.py`, `routing.py`, `mcp_server.py` and two locale
catalogues -- for each of the three. Lifting the verifier registry out of
`verify()` removed one of those files from the list and gave the catalogue a
source; `cli.py` at 2.3k lines and `spec.py` at 1.5k are the two that remain.

The toric numbers below are what moved that item up in the first place, and
they are kept because they are what `cone` was built against --

| | rank | determinant | Smith |
|---|---|---|---|
| vertex cell | 4 | `16` | `[1,2,2,4]` |
| face cell | 4 | `−16` | `[1,2,2,4]` |
| all 16 together | 64 | `16^16 = 2^64` | — |

-- so the arithmetic underneath is measured, not guessed, and what is left is
the geometry that reads those numbers. That is a different and much better
starting point than the one this item had when it was written.

Released in 0.8.0, and struck from the table above: **certified symmetry
reduction** (`certo reduce`), **does this hypothesis earn its place**
(`certo audit`), and **exact integer linear algebra** (`certo matrix`). The
estimates held -- M, S and M -- and each of the three found a defect
underneath, which is now the expected rate rather than a surprise. See
*What landed in 0.8* below.

### The scale, with its anchors

| | Means | What landed at this size |
|---|---|---|
| **XS** | one sitting, reusing machinery that exists | `ratio` (reused the shift test), the version-drift check, `status` reading `.lean` files |
| **S** | one focused pass: module, engine, CLI, MCP, example, tests | `peak`, `exists`, `moment`, `entry`, the Tseitin bridge, typed transport |
| **M** | a pass plus a design decision, and usually a bug found underneath | `family` (a new verification model), `parametric` regions (found a simplex bug), the correspondence parser |
| **L** | several passes, or an algorithm that is a project of its own | the branch-and-bound retie (found a soundness hole); everything toric |
| **XL** | not attempted here | — |

### Two things the table is saying quietly

**Neither P1 is mathematics, and one of them is about mathematics.** The top
of the table is a measurement of what certo cannot settle, and a budget that
does not bind. Neither adds a theorem; both decide how much theorem-adding is
worth doing and in what order. It used to be: for several releases the
top of this table was exact integer linear algebra, then it was a refactor.
What sits there now is a flag that does not do what it says. That is not a
coincidence -- it is what nine releases of external feedback taught. Of the
defects fixed between 0.11.2 and 0.12.1, the overwhelming majority were of one
shape: **the tool said something that was not so.** A dual reported as zero
when there was none, a gap reported as zero when it was 3/2, a minimum
reported with the wrong sign, a binding naming a file it never opened, a
doctor reporting an install that was not there. None of them was a missing
capability. All of them were a promise the output made and the code did not
keep, and every one was found from outside.

The old first paragraph here argued that the cheapest P2 unblocks the
expensive ones, and pointed at exact integer linear algebra. That shipped as
`certo matrix` in 0.8 and the paragraph was still making the case for it nine
releases later, which is the staleness this file is about.

**The toric items can be made much smaller, by the rule this project already
follows.** A Hilbert basis is genuinely hard to COMPUTE -- Normaliz exists for
a reason -- and much easier to CHECK: that each generator lies in the cone,
that none is a sum of others, and that together they generate. Taken as INPUT
and verified, the same way `parametric` takes a dual and `labelling` takes a
permutation, that item drops from L to S-M and stops being a research project.
Computing it is somebody else's job and always was.

That is also why their confidence is low as written: they are specified from a
report rather than measured against an instance, and every estimate this
project made that way changed on contact.

---

## What landed in 0.9

### `reduce --parametric` — the symbolic quotient *(was P1, user feedback)*

Estimated **M / med-high / low radius**, and it landed at that size. The
estimate held for the reason the backlog said it would: both halves existed.

**The risk resolved in the easy direction.** The open question was whether the
orbit COUNT varies with the parameter, which would have needed either a stated
range or a refusal. Measured against three write-ups: it does not — 2, 3 and 4
orbits, fixed. What varies is the ROW SET, because a triangle type that does
not exist contributes no constraint. So the feature is built around row
existence conditions, and the regimes those conditions cut parameter space into
are derived rather than declared.

**One thing measuring did change.** An orbit is present exactly where its
multiplicity is positive, not wherever it is declared: the split family has two
edge orbits for `q >= 1` and one for `q = 0`. Declaring "two orbits" and
meaning it everywhere is how a degenerate case gets a constraint it has no
right to.

Five ways of mis-stating a family are refuted on the window, the tightest being
a single condition dropped: `3x >= 1` carried into `p = 2` fails at 7 of 35
points. The Lean export splits the same way the certificate does — the
multiplicity identity as a theorem `ring` closes, the window as examples
`norm_num` closes, and one `sorry` on the step from the window to the region.

---

## What landed in 0.8

### Domain obligations in `audit` *(defect reported against 0.8)*

Reported by a user within a day of 0.8. Division is total in SMT, so dropping
a hypothesis that guards a denominator produced an instant counterexample at
`d = 0` and the hypothesis read `needed` for a reason about the solver rather
than the theorem. Worse than reported: the witnesses also carried Z3's
internal `div0`/`mod0`, which nothing could re-apply, so on any spec
containing a division `audit` emitted a certificate that did **not verify at
all**.

Divisors are now collected up front, every search is guarded by them, and a
fourth verdict `domain` names the obligation a hypothesis was carrying. The
distinction between `domain` and `redundant` is asked, not read off the shape
of the formula.

### `certo reduce` — certified symmetry reduction *(was P1 #1)*

"Averaging over the automorphism group, an optimal solution may be assumed
constant on each orbit" was a bridge under five shipped examples. Its three
hypotheses are finite checks given a generating set, and now they are checked:
the action permutes the variables, the constraint set is invariant, the
objective is invariant. A generator that fails one is refused BY NAME, because
a wrong group does not give a weaker reduction, it gives a wrong one. The
quotient is rebuilt during verification rather than believed.

K7 triangle cover under S7: 35 variables to 1 orbit, 21 rows to 1, optimum 7
both ways. `examples/symmetry_reduction.py`.

### `certo audit` — does this hypothesis earn its place *(was P1 #2)*

Drop each hypothesis in turn and hunt a counterexample to what remains. One
satisfiability query per hypothesis, three verdicts, and `unknown` is never
folded into the other two. Every `needed` carries the assignment that breaks
it, so re-checking is evaluation rather than search.

On `examples/amgm.py` it found a hypothesis nobody suspected doing no work.
It does NOT claim minimality -- hypotheses are dropped one at a time, and a
pair can be jointly redundant with neither redundant alone -- and `verify`
says so every time, because claiming it would be the overstatement this
command exists to catch.

### `certo matrix` — exact integer linear algebra *(was P2 #1)*

rank, determinant, Hermite and Smith over Z, with the unimodular transforms
carried alongside their INVERSES, so checking is integer multiplication and
not a second elimination. `rows`/`cols` select a submatrix, which is how a
minor is asked for. The sign of the determinant is settled by one determinant
modulo an odd prime -- exact, because `U . U_inv = I` had already narrowed it
to two candidates.

This was the cheapest P2 and it unblocks the two below: the semigroup and
Chow-ring items are built on exactly this arithmetic.

---

## P2 — the substrate two routes share

### 1. Affine semigroups and local toric charts

Saturation, normality, Hilbert bases, the interior of a cone, the Gorenstein
criterion; unimodular cones of height one, SNC divisors, multiplicity and
discrepancy. The second user's highest-return item, and finite exact integer
work throughout. The arithmetic it needs landed with `certo matrix`.

**Effort L as written, S-M taken as input** -- and the second is the version
this project should build. A Hilbert basis is genuinely hard to COMPUTE;
Normaliz exists for a reason. It is much easier to CHECK: each generator lies
in the cone, none is a sum of the others, and together they generate. Take it
as INPUT and verify it, the way `parametric` takes a dual and `labelling`
takes a permutation, and this stops being a research project.

Saturation, normality and the Gorenstein criterion are the same shape: hard to
decide from nothing, cheap to check given the witness a dedicated tool already
produces.

CONFIDENCE IS LOW either way, and that is the part to weigh. This is specified
from a report rather than measured against an instance, and every estimate
made that way in this project changed on contact -- coset pruning looked like
the answer to the canonical form until the number was computed, and the corpus
LPs turned out to be the opposite shape to the one the command was built for.
Before building, get one real cone out of the route that wants it and measure
what actually blocks.


### 2. Chow ring and toric intersection

From rays, cones and linear relations: the presentation, Stanley-Reisner
relations, monomial reduction, intersection numbers, Chern classes. Needs the item
above; the integer arithmetic under both landed with `certo matrix`.

### 3. A canonical form that scales, on its own

Unchanged and unasked-for by anyone. The measurement that blocks it stands: a
1-factorisation of K6 has 15 points and one refinement class, `15!` is
1,307,674,368,000, `|Aut|` is 120, so quotienting by the whole group leaves
10,897,286,400 cosets. `labelling=` removed the pressure by taking the
labelling as input.

---

## P3 — later, or waiting on the above

| | What | Effort | Why it is down here |
|---|---|---|---|
| | Structured ring isomorphisms | **L** | Explicit maps, identity compositions, compatibility with localisation, grading and group actions. Wants the typed transport (landed) to be extended past `compose` first -- without it there is no notion of "the same object" to certify. |
| | Finite group actions | **M** | Invariants, stabilisers, fixed loci, quotient rings. Finite and exact, and downstream of the semigroup work. |
| | Finite homological algebra | **L** | Free complexes, exactness, resolutions, Ext, Tor, dimensions. Mechanical and large; nobody is blocked on it today. |
| | Jacobian criterion certificates | **S-M** | Smoothness, local dimension, singular locus, transversality via exact Jacobian ideals. `ideal` is the machinery; this is the interface. |
| | Batyrev engine, canonical form transport | **XL** | Both are geometric theorem application, which by the stated boundary is Lean's job. certo's part is the finite premises those theorems consume. |
| | Small geometric counterexample generation | **S** | The second user's request, and a special case of P1 #2 applied to fans, cones and semigroups. Follows it. |
| | `export --check` progress | **XS** | A papercut from the first user. The metadata half landed in 0.9.1. |
| | Flag algebras | **L** | Still wants 2-3 real instances to be designed around a problem. |
| | Lean statements for the sweep kinds | **L** | Graphs and set families are not mechanical. Deliberately parked. |
| | `certo qe`, Gomory-Chvatal cuts | **M** each | Distinctive, nobody waiting. |

---

## The boundary, stated

**certo is not a second Lean**, and should not try to become one. Its part is
to find and certify finite, explicit, checkable data; Lean's part is to verify
that data, apply the structural theorem, and carry the geometry. A user on the
toric route put it as a pipeline and it is the clearest statement of the
division this project has:

    certo finds and certifies the data
      -> Lean verifies the certificate
      -> Lean applies the geometric theorem
      -> Lean identifies the model

Everything in P2 is chosen to feed that first arrow. Nothing in it is an
attempt at the last three.

**What that statement left out is who is holding the pipeline.** It says where
certo stops and Lean starts, which is a division of labour between two tools,
and it silently assumes the thing between them is a person assembling a final
argument. Usually it is not. Usually it is a model deciding whether this
pipeline is worth entering at all -- and that decision is made long before any
certificate reaches Lean, on the strength of answers that cost seconds.

So the boundary has a second half, which belongs next to the first:

    a model proposes a route
      -> certo settles what it can, conclusively, cheaply
      -> the route is abandoned, or it earns the pipeline above

The first arrow of the Lean pipeline is what a SURVIVING route needs. Most
routes do not survive, and the work certo does for those is the work that
never appears in a paper and saves the most time. Ranking by what the final
certificate needs systematically undervalues it, which is what this file has
been doing.

---

## What changed the ranking, again

Reordered 2026-09-17, after reports from two users on two different routes and
one measurement of my own. They agree in a way none of them could see alone.

**A Lean export that compiles, has no `sorry`, and says nothing.** A user
exporting an `unsat_core` over a theory certo cannot render in Mathlib got

    theorem from_core : True := by trivial

with the real statement carried verbatim in a comment above it. The comment is
honest. The artefact is not: it passes a build, it passes a `sorry` audit, it
passes `#print axioms`. The user declined to put it in their formal chain,
which was right, and which means the safeguard that worked was a person
reading carefully -- exactly the safeguard this project exists to replace.

certo already has the word for this. `status` reports HOLLOW for a vacuous
proof. Not applying it to certo's own output is the same inconsistency as a
certificate its own verifier rejects, and it is now P0.

**"The biggest risk is not in the calculations."** A second user, on a toric
geometry route, named it directly: the danger is silently moving from a
computational object to the paper's object. They asked for a TYPED TRANSPORT
GRAPH -- every certificate declares which object it speaks about (cone,
monoid, ring, spectrum, model) and every step between levels carries an
explicit map.

**And it is already load-bearing here.** Five examples written this week start
from a symmetrised program -- "averaging over the automorphism group, an
optimal cover may be assumed constant on each edge orbit" -- and certo
certifies everything downstream of that sentence and nothing about it. The
averaging argument has three hypotheses, all of them finite checks given
generators: the action permutes the variables, the constraint set is
invariant, the objective is invariant.

Three observations, one item. The calculations were never the weak part.

**What both users want that is the same substrate.** One asked for exact
determinants, rank, minors, Smith and Hermite normal forms, polytopes and
fans. The other asked for affine semigroups, toric charts and a Chow ring.
The second is built on the first. That makes exact integer linear algebra the
highest-value MATHEMATICAL item, because it is the only one two routes share.

**And the boundary, which one of them stated better than this file did:**
certo should not become a second Lean. It produces finite, explicit,
verifiable certificates; Lean proves the structural theorems and does the
geometric transport. That is now the stated policy rather than an implication.

### Reordered again 2026-09-21, after nine releases

Not one report, this time: five, across four days, from a user running certo
against real work. What they changed about the ranking is less about any
single item than about where ranking information comes from.

**Every significant defect was found by something outside the code that
produced it.** A user hitting it, a derived table disagreeing with a
hand-written one, an engine's own verifier rejecting what the engine wrote, a
Lean compiler refusing a file. Not once by the code reviewing itself.

**Three tests were found agreeing with the bug rather than catching it.** Two
patched one seam while the code under test read another, so they passed
against a machine that was broken. One fixture was built from the same wrong
assumption as the defect -- it put scripts where the bug thought they were --
so it confirmed the bug and reported success. This is the sharpest thing this
cycle produced and it generalises: a test written by whoever wrote the code,
reading the seam that code reads, cannot be relied on to disagree with it.
The countermeasure that has worked here is not more tests, it is **derived
expectations** -- the catalogue, `_declared_against_emitted` -- where the
thing being compared against is computed from a different source. That is now
a P2 item in its own right rather than a habit.

**Three asks were settled without building what was asked for.** A command, a
primitive and a mechanism were each requested, and each turned out to be a
documentation gap, an adjacent feature, or already true. Worth remembering
before the next ask is priced: the first question is whether the thing is
missing or merely unreachable.

**The premise the ranking rested on was never checked.** Every ordering in
this file, from the first version to this one, implicitly ranked by what a
careful REVIEWER of a finished argument would want. The owner named the other
consumer -- a model testing and discarding routes fast, on objective results
-- and the code has said so since `status.py` was written, in the comment that
explains why there are six result states. A backlog can be stale about
versions, which this one has been three times; it can also be stale about who
the work is for, which is worse, because nothing in the repository contradicts
it visibly. That is the correction that produced the section at the top and
the coverage map at P1.

**The one new item came from reading another project, not from a user.** The
bounded-subprocess pattern now at P1 was found by looking at how a neighbouring
tool runs untrusted work, and then checking certo's own tree against it. That
is a cheap source of items and this list had never used it.

---

## Done

| | What landed | Notes |
|---|---|---|
| ✅ | `certo compose` | Lemmas + their certificates into one proof, with the **link** between each lemma and what its certificate closes checked. Bridges are declared and reported every verification. |
| ✅ | `certo bounds` | Rigorous enclosures via Arb / `mpmath.iv`; exact-rational intervals; precision as the work budget; Python floats refused. |
| ✅ | Vacuity detection | `prove`, `core`, `farkas`, `compose`. The verdict stays PROVED; the flag travels in the certificate so `verify` repeats it later. |
| ✅ | **Sweep levels: certified / reproducible / recorded** *(user feedback P0)* | Banner, counters and warnings say what a sweep established about its **predicate**, on PASS and REFUTED alike. |
| ✅ | **Verdict vector + replay verification** *(user feedback P0)* | One code per evaluation plus a digest; `verify` re-runs the predicate and names the first item that disagrees. |
| ✅ | **Honest counters** *(user feedback P0)* | `predicate_uncertified` used to read 0 on every passing sweep however many evaluations went unchecked. |
| ✅ | **Symmetries for `DomainSpec`** *(user feedback P1)* | `canonicalize=` reports labelled count, orbit count and a representative per orbit — for the **counterexamples**, which is the question. `verify` checks the decomposition adds up. |
| ✅ | **Standard reducers** *(user feedback P1)* | `reduce="auto" / "sets" / "sequences" / "decrement" / "graphs" / "masks"`. `auto` refuses on a type it does not know rather than inventing a reduction. |
| ✅ | **`certo doctor`** *(user feedback P1)* | Capabilities present and missing, each with **what happens without it**, plus `--register-mcp` (merges, never replaces) and a real start check. |
| ✅ | **`g6` → `id` in the payload** *(user feedback P1)* | A `DomainSpec` used to label triples of sets "graph6". Readers still accept `g6`, so earlier certificates verify. |
| ✅ | `load_spec` runs the bytes it hashed | Was reading stale `__pycache__` bytecode for a spec edited within the same second to the same length — which would have silently defeated replay verification. |
| ✅ | A spec can import a sibling file *(user feedback)* | `load_spec` puts the spec's directory on `sys.path`, the way Python does for a script. |
| ✅ | MCP `verify` returns its warnings | It was dropping them entirely — and the warnings are the whole honesty layer. |
| ✅ | MCP stamps provenance | Certificates produced over MCP carried no spec path, so they could not be replayed or found by `ledger verify`. |
| ✅ | `Path("")` is `.` | `shrink_graph` and `shrink_domain` verification died with a permission error instead of saying the certificate recorded no spec path. |
| ✅ | **Native combinatorial types** *(user feedback P2)* | `SetFamily` — hypergraphs, designs, codes, mask systems. Supplies `key()`, `canonical()` and `reductions()` itself, so a `DomainSpec` over one leaves all three at `"auto"`. The canonical form is exact and **raises** rather than falling back to an invariant that could merge two orbits. |
| ✅ | **`certo induct`** *(P2)* | Base cases + step, with the join checked: no gap in `k0..base_upto`, and the step starting no later than the base ends. Z3 has no induction schema; the principle is applied here and said so on every verification. |
| ✅ | **Symmetries on graph sweeps** *(P2)* | `SweepSpec(canonicalize=...)`, for a symmetry finer than isomorphism. `"auto"` asks the item for its own canonical form. |
| ✅ | **`sweep --by-orbit`** *(P1)* | Evaluate one item per orbit. Sound only under an invariance nothing can prove, so it is named in the certificate AND spot-checked against real non-representatives; a predicate that is not invariant stops the run by name. |
| ✅ | **`sweep --witnesses`** *(user feedback P1)* | The structural story end to end: N labelled → K orbits → a minimal witness per orbit, in one certificate that verifies they came from the same run. |
| ✅ | **`certo ideal`** *(0.3.0)* | Gröbner cofactors: `1 = Σ hᵢgᵢ` refutes a polynomial system, `f = Σ hᵢgᵢ` certifies what follows. Buchberger with the transformation tracked, so the cofactors are in the user's own generators. Decides, so a negative answer is conclusive. |
| ✅ | **`certo sos`** *(0.3.0)* | Sums of squares: numeric search by alternating projections, exact rounding, exact LDLᵀ. Retracts this project's own earlier argument that SDP-based certificates could not be citable — the answer was `opt`'s all along. |
| ✅ | **`certo order`** *(user feedback)* | The exponent of a parameter once magnitudes are substituted. Asks what `prove` cannot: a Θ(1) term is not infeasible, so a solver says "satisfiable" forever while the bound never improves. Found four bugs in a user's session before it existed. |
| ✅ | **Branch and bound with certified leaves** *(0.4, P1)* | `mixed --prove-optimal`. Every leaf closed by an exact dual, a Farkas ray, or a fully-fixed residual LP; the tree checked to COVER the integer domain. Turned `ν = 7` from a design into the proved optimum on the research instance, in 73 nodes. |
| ✅ | **`farkas_ray`: LP infeasibility with a certificate** *(0.4)* | `y >= 0`, `A^T y >= 0`, `b.y < 0`. Three dot products, no solver. |
| ✅ | **`PackingSpec.lists` and `opt --gap`** *(0.4, P1)* | The shape 51 of 131 corpus scripts share, in three lines; and `mu* - nu` as one exact rational with both sides certified and checked to be the same packing. |
| ✅ | **`--by-orbit` for graph sweeps** *(0.4, P1)* | Both sweep payloads are now symmetric, which is what made it urgent before the freeze. |
| ✅ | **`examples/WALKTHROUGH.md`** *(0.4)* | One problem, end to end. |
| ✅ | **MILP levels named, `--freeze`, `opt --target`, per-kind packing integrality** *(user feedback, 2nd round)* | The taxonomy the user asked for — feasible / conditional_optimum / global_optimum — plus taking the skeleton from their own solver, certifying a target rather than an optimum, and whole-or-fractional per item kind. |
| ✅ | **`S**4` was refused as a non-constant exponent** *(user feedback)* | With a REAL base z3 makes the exponent a rational literal; `is_int_value` said no. The sort was never the question. |
| ✅ | **`certo mixed`** *(user feedback)* | Per-variable kinds, and the search-then-certify flow a user was running by hand. Certifies the construction, the exact residual dual, and the link between them; states plainly that it does not claim MILP optimality. Throws in the relaxation bound, which certifies global optimality for free when the two meet. |
| ✅ | **`certo number`** *(0.3.0)* | Pratt primality trees and factorisations. Checked by modular exponentiation alone. |
| ✅ | **A refutation showed the verdict and hid the counterexample** | The values were in the certificate and nowhere on screen, so refuting a claim meant opening a JSON file to find out WHAT refuted it — and the counterexample is the answer, not the "no". `prove`, `check` and `check --hypotheses-only` now print it. |
| ✅ | **`certo repro`** *(P1)* | Spec, certificates, versions, hashes and ledger in one directory a referee checks with nothing but certo. Nothing invalid goes in, and nothing untied goes in quietly — a bundle that silently shipped a different spec would be the worst failure available. Measured on a real directory: 132 certificates, 5 refused with reasons, 6 named as untied, and the bundle re-verified end to end. |
| ✅ | **Adversarial verification tests** *(P1)* | Every kind, every payload field mutated, and a mutation that flips no check is the finding. Three real holes: a Pratt tree never tied to the number it claimed (2³¹−1 relabelled as 2³¹ verified), an `lp_dual` accepting a primal one entry short because `zip` truncates in silence, and an `unsat_core` with multipliers never reading its own `core_smt2`. Exclusions are named with reasons, in two categories — descriptive, and weakening, since a smaller true claim is not a forgery. |
| ✅ | **`verify --spec` and `certo --version`** *(user feedback P1)* | Refuse unless the file is the one the certificate was made from, by hash; and print version, commit and the newest schema this build writes. |
| ✅ | **`cover --optimize` and `CoverSpec.to_lp`** *(user feedback P1)* | Three numbers with their statuses attached: your cover as a certified upper bound, the relaxation as an exact rational lower bound, and the integer optimum when branch and bound finishes. `candidates` required and refused rather than guessed, because minimal-relative-to-what is a modelling fact. Built for a misreading: a valid cover reported as an optimal one. |
| ✅ | **An exact rational simplex** | Surfaced by the above. Deriving a degenerate dual by choosing which tight rows carry weight is C(49,7) on a realistic exact cover, about 10^8 — right for a handful of tight rows and hopeless past it. Past that the dual is solved outright, two-phase, Bland's rule, no floats. The motivating instance came back `exact: False` and is certified now. |
| ✅ | **`certo order` shipped and nobody found it** *(user feedback P1)* | Not a missing feature: a discovery failure, which is worse, because the work was done and did not reach anyone. `asymptotics` and `decays` as aliases, a help line that leads with "does this DECAY in n", `certo commands` putting the question-to-command table in the terminal, and a `lint` note that names the command when a claim divides by a product of symbols. The last has a narrow trigger — two or more symbols at negative exponent — and fires zero times across the shipped examples. |
| ✅ | **A `mixed_design` certificate its own verifier rejected** *(user feedback P0)* | Any model with a `>=` or `==` row: `as_leq_system` renames and negates those, and the equivalence check looked up the original name in a table keyed by the normalised ones. Reported as "all variables discrete"; the empty residual was incidental and the blast radius was every quota model. The mapping now lives in `normalised_rows` and both consumers use it. |
| ✅ | **`--self-check`** *(user feedback P0)* | The real verifier, run over what was just produced: by default for solver-free certificates, opt-in otherwise. A failure exits non-zero and says it is certo's bug. This is the fix for the class — 339 tests missed both defects because every one fed verification a certificate the producer had built, so both sides were wrong in the same place. |
| ✅ | **`parametric` for cover programs** | `sense="min"` with `>=` rows, bounding from BELOW out of a feasible packing, and dual entries that may be polynomials because a cover's dual grows with the instance. Forced by three separate write-ups of one argument, all of which reduce to a symmetrised cover over edge orbits and all of which state the value as a minimum of named closed forms. Two branches of a two-orbit program and one branch of a four-orbit program are now certificates; each is EXACT against an exact rational simplex on its branch (49 and 343 points). The branch conditions come out as the dual's own feasibility. |
| ✅ | **`certo exists`: non-existence, with a refutation** *(P1)* | certo could exhibit a cover and not say "none exists". A paper in the corpus states two obstructions -- divisible graphs with no triangle decomposition -- and the honest artefact for a finite non-existence is a refutation, not an absence. The CDCL and DRAT machinery was already here with no way to reach it from a combinatorial question; this is the bridge. Two answers, both certificates: a model is a SUGGESTION whose parts go through `cover`'s own counting verifier, and a refutation is a DRAT proof checked by unit propagation. Both obstructions verify, and the encoder is not vacuously unsatisfiable -- K7 and K9 come back with decompositions. `--max-parts` found that pairwise "at most k of n" is C(n, k+1): 6,724,520 clauses at 35 candidates and a cap of 6, now 667 with a sequential counter. |
| ✅ | **`certo family`: the largest of many LPs** *(P2)* | From a script in the corpus: enumerate every bipartition, solve one LP each in floats, take the largest, re-solve just that one exactly. That confirms the winner and leaves the claim unmade -- "no bipartition does better" is about all 16,384 of them. Two claims and they are not symmetric: the winner is ATTAINED by a primal and dual that meet, every other item is BOUNDED by a feasible dual, and a dual does not have to be optimal to bound. Nothing stores an LP; each is rebuilt from the spec, so a dual for a different item does not fit and `verify` needs the spec and fails loudly without it. |
| ✅ | **`certo ratio`: a fraction inequality for every n** *(P3)* | `(n-2)/n^2 <= 1/n` for n >= 2 and its cousins, which `prove` settles with an unsat core that re-checks by running a solver again. Clearing the denominators makes it the shift test, and the step that can go wrong -- clearing them -- is the step that gets checked: a denominator not shown positive is a refusal, because a negative one flips the inequality and makes the certificate backwards. `>=` is not offered, being the same claim with the sides swapped. |
| ✅ | **`certo moment`: the first moment, exactly** *(P3)* | The probabilistic method in one line, and the line is a sum of rationals -- usually done in floating point, where `0.9999999` and `1.0000001` have both been written down as "less than one". Two shapes: by event (linearity, no independence needed) and by tail (masses as successive differences, which is the shape the active corpus work states). The existence conclusion is drawn only when the quantity is declared a COUNT, and `verify` re-earns that rather than believing the flag. |
| ✅ | **`certo entry`: the first crossing, and its window** *(P3)* | A proof walks a finite path and stops at the first index past a line. The claim that goes wrong is not "it crosses" but "it had not crossed yet". The prefix is the whole evidence -- nothing past the crossing is part of either claim, so the tail never travels. A step bound buys the WINDOW: the step before was on the near side, so the crossing overshoots by at most delta. |
| ✅ | **Typed transport: a level cannot be crossed silently** *(user feedback P1)* | Two users on two different routes reported the same risk from opposite ends, and one named it exactly: silently passing from a computational object to the paper's object. `compose` already checked the LINK between a lemma and what its certificate closes; what was missing was the OBJECT. A lemma now declares `subject=(kind, id)` and, when that differs from the theorem's, must name a `transport`. An unnamed crossing is REFUSED. certo does not check the map -- that is Lean's part and the boundary this project keeps -- but every crossing is recorded and repeated on each verification, the way bridges are. Declaring no subjects keeps the old behaviour exactly, because a proof that never mentions objects has no levels to cross. |
| ✅ | **Integer arithmetic exports to a theorem `omega` closes** *(user feedback P1)* | The exporter emitted ℤ binders and then handed the goal to `linarith` -- which reasons over ordered FIELDS, so `2x >= 1 implies x >= 1` is beyond it -- or, with no Farkas multipliers, to `sorry`. The second is the common case in combinatorics: a core over the integers exported as a hole even when the statement was DECIDABLE. Linear integer arithmetic is Presburger without quantifiers, `omega` decides it, and it needs no multipliers because it is not searching for a combination. Non-linear integer rows keep the old route, because `omega` does not do variable times variable and a tactic call that fails looks the same to a reader as a gap. And the footer no longer claims a `sorry` the file does not have -- the same lie as a hollow theorem, in the other direction. |
| ✅ | **Propositional logic reaches a DRAT proof** *(user question)* | An asymmetry, once it was named: `prove` DECIDES logic -- disjunctions, implications, quantifiers, booleans mixed with arithmetic -- and its `unsat_core` re-checks by running a solver again. `cases` refutes a CNF with a DRAT proof that re-checks by unit propagation and nothing else, and was reachable only by writing clauses by hand. So anything with an `Or` in it fell back to trusting z3 twice. `to_cnf` is the standard bridge, Tseitin, with the honest parts said out loud: EQUISATISFIABLE and not equivalent, `prove=True` encodes the NEGATION so the verdict reads backwards and the meaning is printed beside it, and the auxiliaries are dropped from the reported witness. Arithmetic inside a formula is REFUSED rather than encoded as an atom -- a CNF whose refutation says nothing about the arithmetic is a wrong answer wearing a proof. Checked against z3 on 60 random formulas for satisfiability, validity, and every model substituted back. |
| ✅ | **The exported theorem is compared against the certificate** *(user feedback P0)* | Nothing compared them. The exporter reads a certificate and writes Lean, and a bug anywhere in that path -- a dropped hypothesis, a sign, a coefficient, a goal rendered from the wrong row -- produces a theorem that COMPILES, looks right, and is not the one the certificate supports. It is the failure this project has already had twice in the other direction: producer and verifier wrong in the same place, agreeing with each other. So the check does not ask the exporter what it meant: it PARSES THE EMITTED TEXT BACK and compares, by a different route. Comparison is semantic, because `-a < 0` and `a > 0` are one row and the exporter writes hypotheses one way and the goal the other on purpose. Four mangles caught, each naming what changed rather than pooling into one boolean. The parser covers only the grammar certo emits and REFUSES the rest, because one that guessed would quietly approve a statement it misread. |
| ✅ | **A hollow Lean export says it is hollow** *(user feedback P0)* | A user exporting an `unsat_core` over a theory certo cannot render got `theorem from_core : True := by trivial` -- compiles, no `sorry`, passes `#print axioms`, states nothing. They declined to put it in their formal chain, which means the safeguard that worked was a person reading carefully. Three changes: a placeholder closes with **`sorry`** rather than `trivial`, so every audit a formalisation project already runs sees it; its name carries `_HOLLOW`, so it is not cited by accident; and `export --check` reports **HOLLOW** and exits non-zero instead of OK, because compiling was never the question. The manifest records the count per file. The route that WORKS -- linear arithmetic over the reals, with real binders and a positively stated goal -- is unmarked, which is what keeps the signal worth anything. |
| ✅ | **A dedup you can check: `labelling=`** *(P2)* | `canonicalize` hands over a FORM and asks to be believed, so "these forty are the same object" was the spec's claim and a certificate could only check that the decomposition's arithmetic held together. `labelling` hands over the PERMUTATION: certo applies it, the result is the canonical form, and the permutation travels so anyone can re-apply it. The claim becomes an arithmetic fact. No cap, because nothing is searched -- the instance that motivated the whole item, a vertex-transitive object certo's own canonical form refuses outright, deduplicates 40 labelled copies to 1 orbit with 40 witnesses, all re-applied on verification. What it still does NOT show -- that two DIFFERENT representatives are different objects -- is a warning rather than an implication. Declaring both is refused: one asks to be believed, the other to be checked. |
| ✅ | **A `SetFamily` id was ambiguous past ten points** | Found by the above, when the witness decoder refused to round-trip. `key` juxtaposed point numbers, which is unambiguous only while a point is one digit: on fifteen points `{1,2,13}` and `{12,13}` both read as `1213`, so two DIFFERENT families shared an id and `from_key` returned a third family. The id is the dedup key and what lands in a certificate. Ids separate their points above ten now and are byte-identical at or below it, which is every id any stored certificate contains. |
| ✅ | **A branch-and-bound tree tied to its own problem** *(user feedback P1)* | The item was compression and a `--fully-checkable` mode. Measuring it found something else first: a node's dual was a whole nested certificate checked ON ITS OWN TERMS, and a dual for a node's relaxation is a valid dual for SOME linear program with nothing saying which node. Exchanging two node certificates verified -- so an expensive subtree could be closed by a cheap one's, and "no design does better", the strongest thing certo says, was not established. Each node's program is DERIVED now, from a root system carried once and the node's own fixings, by the same function the producer uses. The compression and the mode came free: node data fell from ~33,654 bytes to 880 on a 98-row instance, ~150-176 bytes per node on branching trees, and `solver_free` is COMPUTED and comes back true -- every node closes by exact rational arithmetic. Certificates written before the root system existed still verify, with a warning naming exactly what they do not establish. `branch_bound` was also missing from the adversarial suite entirely, which is how the hole survived; it is in it now, and nested sub-certificates are mutated in their payload rather than their schema number. |
| ✅ | **`certo peak`** *(P1)* | The best INTEGER choice for a family of concave quadratics. A write-up completes the square, says the objective is an integer at integer argument, and concludes the maximum is the FLOOR of the continuous peak -- and the floor of a parametric expression is not a polynomial, so there is nothing to expand. Moving the origin to the claimed maximiser makes it polynomial: an integer step changes the objective by `A t^2 + q'(x*) t`, non-positive for every non-zero integer `t` exactly when `A <= q'(x*) <= -A`. Two inequalities, checked by shift, no floor and no residue inside the certificate. The bound is ATTAINED because `x*` is an integer, so a non-integral maximiser is refused rather than assumed integral. Residue classes are separate specs, the way branches are. Matches brute force on three classes for every n < 180. |
| ✅ | **`parametric` past the box: `region=`** *(P1)* | The shift proves non-negativity on a ray, so a certificate covers a BOX -- and a branch cut out by `q d + d r = d(d-1) + r(r-1)` is not one. Side conditions are now DECLARED: `g(p) >= 0` enters the certificate's scope, nothing proves it, and `verify` warns separately and loudly because a polynomial condition reads like something proved. certo finds the MULTIPLIERS, since that search is a linear program -- polynomial ones, because the multiplier of a condition is `r/2` as often as it is a number. A trichotomy that two boxes covered 68% of now takes five certificates and covers 1170 of 1170 measured points, every bound exact against the simplex. |
| ✅ | **The exact simplex could return a `y` violating its own constraints** | Found by the above, silently. Dependent rows -- one per monomial of a polynomial identity, so dependent by construction -- end phase 1 with an artificial basic at level zero, and the transition renamed it to variable index 0, which is a real variable. That states a false tableau; the answer came back wrong or as a spurious "unbounded". Artificials are now pivoted out on a real column, and a row with no real column left is dropped as redundant. Not a soundness hole anywhere it was used -- every caller re-checks what the simplex hands back -- but it was losing answers and would have gone on doing it. |
| ✅ | **A named square is a legitimate hint** | `farkas --nonlinear` searches a fixed square set -- each hypothesis squared, `x²`, `(x-y)²` -- and a margin estimate that completes the square as `(2s-q)²` or `12(u-v/4)²` is outside it, so the heuristic missed and said so. It did not need a feature: a square is a tautology, so assuming one adds a row without adding an assumption. Three comparisons from one write-up now close solver-free, with multipliers `1/16` and `1/48` that are the source's own arithmetic read back. Documented, because the mechanism existed and nobody could have guessed it. |
| ✅ | **A `>=` load priced at zero** *(user feedback P1)* | Same root cause, other consumer. Now `d(optimum)/d(bound)`, summed over the normalised rows with their signs — negative for a binding `>=`, because raising a floor costs you — with the direction stated and the source rows in the payload. |
| ✅ | **Minimisation in branch and bound** *(user feedback P1)* | Refusing it left the user negating by hand and their certificate describing a formulation nobody posed. The tree still searches `max -c.x` because that is what happens, and the payload records both what was searched and what was asked. |
| ✅ | **`--wall-timeout-ms`, and a stopped search that reports** *(user feedback P1)* | `--timeout-ms` bounds a solver call, not the search. On expiry by clock or nodes: best design, best bound, gap, node count, and no certificate of optimality. A search that runs out always knew all four. |
| ✅ | **A solver's stop reason, in words** *(user feedback)* | z3 says "canceled", which reads as if the user cancelled it. Now named as the limit it was, with the lever to raise and a hint about dividing out a common power — which in the report turned a 10 s timeout into 12 ms. |
| ✅ | **`certo cover`: exact covers and clique partitions** | Every element of a universe in exactly one part, checked by counting; with `cliques=True` the parts are vertex sets and each is refused unless every pair among them is an edge. Three failures reported as three different things, because a non-clique part is a statement about the graph and a doubled edge is one about the cover. An upper bound with an artefact attached: pair it with `opt`'s exact dual for the lower one. |
| ✅ | **Local loads in a packing certificate** *(user feedback P1)* | Named regions with bounds, declared apart from resource capacities because a capacity is part of the encoding and a load is part of the argument. They become rows, so the dual prices them: a binding region reports its shadow price, a slack one reports that it is not what constrains the answer. The certificate carries each load's coefficients so `verify` recomputes the achieved value rather than believing it. Built to the shape of the corpus model, `within-A load <= N_A`. |
| ✅ | **`certo parametric`: a bound for every parameter value** *(P1)* | Weak duality, symbolically: `y >= 0` with `A(p)ᵀy >= c(p)` bounds `opt(p)` for every `p` at once, and each dual-feasibility row is certified on a ray by substituting `p = p0 + u` and reading the coefficient signs. Turns "checked for p = 5..12" into "holds for every p >= 10". Built against the corpus instance whose duals are piecewise constant with thresholds; on a reproduced slice one dual read at p = 10 gives the EXACT optimum at 10, 11, 15 and 30. The shift is sufficient and not necessary, so a failure emits no certificate and says the route failed rather than that the bound is false. |
| ✅ | **`certo eliminate`: resultants** *(P2)* | Removes a variable from two polynomials and returns the condition on the rest, with the Bezout identity `Res = A*f + B*g` attached — so checking a determinant over a polynomial ring is expanding two products. Bareiss throughout, every division verified exact rather than assumed. A non-zero constant resultant refutes a common root over any field; `Res = 0` is necessary always and sufficient only over an algebraically closed field with a non-vanishing leading coefficient, which `verify` repeats and qualifies. |
| ✅ | **Derive the LP dual instead of reconstructing it** *(user feedback P1)* | 3 of 56 exact LPs needed the rational pair injected by hand, all on symmetric solutions: on a degenerate vertex CBC returns an arbitrary one of many optimal duals and rounding it need not be dual-feasible. Complementary slackness determines the dual from the primal in exact `Fraction`, and where it underdetermines it the choices ARE the optimal duals. Certifies now with no usable dual from the solver at all. The second cause this item claimed — a coupled denominator ladder — was **measured and refuted**; that pass was dropped rather than shipped. |
| ✅ | **A solver-free certificate for linear-arithmetic proofs** *(user feedback P1)* | An `unsat_core` meant re-running z3 to check it. Now the Farkas search runs over the core's own rows and the multipliers travel as optional fields: verification expands the combination in `Fraction` and reads off the contradiction. Floats in the search do not compromise it — the LP finds the vector, exact arithmetic accepts or rejects it. Fell out of it: the Lean export emits `linarith` instead of `sorry`, so the two gaps this user reported separately had one fix. |
| ✅ | **`check --hypotheses-only`** *(user feedback)* | Asking "is my regime non-empty?" by claiming `False` returned UNSATISFIABLE on regimes that have models -- correct, and the opposite of what it reads as. The flag asks it directly: a solver-free model when the regime is inhabited, the minimal clash when it is not. A constant claim is named in `check` and in `lint` for whoever does not know the flag exists. |
| ✅ | **`export --lean` for `unsat_core`** *(user feedback)* | The kind the most-used command produces used to be refused. Linear arithmetic gets real binders, hypotheses and a positively stated goal with `sorry`; a vacuous core becomes `h₁ → … → False`, the emptiness of the regime stated in Lean. The sort is read off the formulas. Everything else carries the SMT-LIB2 and says so. |
| ✅ | **`--check` had never compiled anything** | A relative path against a cwd inside the Lean project; lake reported "no such file or directory" and it surfaced as a compile failure. Found because the lean CI job, fixed in the same round, finally got far enough to run it. |
| ✅ | **A fractional "integral point" verified as valid** *(user feedback)* | `_verify_lp_dual` checked the declared integral point for feasibility and for matching its objective, and never that the values were integers: `x = 3/2` passed. Now checked per DECLARED KIND, so a mixed problem's continuous weights stay fractional on purpose. `mixed_design` had it right all along; `lp_dual`, which `opt` produces, did not. |
| ✅ | **`certo status`** *(P1)* | Reads a directory of certificates and reports where the work stands: RESULTS (nothing else builds on them), STILL OWED (every bridge and unclaimed optimality, including ones three levels down), HOLLOW (vacuous proofs with their clash named, sweeps that certified nothing), STALE (the spec moved under the certificate). Emits no certificate of its own: it makes no claim. |
| ✅ | **`certo lint`** *(P1)* | The dry pass before the compute. Contradictory hypotheses found BEFORE the proof rather than after a valid-and-empty win; an inductive step that starts after the base cases end, caught by comparing two integers instead of discharging six sweeps; a `bool` predicate named as `reproducible` in advance. Counts a domain without materialising it and reads a graph family's size from a table. |
| ✅ | **Deep Lean export** *(user feedback P1)* | A Farkas certificate becomes a runnable `linarith`/`nlinarith` example carrying the `sq_nonneg` hints it used; a `compose` proof becomes a skeleton with `sorry` on exactly the bridges; a sweep becomes a `List` Lean can `decide`. Plus `--manifest` (hashes) and `--check`, which compiles. All three verified against Mathlib v4.28.0. |

---

## Decisions taken

Recorded so they do not get re-litigated, and so the priorities below can be
read as following from something.

| | Decision | Consequence |
|---|---|---|
| **PyPI** | ~~Not yet. Revisit at a stable version.~~ **Superseded.** | Was: installation stays `git clone` + `pip install -e`, no release workflow to maintain. Revisited and reversed: certo ships as `certo-math` via Trusted Publishing, and the release workflow described at the foot of this file is the thing that was being avoided here. Kept rather than deleted because the reason it was deferred -- keeping payload changes cheap -- is the same reason the schema freeze now matters. |
| **Who this is for** | The primary caller is a model exploring, not a person refereeing. | Stated 2026-09-21, after nine releases of ranking as though it were the other way. Drives the coverage section at the top of this file; see also `status.py`, which has assumed it since it was written. |
| **Certificate schema** | **Frozen from 0.4**, once that version closes. | Until 0.4 ships, payload fields may still move (readers keep accepting the old shapes). From 0.4 a payload change needs a schema bump and a migration note. Anything produced for a paper before then should be re-run after 0.4. |
| **Lean** | Deeper Lean is **not the focus**. certo helps establish the mathematics; a separate tool generates and compiles the Lean. | P1 "Lean statements, not only structure" drops to P3. What stays is the export as it is -- data, `linarith` examples with their hints, and the theorem/bridge boundary -- because those are the *mathematical* content, not a formalisation. Revisit if the handoff turns out to lose something. |
| **Admin rights** | Not available on this machine, and not coming. | `cadical` / `kissat` moves from Blocked to Closed. The built-in CDCL is the answer: correct, and slow. `certo doctor` says so in one line. |
| **Real instances** | Supplied by a user, from their own working corpus. | See below -- one instance has already been used, and it found a bug. |

---

## What the first real instance found

The research corpus is dominated by one computational shape: **51 of 131
scripts build an LP or ILP over a family of lists with exact rationals.** A
"list" is a set of colours; the packing puts a pair `{a,b}` from list `j` into
a solution, each pair usable once globally and each `(list, colour)` once. That
is a `PackingSpec` exactly, and the quantities computed are the integral
optimum `ν` and the fractional `μ*` -- the integrality gap.

Rebuilt as a certo packing, the canonical core instance reproduces their
numbers: `ν = 7`, `μ* = 15/2`. Two differences worth having: `μ*` comes out as
an **exact rational** rather than the float `7.5`, and the dual verifies
without a solver, reading as a load per resource.

**And it found a bug.** `opt` on an ILP reported the relaxation's value as
`meta["objective"]` -- so `ν = 7` came back as `15/2`. The detail text was
half-honest about it; every programmatic reader was not. Fixed in a way that
is better than the original intent: an ILP now certifies **both sides** -- a
feasible integral point, rounded and checked exactly, as the achievable value,
and the exact dual as the bound. When they coincide the integer optimum is
certified exactly; when they do not, the gap is reported rather than hidden.

That is the argument for real instances in one paragraph, and it is why the
items below still say "build against a real problem".


### A note on the README

Rewritten twice on 2026-09-17, for two different reasons, and the second one
is the interesting one.

The first pass replaced an abstract opening with three real sessions. The
second replaced those, because all three showed the SAME PHASE of the tool:
catch a false claim, catch a vacuous one, hand over an artefact. The tagline
said "certo tries to break it", which is a mode and not a summary. Nothing on
the front page showed it FINDING anything, measuring how much a thing fails
rather than whether, or collapsing ninety counterexamples into the two objects
they actually are.

It now leads with **the arc** — find, break, measure, reduce, establish,
assemble — as a table, and then one session per phase. The through-line is the
last column of that table rather than the verb in the tagline: every phase
returns something re-checkable, and that is the claim worth making.

Worth recording as a lesson rather than a changelog entry: a front page
written by whoever built the tool will over-represent whatever they worked on
most recently. Three sessions all drawn from the honesty layer looked like
coverage and were not.

Every block of output on both front pages is copied from a run. Two were wrong
when first checked, including one claiming a `branch_bound` certificate
verifies *without* a solver. It does not.


## Closed

**`cadical` / `kissat`.** No Windows wheel, no binaries in cadical's releases,
kissat on macOS and Linux only, no C++ compiler, and WSL needs administrator
rights that are not available on this machine and are not coming. Decided
rather than blocked: the built-in CDCL is the answer. It is correct and it is
slow, `certo doctor` says so in one line, and CI now runs the suite on Linux
where an external solver could be installed if anyone ever needs one.

---

## Won't do

**Chasing an adjacent library's coverage.** Measured 2026-09-17: 1175 modules
against 28 commands, with whole areas — topology, probability, analysis,
groups, lattices, finite fields — where certo has no analogue and no reason to
grow one. Trying would lose, and the attempt would produce a thousand commands
with no certificate.

The rule that falls out, and that has already been applied twice: **do not
build a search here because a certificate needs one.** `cover` takes a
partition, `parametric` takes a dual, `farkas` finds its own multipliers only
because that search was an LP already in the box. What another tool computes,
certo certifies and archives — and certo has no 32-variable cap because it is
not a service with a request quota.

One correction to how that is applied, from the same reading: **look at the
catalogue before building in the overlap.** `cover` would have shipped anyway,
since the persisted certificate and the pairing with a lower bound are the
point, but the plain check already existed and knowing that would have started
the work at the pairing, which is the half that fixed a real misreading.

---

The one long-standing entry that used to be here was flag algebras and
SDP, refused on the grounds that floating point cannot produce a citable
certificate. `certo sos` (0.3.0) shows that argument was wrong: the same
round-and-re-verify-exactly move that `opt` has always used applies, and the
floats stay in the search. Flag algebras are now a P2 item rather than a
refusal — still wanting 2–3 real packing instances before anyone builds it,
but for reasons of demand, not of principle.

---

## Release process

Releases are authorised by the project owner, one at a time. Work lands in
local commits; **pushing to the public repository is not automatic** and is
asked for each time. Each release bumps the version, writes its section of
[CHANGELOG.md](CHANGELOG.md), and is tagged.

Current: **0.12.1**, with **48 certificate kinds**. The certificate schema
has been **frozen** since 0.4.0 and `SCHEMA_VERSION` is still 4: everything
since has been a new kind, an optional field, or a command that emits no
certificate. The optional fields added under the freeze so far are `loads`,
`declared` and `relative`.

Frozen means an existing payload's fields do not move: no renames, no
removals, no changes of meaning. What stays allowed, permanently:

* a NEW certificate kind — additive, breaks nothing;
* an OPTIONAL field on an existing payload that older readers may ignore.

Anything else needs a `SCHEMA_VERSION` bump and a migration note. Every item
left below is of the first kind, which is why none of them is urgent.

### What a release is, beyond the index

Publishing to PyPI is not the whole of shipping, and treating it as such left
**ten tags with no GitHub Release** -- every version from 0.11.1 to 0.13.0.
`publish.yml` runs guard -> tests -> build -> publish and stops. Nothing wrote
a release note, so the repository's own front door still advertises 0.11.0.

The project page is the other half and behaves differently: GitHub Pages
builds it automatically from `main`/`docs`, so its COUNTS are always right --
a derived test enforces them. What it does not do is name anything. The live
page mentions no command added since 0.10, because the test checks the number
and nothing checks the content. A number nobody recomputes was the failure
this project started with; this is its mirror, a number recomputed beside
prose nobody does.

So a release is four things, and only the first is automated:

  1. the tag, guarded against `__version__` and the CHANGELOG, then PyPI;
  2. a GitHub Release carrying that version's CHANGELOG section;
  3. `docs/index.html` saying what is new, not only how much there is;
  4. the installed copy on the maintainer's machine, so `doctor` agrees.

### The gate, and the hole in it

Publication runs through Trusted Publishing in `publish.yml`: `guard` (the tag
and `__version__` and the CHANGELOG entry must agree) -> `tests` -> `build` ->
`publish`. No token is held anywhere, by anyone, and the guard has refused a
release for disagreeing with itself, which is the job.

**What it does not have is a human.** The `pypi` GitHub environment has no
required reviewer, so the last step runs as soon as the tag lands. Nine
versions reached the index in three days that way. Every one was authorised by
the owner in conversation first -- the practice held -- but the practice is the
only thing holding it, and a version on PyPI cannot be replaced, only yanked.
That is the same shape as everything else on this list: a safeguard that
works because somebody remembers. It is one setting, and only the repository
owner can change it.
