# certo

**Between having a mathematical idea and having a proof of it there is a lot
of work that is not proving.** certo does that work — find the object, break
the claims that are false, measure what survives, reduce it to what it really
is, and assemble the rest — and every step comes back with a **certificate
anyone can re-check without trusting certo.**

CLI and MCP. Fifty-four commands. Runs in milliseconds where a formalisation
costs hours.

*Español: [README.es.md](README.es.md) · run any command with `--lang es`.*

| | |
|---|---|
| **[Project page →](https://jtraverso.github.io/certo-math/)** | the didactic introduction: what certo is for, in one page, in both languages |
| **[Commands](docs/COMMANDS.md)** | all fifty-four, one entry each: the question, the spec, the certificate, and what it does not establish |
| **[Specs](docs/SPECS.md)** | the DSL: every spec type with a minimal working example, shared options, exit codes |
| **[Certificates](docs/CERTIFICATES.md)** | why they are the centre, the fifty-three kinds, which re-check without a solver |
| **[Worked cases](docs/CASES.md)** | real problems end to end: symmetry, sweeps, parametric bounds, packings, toric data |
| **[What a result means](docs/VERDICTS.md)** | status against verdict, the four optimisation claims that look alike, `false` against `null`, exit codes |
| **[Limits](docs/LIMITS.md)** | what it does not do, and the FAQ |
| **[Walkthrough](examples/WALKTHROUGH.md)** | one problem, seven commands, fifteen seconds |

---

## What it is

The lab instrument: find a contradiction fast, learn which hypotheses are
redundant, exhaustively validate a finite case, bracket a constant with a
certificate, synthesise a candidate over a bounded domain.

It is **not** a proof assistant — that is Lean, Rocq or Isabelle — nor a
computer algebra catalogue. [What it does not do](docs/LIMITS.md) matters as
much as the command list.

The division of labour, in a user's words after a real session: certo finds
and certifies the small trades; the human proof explains why they assemble
globally without double-counting.

| Phase | What you ask | What comes back |
|---|---|---|
| **Find** | Is there an object like this? What is the best one? | the object itself — and with `mixed --prove-optimal`, a proof that it *is* the best |
| **Break** | Is this claim actually true? | a counterexample **with concrete values**, in milliseconds |
| **Measure** | Not *whether* it fails — how much, and where is it worst? | exact min, max and mean, and the extreme instances by name |
| **Reduce** | Ninety counterexamples. How many objects is that really? | orbits under your symmetry, and one minimal witness per orbit |
| **Establish** | Is it true for every case, every `n`, exactly? | DRAT proofs, induction with the chain checked, Farkas multipliers, Gröbner cofactors, sums of squares, rigorous enclosures |
| **Assemble** | What does my whole project rest on, and what do I still owe? | the proof with every **bridge named**, and a report of what is still assumed |

A verdict you cannot re-check is a rumour. Everything here produces an
artefact, and most of them check without a solver at all.

## Install

Requires Python 3.11+.

```bash
pip install "certo-math[mcp,numerics]"
```

The import package and the commands are `certo`, not `certo-math`:
`from certo import Spec`, `certo prove spec.py`. Only the distribution
carries the longer name, because `certo` alone is a crowded word.

From a checkout instead:

```bash
git clone https://github.com/jtraverso/certo-math
cd certo-math
pip install -e ".[mcp,numerics]"
```

Dependencies: `z3-solver` and `pulp`, both of which ship their binaries. The
extras are `mcp` for the MCP server and `numerics` for `bounds` and `sos`
(`python-flint`, `mpmath`, `numpy`, `clarabel` and `highspy`); without them you
get the CLI, minus rigorous numerics and sums of squares, and LPs solved by
starting CBC rather than by HiGHS in-process. `polyhedra` (`pycddlib`)
makes `semigroup` decide with the facets of the cone instead of searching; it
has wheels only for Windows, and elsewhere builds against cddlib and GMP.

Check it works:

```bash
certo doctor
```

Optional tools, none installed automatically and none needed to start:

| Tool | What for | Without it |
|---|---|---|
| [`nauty`](https://pallini.di.uniroma1.it/) (`geng` on `PATH`) | enumerating graphs | Python engine, comfortable to n=8 |
| `cadical` or `kissat` | `cases` on large instances | our own CDCL, correct but slow |
| `drat-trim` | second opinion on DRAT proofs | the built-in Python checker suffices |
| `python-flint` (Arb) | `bounds` with special functions | `mpmath.iv`, for the elementary ones |
| `numpy` | the Gram search behind `sos` | **nothing** — `sos` cannot run without it |

`certo doctor` says which of these you have and **what each gap costs**, which
is the part a checklist of red crosses leaves out.

## Two minutes in

```bash
certo core examples/amgm.py
```

```
PROVED -- symbolic and universal under the hypotheses  [unsat]
  hypotheses needed: a_pos, b_pos, c_pos | redundant: noise
```

Every file in [`examples/`](examples/) carries in its docstring what it does
and what to expect. Lost? `certo commands` prints the routing table below in
your terminal, in your language.

## The three cross-cutting rules

1. **Every command returns a certificate, or says explicitly why not.**
   Never a bare "yes".
2. **Six result states:** `unsat`, `sat`, `unknown_solver`, `timeout`,
   `resource_exhausted`, `out_of_theory`. Only the first two are conclusive.
   The other four all mean "no answer", but for different reasons, and
   collapsing them is expensive: an LLM that reads "unknown" writes "no
   solution exists".
3. **Determinism by work budget, not by clock:** `rlimit` in Z3 and
   `conflict_budget` in SAT. *This covers our engines, not your predicate:* if
   your `sweep` predicate calls scipy or CBC, that part is outside the
   guarantee.

## If you are an LLM being asked to use this

1. Read [`docs/SPECS.md`](docs/SPECS.md), or call the `dsl_guide` MCP tool,
   before writing a spec.
2. Find the command by the **question**, not the name:
   [`docs/COMMANDS.md`](docs/COMMANDS.md), or `certo commands`.
3. Run [`certo lint`](docs/COMMANDS.md#certo-lint) on every spec before
   running it. It is the cheapest thing in the tool and it catches the
   contradictory regime, the empty family and the 10⁹ domain.
4. Read the verdict, not the exit status. `unknown_solver` is **not**
   "does not exist".
5. Certificates are written to disk and do not travel in an MCP response.
   Call `verify` with the path you are given.
6. Running more than a handful of questions? Use the
   [in-process API](#in-process-api), not a loop over the CLI: the startup
   dominates, and a fallback written to avoid it is a fallback in floating
   point.

## The fifty-four commands

Grouped as [`certo commands`](docs/COMMANDS.md) groups them. Full entries,
with what each one does **not** establish, in
[`docs/COMMANDS.md`](docs/COMMANDS.md).

| Command | What it does | Engine | Certificate |
|---|---|---|---|
| `prove` | Negate the claim, look for `unsat` | Z3 | unsat core, or counterexample |
| `check` | Satisfiability; `--hypotheses-only` asks if the regime is non-empty | Z3 | model, or core |
| `core` | MUS: which hypotheses are needed | Z3 | minimal core |
| `audit` | Does every hypothesis earn its place, or is the theorem overstated? | Z3 | **verdict per hypothesis, each with the assignment that breaks it** |
| `farkas` | `linarith` / `nlinarith`, with the multipliers | exact LP | **Farkas certificate**, solver-free |
| `compose` | Assemble lemmas into one proof, checking the join | Z3 | **proof**: every lemma, its certificate, and the link |
| `induct` | Base cases + a step, and the check that the chain joins | Z3 | **induction**: both halves, and the two numbers that matter |
| `synth` | CEGIS: ∃obj ∀input ∃aux | CEGIS/Z3 | object + the counterexamples that forced it |
| `opt` | LP/ILP, or a packing | CBC | **dual in exact rationals** = the load certificate |
| `mixed` | A discrete skeleton searched, the continuous part certified | CBC + exact LP | **mixed design**: assignment, exact dual, and a bound |
| `order` | The exponent of `n` once magnitudes are substituted: decays, or Θ(1)? | exact Laurent | **the exponent**, solver-free |
| `bounds` | A numeric inequality, rigorously (`e`, `log`, `π`, `ζ`) | Arb or mpmath | **enclosure in exact rationals** |
| `ideal` | Polynomial systems: refute them, or certify what follows | Gröbner, ours | **cofactors**, checked by expanding |
| `eliminate` | Remove a variable from two polynomials; keep the condition on the rest | Sylvester + Bareiss | **Res = A·f + B·g**, solver-free |
| `parametric` | A bound for EVERY value of a parameter, from a dual you already have | weak duality, symbolic | **y and the shifted residuals**, solver-free |
| `peak` | The best INTEGER choice for a family of concave quadratics, and the value there | exact, no search | **the maximiser and two step inequalities**, solver-free |
| `reduce` | "By symmetry": the three hypotheses of the averaging argument, checked | exact, no search | **generators, orbits and the quotient**, solver-free |
| `matrix` | Exact integer linear algebra: rank, determinant, Hermite and Smith | unimodular transforms | **U, V and their inverses**, checked by multiplication, solver-free |
| `solve` | `A x = b` exactly, over ℚ or ℤ | exact elimination, Smith | **the solution and the system**, one product to check; an obstruction when there is none |
| `quotient` | A partition of a program, and the equivalence it induces | exact counting | **the class data and both regularities**, solver-free |
| `cone` | Local toric data: primitivity, multiplicity, the height functional, discrepancies | exact det and solve | **the numbers two geometric theorems consume**, solver-free |
| `columns` | An LP over every clique of a graph, without listing the cliques: column generation with a pricing search the verifier reruns | exact rational arithmetic | solver-free |
| `atlas` | A parameter domain covered by boxes, each certified by `parametric`, and ONE statement for the whole | every piece re-verified, the covering recomputed cell by cell | **names the uncovered sliver**, solver-free |
| `semigroup` | Affine semigroups as a checker: pointedness, minimality, and membership of the cone, the group and the semigroup | exact integer and rational arithmetic | **refutes normality with a witness, never asserts it**, solver-free |
| `profile` | How an optimum responds to ONE capacity across an interval: a piecewise-affine function, not a value | exact rational arithmetic | **decides `f` on its domain** — bound, attainment and coverage — solver-free |
| `family` | The largest of ten thousand linear programs, and why nothing beats it | exact LP | **the winner and a dual for the rest**, solver-free |
| `ratio` | A fraction inequality for EVERY n | exact polynomials | **the cleared numerator and the sign of the denominator**, solver-free |
| `moment` | Is the expected number of bad events below one, so a good object exists? | exact rationals | **the moment and the mass it leaves over**, solver-free |
| `entry` | Where a sequence first crosses a line, and by how little | exact rationals | **the prefix and the two terms that bracket it**, solver-free |
| `exists` | Does one exist at all, and the refutation when it does not | own CDCL | model, or DRAT proof |
| `cover` | Is this an exact cover? A clique partition is one case | counting | **the universe and the parts**, solver-free |
| `sos` | A polynomial is non-negative, as a sum of squares | numeric + exact rounding | **rational squares**, solver-free |
| `number` | Primality, or a factorisation | Pratt | **modular-exponentiation tree** |
| `cases` | SAT with a verified DRAT proof | own CDCL or external binary | DRAT proof |
| `enum` | Non-isomorphic graphs with filters | nauty or Python | canonical list + hash |
| `sweep` | Predicate and/or value over a family or ANY finite domain | nauty or Python | family **+ predicate certificates** |
| `shrink` | Minimise a counterexample (graph or MUS) | CDCL / reduction | minimality witness |
| `bisect` | A constant's threshold | prove or cases | the pair that brackets it |
| `range` | The admissible interval of one variable over the regime, not one point of it | exact LP dual | **a Farkas combination at each end**, solver-free |
| `cycle` | A parameter that depends on itself: compose the growth classes and close the loop | growth ladder | **the chain, its classes and the one comparison**, solver-free |
| `bind` | Tie a certificate to the Lean declaration meant to justify it, and check it does | Z3 entailment | **the hypothesis, the statement, and whether one covers the other** |
| `lint` | Check a spec before spending the compute on it | — | — |
| `status` | Where a proof stands: proved, owed, hollow, stale | — | — |
| `doctor` | What this install can do, and what each gap costs | — | — |
| `report` | Whose bug is it -- certo's, the spec's or the machine's -- and a local folder to file it with. Sends nothing | — | — |
| `ask` | One entry point: load a spec and run whatever it asks for (`what` is the same command) | — | whatever the command produces |
| `commands` | Which command answers which question | — | — |
| `repro` | Bundle spec, certificates, versions and hashes for a referee | — | the bundle |
| `promote` | Run an `--explore` again, certified, and say whether the two agree | re-run certified | the certificate of the certified run |
| `pack` | Thousands of certificates into one zip with a manifest, each member readable alone | — | the archive; `verify` checks every member |
| `mcp` | Which certo MCP servers are running old code after a reinstall; `restart --yes` stops them | — | — |
| `verify` | Re-verify a stored certificate | — | — |
| `export` | Spec to SMT-LIB2/DIMACS, or a linear Farkas certificate to Lean | — | — |
| `ledger` | Audit log of what was run | — | — |

Common options, **after** the subcommand: `--json`, `--cert FILE`, `--lang`,
`--timeout-ms`, `--rlimit`, `--max-memory-mb`, `--seed`.

Exit codes: `0` conclusive, `2` inconclusive, `1` invalid certificate,
`3` error. What each status and verdict means is in
[What a result means](docs/VERDICTS.md).

## What it does not do

The hard limit is **asymptotic statements with quantifiers over `n`**. "There
exists `N` such that for every `n ≥ N`, every graph…, the loss is `≤ εn²`" is
not decided by this tool.

| Question | `certo`? |
|---|---|
| Is R(3,3) ≤ 6? | **Yes.** `cases`, a 23-line DRAT proof, verified |
| Is R(3,3) = 6? | **Yes.** `bisect`, threshold certified on both sides |
| Is R(5,5) ≤ 48? | **Not in practice.** Finite, but the space is 2^903 |
| Does R(k,k)^(1/k) converge? | **No, in principle.** Asymptotic: not expressible |

The full list, and the FAQ, in [`docs/LIMITS.md`](docs/LIMITS.md).

## In-process API

A CLI costs one Python startup per question. On a Windows laptop that is
**1.2 s before certo is imported** — `python -c pass` alone — against ~70 ms
of certo's own. A sweep of 853 linear programs is two minutes of work behind
twenty minutes of starting Python.

```python
from certo import LPSpec, api

spec = LPSpec(sense="max", title="w")
...
res = api.run("opt", spec)
res.meta["objective"]     # '32/3' -- an exact string, not a float
res.certificate           # the artefact `--cert` would have written
```

| | |
|---|---|
| `api.run(command, spec, limits=None, **options)` | returns a `Result` |
| `api.runnable()` | every command that takes a spec |
| `api.options(command)` | what that command accepts, read off the engine |

`run` **verifies what it produced** and raises `api.SelfCheckFailed` rather
than hand back a certificate that fails its own verifier. It costs under 1% of
an `opt`. Pass `self_check=False` only after measuring.

The engine modules under `certo.engines` stay private; `run`, `runnable` and
`options` are the promise. Commands that read a directory or the environment
(`verify`, `status`, `doctor`, `enum`, …) are not here — `certo.verify` and
`certo.load_spec` are already exported for the first two.

## MCP server

Every command exposed to the LLM, with no copy-pasting. The project ships a
ready [`.mcp.json`](.mcp.json); to register it by hand in Claude Code:

```bash
claude mcp add certo --env CERTO_WORKSPACE=. -- certo-mcp
```

`CERTO_WORKSPACE` (the current directory by default) holds `specs/` and
`certs/`. **Every path is confined there.**

Three design decisions:

1. **Certificates do not come back in the response.** A MUS takes 18× more on
   disk than the whole response, and the model cannot verify it by reading it.
   They are written to disk and the path, kind and digest come back.
2. **Errors come back as data, not as exceptions.** The SDK turns any
   exception into `Error executing tool X` and swallows the reason; a model
   reading that cannot fix its spec. Here it gets what happened and what to
   correct.
3. **`dsl_guide` first.** Both a tool and a resource (`certo://dsl`).

> **Specs are Python code and they get executed when loaded.** That is
> inherent to the DSL and it is the same level of trust an agent with file
> access already has. The server confines paths, but it **is not a sandbox**:
> do not point it at third-party specs.

`certo doctor --register-mcp` adds certo to `.mcp.json` in the current
directory, **merging** with whatever is already registered rather than
replacing it, refusing to touch a file that is not valid JSON, and checking
that the server actually starts — a different question from whether it is
registered, and the one people mean.

## Languages

English is the default and the source of truth. Spanish ships as an overlay:

```bash
certo core examples/amgm.py --lang es      # or CERTO_LANG=es
```

Translations live in [`src/certo/locales/`](src/certo/locales/) as JSON. A
missing key falls back to English, so a partial translation degrades instead
of breaking. To add a language, copy `en.json`, translate the values and keep
the `{placeholders}` — there is a test that enforces both invariants.

Two things deliberately stay English whatever `--lang` says, because they are
API surface rather than prose: **command names and flags**, and **MCP tool
names and descriptions**. Certificates store note **keys**, not rendered text,
so one issued in Spanish reads correctly for an English reader.

## Tests

Over five hundred, no test framework required. The count is deliberately not
given exactly: the previous README said 253 when there were twice that, and a
number nobody recomputes goes stale.

```bash
for t in smoke mcp i18n extras adversarial determinism; do python tests/test_$t.py; done
```

`python tests/run_examples.py` runs all 65 example specs and verifies every
certificate they produce.

Release notes in [CHANGELOG.md](CHANGELOG.md); what is planned, blocked and
deliberately refused in [BACKLOG.md](BACKLOG.md).

## Licence

MIT. The synthesis engine is a reimplementation of the CEGIS algorithm from
[marcelwa/CEGIS](https://github.com/marcelwa/CEGIS) (MIT), not of its code.
