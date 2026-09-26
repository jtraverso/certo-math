# What a result means

Every certo command answers with **two words and, usually, a certificate**:
a *status* and a *verdict*. They are different questions, and reading one as
the other is the most common way to misread a result. This page is the one
place that says what each means, command by command where it differs.

## Status and verdict are not the same thing

The **status** is what the solver said about the query certo *posed to it*.
The **verdict** is what that means for *the question you asked*.

They come apart because certo usually poses the negation of your question.
To prove `x > 0` it asks whether `x <= 0` is possible; the solver says
`unsat`, and your verdict is `proved`. To prove that an integer optimum is 9,
branch and bound asks whether anything beats 9; the answer is `unsat`, and the
verdict is `proved`. **An `unsat` status on a proved optimum is not a
failure.** Read the verdict.

## The seven statuses

| Status | Means | Conclusive |
|---|---|---|
| `unsat` | the query certo posed has no solution | **yes** |
| `sat` | the query has a solution, and certo has it | **yes** |
| `unknown_solver` | the solver stopped without concluding, for its own reasons | no |
| `timeout` | the clock ran out | no |
| `resource_exhausted` | a node, memory or rlimit budget ran out | no |
| `out_of_theory` | the question is outside what this command decides | no |
| `explored` | `--explore` answered cheaply, in floating point or on a sample, and certified nothing | no |

**None of the last four means "does not exist".** Each is a different reason
for having no answer, and they are kept apart because a reader who sees
`unknown` tends to write "there is no solution". `resource_exhausted` on a
search usually comes with what the search knew when it stopped -- see
`branch_frontier` below.

## The seven verdicts

| Verdict | Means for your question |
|---|---|
| `proved` | what you claimed holds, and the certificate is the proof |
| `refuted` | what you claimed fails, and the certificate carries the counterexample |
| `satisfiable` | what you asked for exists, and here it is -- a point, an optimum, a design |
| `unsatisfiable` | what you asked for does not exist: your constraints contradict each other |
| `inconclusive` | no answer. The status says why |
| `error` | the command could not run: a spec that does not load, a flag that does not apply |
| `likely` | `--explore` found it where it looked, uncertified. Never `proved`; `certo promote` is how it becomes one |

## Exit codes

`0` conclusive, `2` inconclusive, `1` a certificate that fails its own
check, `3` error. `lint` differs: `0` clean or notes only, `1` errors,
`2` warnings. Scripts should branch on these, not on the text.

`--deadline` stops a run with `2`, after printing every thread's stack. Any
OTHER code is not certo's: `-1073741819` (`0xC0000005`) or `-1073740022`
(`0xC000070A`) on Windows, or a negative signal number on Linux, is the
process dying in native code; a large or negative code with nothing on
stderr is usually a kill from outside -- a driver's own timeout. A run that
ends with no output and succeeds when relaunched: run `certo doctor`, whose
`startup` row names the start-up hooks known to kill the interpreter before
certo runs. Setting `PYTHONFAULTHANDLER=1` makes even those print a stack.

### Calling certo from a program

- **Use `python -m certo ...`, not `certo`.** On Windows `certo.exe` is a
  launcher that starts the interpreter as a *child*. A timeout that kills
  `certo.exe` leaves that interpreter alive and holding the pipes, and the
  caller waits on them forever. Under load the launcher itself can also fail
  to be found (`WinError 2`). `python -m certo` is one process and no
  launcher. If a launcher is unavoidable, kill the whole tree
  (`taskkill /T /F /PID ...`).
- **`--json` always writes JSON.** A run that fails, whether by an exception
  (exit `3`) or a refusal (exit `1`), and would have left stdout empty now
  writes one line: `{"status": "error", "exit": ..., "message": ...}`, where
  the message is what stderr said. The one thing it cannot cover is a
  process that dies natively before Python runs. `doctor` names the start-up
  hooks known to do that.
- **Start-up cost.** Each run imports certo and z3 again. Where a `.pth` hook
  slows or kills interpreter start-up, `python -S` with the site-packages
  directory on `PYTHONPATH` skips every `.pth` file. One user measured
  `import certo` falling from 10–21 s to 1.7–4.8 s that way, without touching
  their Python installation.

## Optimisation: four different claims

This is where the words matter most, because four results look alike on
screen and establish very different things.

| What you see | Command | What is established |
|---|---|---|
| `EXACT optimum certified: v` | `opt` on an LP | **the optimum**, in exact rationals, with a dual that proves nothing does better |
| `integer optimum v, CERTIFIED` | `opt` on an ILP, tight | **the integer optimum**: an integral point reaches the relaxation's exact bound |
| `best integral point found: v ... bounds the optimum by b` | `opt` on an ILP, with a gap | only that the optimum lies **between** `v` and `b`. The integral point is the solver's, not proved optimal |
| `OPTIMUM v, PROVED` | `mixed --prove-optimal`, `cover --prove-optimal` | **the integer optimum**, by branch and bound: every leaf certified, and the tree checked to cover the whole integer domain |

When `opt` reports a gap, **`certo mixed SPEC --prove-optimal` closes it** on
the same spec. It has existed since 0.4.0; the message now says so.

### `mixed`: three levels, named in the certificate

| Level | Means |
|---|---|
| `feasible` | this design exists and achieves its value. **No optimality at all** |
| `conditional_optimum` | the best the continuous part can do **given this discrete skeleton**. Another skeleton may do better. **It is not a proof of the global optimum**, and it is the level most often read as one |
| `global_optimum` | the achieved value meets the relaxation bound over all skeletons, so nothing does better |

To go from `conditional_optimum` to a proof, use `--prove-optimal`.

### A search that stopped

`--prove-optimal` that runs out of nodes or clock returns
`resource_exhausted` with a **`branch_frontier`** certificate: the incumbent,
the best bound, the gap, and every node still open. That is a status report,
not a proof -- but it is exact, and the incumbent is a genuine lower bound.
It is never promoted to "optimal" because the budget ended.

## A negative, and an absence of an answer

Several commands distinguish "no" from "could not tell", and the difference
lives in the certificate as `false` against `null`.

| Field | `false` means | `null` means |
|---|---|---|
| `semigroup` `in_semigroup` | not in the semigroup, and the graded search that proves it is bounded | the search was not finite or ran out |
| `semigroup` `pointed` | not pointed, **with a zero combination of the generators that shows it** | neither a grading nor that combination was found |
| `semigroup` `normal` | -- | always `null`: a witness refutes normality, nothing here asserts it |
| `hilbert` `is_minimal_generating_set` | decided: not the minimal set, and why | could not be decided |

## Scope: what a conclusive answer is about

A conclusive verdict is conclusive **about what was asked**, which is not
always the statement you have in mind.

* `sweep` and `cases` settle **the finite cases** they were given, not the
  general statement.
* `synth` **discovers** over a bounded domain. It does not prove a theorem.
* `family` and `sweep` take the **completeness of their list** as the spec's
  claim, the way a proof takes its hypotheses.
* Every certificate states what it does **not** establish; the command
  reference has a "Not established" line for each command.

## Verifying: valid, invalid, and a warning

`certo verify FILE` redoes every check from the certificate alone.

* **VALID** -- every check passed.
* **INVALID** -- a check failed. The certificate must not be relied on,
  whatever produced it.
* **A warning on a valid certificate** is a different fact from invalidity:
  a `--target` not reached, a certificate from an older version that says
  less than a new one would, or a floating-point certificate marked **not
  citable**. The certificate is correct; the warning says what it does not
  give you.
