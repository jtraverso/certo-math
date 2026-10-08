# What it does not do

This page matters as much as the list of commands.

## The hard limit

**Asymptotic statements with quantifiers over `n`.** "There exists `N` such
that for every `n ≥ N`, every graph…, the loss is `≤ εn²`" is not decided by
this tool. `prove` and `synth` work over decidable formulas or bounded domains;
`sweep` and `cases` over finite families.

The ladder, with Ramsey numbers as the example:

| Question | `certo`? |
|---|---|
| Is R(3,3) ≤ 6? | **Yes.** `cases`, a 23-line DRAT proof, verified |
| Is R(3,3) = 6? | **Yes.** `bisect`, threshold certified on both sides |
| Is R(5,5) ≤ 48? | **Not in practice.** Finite, but the space is 2^903 |
| Does R(k,k)^(1/k) converge? | **No, in principle.** Asymptotic: not expressible |

## The specific limits, each stated in the run's own output

- `sweep` and `cases` settle the **finite case**, not the theorem.
- A `sweep` over a bare `bool` predicate is **reproducible**, not certified:
  nothing establishes that the predicate's answers are right.
- The `graph_set` certificate verifies non-isomorphism and the filters, **not
  completeness** of the family.
- For an ILP the dual certifies the **relaxation bound**, not integer
  optimality.
- `mixed` certifies that a construction exists and attains a value — not that
  the discrete skeleton was optimal, unless `achieved` meets `bound`.
- `shrink` gives a **1-minimal, not minimum** counterexample.
- `audit` drops hypotheses one at a time, so it does not establish that the
  hypothesis set is **jointly** minimal.
- `bisect` **assumes monotonicity** in the parameter; it checks the endpoints
  and warns if they do not behave, but monotonicity itself is not proved.
- `parametric` and `peak` use a shift test that is **sufficient and not
  necessary**, so a failure means *not established by this route*, never
  *false*.
- `ideal` works over **ℂ**. A proper ideal means a complex root exists and says
  nothing about a real one.
- `eliminate` gives a resultant that is **necessary** for a common root over any
  field and **sufficient** only over an algebraically closed one.
- `sos` is incomplete: from degree 4 in 3 variables there are non-negative
  polynomials that are not sums of squares.
- `order` certifies the **exponent, not the constant**.
- `cone` computes the numbers two geometric theorems consume; it does **not**
  claim a smooth chart, a crepant modification, or an SNC or reduced fibre.
- `bounds` will never prove a quantity non-zero when it is in fact zero; it
  reports `resource_exhausted`.
- Quantifier elimination over the reals is doubly exponential and hangs on
  textbook examples. That is why `qe` is not among the commands.

- A `card` -- role, link, pending -- is **declared**, never checked: it says
  what the author meant the result for, and a PASS that rests on something
  pending is conditional.
- An exact LP solved from the float solver's basis is still **checked**, not
  believed: `check_lp` decides, whatever the route that found it.

**The niche is clear:** discover objects, destroy false formulations and
minimise hypotheses before paying the cost of formalising them.

## Things certo will not guess

A recurring design decision, listed in one place because it explains a lot of
refusals:

| It refuses | Because |
|---|---|
| a float in a `BoundSpec` expression | an enclosure built from `0.1` is rigorous about `3602879701896397/2^55` |
| a non-integer entry in a `MatrixSpec` | a matrix quietly rounded is a different matrix |
| `reduce="auto"` on an unrecognised type | a witness minimal for the wrong relation looks exactly like one minimal for the right one |
| both `canonicalize` and `labelling` | one asks to be believed, the other asks to be checked |
| a symmetry generator failing any of the three hypotheses | a wrong group gives a wrong reduction, not a weaker one |
| a `peak` maximiser with non-integer coefficients | an argument about a point that does not exist proves nothing |
| `cover --prove-optimal` without `candidates=` | a cover is only minimal relative to what you were willing to use |
| a canonical form beyond its cap | an invariant that merged two non-isomorphic families would merge two orbits, and nothing downstream would notice |

---

# FAQ

**Is this a theorem prover?**
No. It decides formulas in decidable theories and verifies finite cases. For
the theorem, Lean or Rocq. certo is the layer before.

**If I already trust Z3, what is the certificate for?**
So that whoever reads your paper does not have to. A Z3 `unsat` is an
assertion; a verified DRAT proof is something a referee checks on their own
machine without running your code. It is also a safety net: if the solver had a
bug, the certificate would not verify and you would get `ERROR`, not `PROVED`.

**What does `unknown_solver` mean? Is it "does not exist"?**
No. It means the solver finished without concluding. `timeout` is the clock
running out, `resource_exhausted` the budget, `out_of_theory` the formula
falling outside the decidable fragment. All four differ from `unsat`, which
does mean "does not exist".

**Why did my `opt` come out in floating point?**
Because nothing exact verified. certo tries three routes in order: reconstruct
CBC's answer as rationals; derive the dual from the primal by complementary
slackness; and solve the dual outright with an exact simplex. The usual cause of
the first two failing is input data that were already floats -- pass them as
`Fraction` or as the string `"7/12"`. The third route is bounded by a pivot
budget, so a large enough program can exhaust it.

**My `opt` reported a number but wrote no certificate.**
That is deliberate. A floating-point certificate is allowed
to be loose; it is not allowed to be one certo itself rejects. When the only
certificate available fails `certo verify` -- which is what a dual of all zeros
does, since `b.0 = 0` bounds nothing -- the number comes back labelled
uncertified and no file is written. An artefact that fails the verifier is not a
weaker certificate; it is not a certificate.

**Why is `prove` fast on one polynomial and hopeless on another?**
Degree. On `t^k <= t` over `[0, 1]` — trivially true, squarely decidable —
degree 10 proves in 12 ms and degree 11 does not prove in 20 seconds. It is a
cliff, not a slope, and it sits far below where people expect: a degree-63
goal is not "a bit harder". `certo lint` warns at 11. The remedy is a
substitution that lowers the degree; one user's degree-63 schedule became
`t = s^3` plus a domination argument, and certo closed it in 4.3 ms.

**I need to run thousands of instances.**
Do not loop over the CLI. Each call pays a Python startup — 1.2 s on Windows
before certo is imported — so a two-minute sweep takes twenty. The
[in-process API](../README.md#in-process-api) is `api.run(command, spec)`, and
it keeps the exact rationals that a hand-rolled float fallback gives up.

**Why is the built-in SAT solver slow?**
Because it is a CDCL in Python. It exists because pysat's proof logging does not
work on Windows — it returns 0 lines with every one of its solvers — and without
a proof there is no certificate. For large instances:
`certo cases spec.py --solver-binary /path/to/cadical`.

**Can I trust that CDCL?**
You do not have to. If it emitted a malformed proof, the DRUP checker rejects it
and you get `ERROR`. There is also a differential test against Z3 over random
CNFs. **The checker audits the solver.**

**Are results reproducible?**
Those of our engines are: the budget is work, not time. Your `sweep` predicate
is outside that guarantee.

**What if I change the spec after generating a certificate?**
`verify` still accepts it — it verifies on its own — but warns that it no longer
corresponds to the current file. `certo status` calls that **stale**.

**Does `synth` prove anything?**
It finds a candidate in the bounded domain you declared. That is a discovery,
not a theorem, and the banner says so. For the general statement, use
`--prove-candidate`.

**How do I connect this to Lean?**
`certo export --lean` emits **one** thing: a linear Farkas certificate as a
runnable `linarith` example. Everything else is by hand, and that is
deliberate — certo used to emit scaffolding for several certificate kinds and
none of it compiled, which costs a Lean build to discover. Where a certificate
is the deliverable, what a formalisation needs from it is the numbers and the
statement, and both are in the payload.

**Why not a real SOS certificate through an SDP, in `farkas --nonlinear`?**
Because an SDP is solved in floating point, so what comes back is not exact, and
an inexact certificate is not citable — the same reason `opt` reconstructs
rationals instead of printing the solver's floats. A degree-2 heuristic whose
output is exact beats a degree-*d* one whose output needs a caveat.
`certo sos` is the exact route: numeric search, rational reconstruction, exact
LDLᵀ.

**Can I use it offline with nothing else installed?**
Yes. `z3-solver` and `pulp` ship their binaries; the rest is pure Python.
