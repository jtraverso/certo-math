# Specs: the DSL

Python is the host language. A spec is a `.py` file with a `spec()` function
that returns one of the types below. There is no bespoke language, because an
LLM writes Python far better than it writes SMT-LIB.

> **Specs are executed when loaded.** That is inherent to the DSL. It is the
> same level of trust an agent with file access already has, but it means: do
> not run third-party specs you have not read.

```python
import z3
from certo import Spec

def spec():
    a, b, c = z3.Reals("a b c")
    s = Spec()
    s.assume("a_pos", a > 0)      # NAMED hypotheses: core reports on them
    s.assume("b_pos", b > 0)
    s.assume("c_pos", c > 0)
    s.claim((a+b)*(b+c)*(a+c) >= 8*a*b*c)
    return s
```

Name every hypothesis. The name is what `core`, `audit` and `farkas` report
back, and an unnamed hypothesis is one you cannot be told about.

## Which type for which command

| Type | Commands |
|---|---|
| `Spec` | `prove`, `check`, `core`, `farkas`, `audit` |
| `MultiSpec` | `core` over several goals |
| `SynthSpec` | `synth` |
| `LPSpec` | `opt`, `mixed` |
| `PackingSpec` | `opt` |
| `CNFSpec` | `cases`, `shrink` |
| `SweepSpec` | `sweep`, `shrink`, `enum` |
| `DomainSpec` | `sweep`, `cases`, `shrink` over any finite domain |
| `ProofSpec` | `compose` |
| `InductSpec` | `induct` |
| `IdealSpec` | `ideal` |
| `EliminateSpec` | `eliminate` |
| `ParametricSpec` | `parametric` |
| `PeakSpec` | `peak` |
| `SymmetrySpec` | `reduce` |
| `EquitableQuotientSpec` | `quotient` |
| `MatrixSpec` | `matrix` |
| `LinearSystemSpec` | `solve` |
| `ConeSpec` | `cone` |
| `CycleSpec` | `cycle` |
| `BindSpec` | `bind` |
| `FamilySpec` | `family` |
| `CoverSpec` | `cover`, `exists` |
| `RatioSpec` | `ratio` |
| `MomentSpec` | `moment` |
| `EntrySpec` | `entry` |
| `SOSSpec` | `sos` |
| `NumberSpec` | `number` |
| `BoundSpec` | `bounds` |
| `OrderSpec` | `order` |
| `BisectSpec` | `bisect` |

`certo ask spec.py` reads the type and runs the command it belongs to, so you
never have to remember this table. `certo lint spec.py` reads it too, and
names the commands the spec is for.

## Numbers

Coefficients accept `int`, `Fraction`, the string `"7/12"` or `float`:

```python
lp.objective({"x": Fraction(7, 12), "y": "1/3"})
lp.constraint({"x": 1, "y": 1}, "<=", Fraction(1, 2), name="cap")
```

Prefer `Fraction` or the string form. A float that arrives as data is a float
in the certificate, and `verify` will tell you it is not citable. In
`BoundSpec` a Python float **raises** rather than being accepted, because an
enclosure built from `0.1` would be perfectly rigorous about
`3602879701896397/2^55`.

## Finite domains

`DomainSpec` runs the exhaustive pattern — same six states, same predicate
certificates, same calibration — over anything you can enumerate.

```python
from certo import DomainSpec, Outcome

def spec():
    return DomainSpec(
        items=[(s, r) for s in range(2, 8) for r in range(2, 8)],
        predicate=lambda p: bound_holds(*p),
        collect=lambda p: ratio(*p),
        key=lambda p: "s={},r={}".format(*p),
    )
```

`key` turns an item into a stable id: it is what lands in the certificate, so
it must identify the item unambiguously. `verify` checks the ids are unique.
What it cannot check is that the domain is **complete** — the spec defines it.

`items` may be a callable returning an iterator, and `lint` peeks at the count
without materialising it, so `lambda: iter(range(10**7))` is linted in the time
it takes to read the file.

### Certifying the predicate

A bare `bool` gets you a **reproducible** sweep. Returning an `Outcome` gets
you a **certified** one:

```python
from certo import Outcome

def predicate(item):
    res = lp.opt(build(item))
    return Outcome(ok=res.verdict is Verdict.PROVED, cert=res.certificate,
                   detail="W* = " + res.meta["objective"])
```

```bash
certo sweep spec.py --cert-all
```

Both halves are needed. A predicate that certifies every answer but runs with
the default `--cert-all` off keeps only the counterexamples' certificates, and
the certificate then carries one out of twenty-one — and says so. **A
certificate can only attest what it actually contains.**

`ok=None` means "did not conclude". A predicate that crashes or fails to
conclude no longer brings down the whole sweep, but it does block the claim
that the property holds across the family. A counterexample, by contrast,
refutes even if other items failed.

### Measuring instead of refuting

`collect` returns a value per item and the statistics stay **exact** if you
return a `Fraction`: `2/5`, not `0.4`. `predicate` is optional, so you can
measure without refuting anything, and you can return
`Outcome(..., value=...)` so nothing is computed twice.

```python
SweepSpec(n=5, filters=["connected"], collect=lambda g: ratio(g), worst="min")
```

```
CALIBRATION over 21 graphs: min=2/5 (D?{)  max=1 (D~{)  mean=13/21
  3 lowest: D?{ 2/5 | DCw 2/5 | DEg 2/5
```

The certificate stores the values and `verify` recomputes min, max and mean to
check they agree. A conjecture that fails is one fact; *how badly and on which
object* is what tells you whether to weaken it or abandon it.

### Filters

The named ones: `connected`, `chordal`, `triangle_free`, `k4_free`,
`regular`, `has_triangle`, `min_degree=K`, `max_degree=K`, and the edge count
as `edges=K`, a range `edges=A:B` (either end may be left open), `min_edges=K`
or `max_edges=K`.

**With `geng` installed, the ones it can do exactly are done by `geng`**:
`connected`, the degrees and the edge range always, and `triangle_free`,
`k4_free` and `chordal` when the installed `geng`'s own help lists them. Every
filter is still applied afterwards, so pushing one down can only save time --
a user's chordal sweep at n=9 enumerated 274 668 graphs to keep 125, all of the
difference filtered in Python. `enumerated` then counts what `geng` produced,
after its part of the filtering. certo finds `geng` under that name or as Debian's `nauty-geng`.

`filters` accepts callables alongside the named ones, so a family the
catalogue does not know still gets counted properly:

```python
SweepSpec(n=6, filters=["connected", is_split], predicate=...)
```

The counts stay separate — `enumerated` before filtering, `in_family` after —
and `verify` says plainly that a programmable filter cannot be re-checked from
the certificate alone, because it lives in the spec.

## Symmetry: `canonicalize` versus `labelling`

Both declare when two items are the same object relabelled. They differ in
what a certificate can do about it.

```python
canonicalize=lambda t: tuple(sorted(t))          # asks to be believed
labelling=lambda item: {source_point: label}     # asks to be checked
```

`canonicalize` is arbitrary Python, so *"these forty share a canonical form"*
is the **spec's claim**. What `verify` checks is that the decomposition holds
together — the counts add up, the representatives are distinct, each belongs
to the orbit it heads. That is worth having (a decomposition whose parts do
not add up is wrong whatever the group was) and it is not the question.

`labelling` hands over the **permutation** instead of the form. certo applies
it, the result *is* the canonical form, and the permutation travels in the
certificate:

```
[ok] each member IS the representative relabelled, by re-applying the stored
     permutation  (40 re-applied, 0 carried but not decodable, failing: -)
```

Declaring both is refused: one asks to be believed and the other asks to be
checked.

certo's own canonical form is exact and **refuses** rather than guessing. On a
vertex-transitive object it refuses immediately — a 1-factorisation of K6 has
fifteen points that all look alike, and knowing `|Aut| = 120` still leaves
10,897,286,400 cosets. Computing a canonical labelling well is a hard search
that a tool built for it does far better, so nauty finds the labelling, certo
checks it, and the artefact carries both. **There is no cap on that route,
because nothing is searched.**

## Native combinatorial types

Set families, hypergraphs, designs and mask systems were being re-encoded by
hand in every spec: a tuple of frozensets here, bitmasks there, a `key` to make
an id, a `canonicalize` to quotient, a `reduce` to shrink. Four pieces of
boilerplate per problem, each a place to get it subtly wrong.

```python
from certo import DomainSpec, SetFamily

def spec():
    return DomainSpec(
        items=lambda: list(SetFamily.all_families(5, 2, 3)),
        predicate=lambda f: f.intersecting(),
        canonicalize="auto", reduce="auto",      # and no key= at all
    )
```

| | |
|---|---|
| `is_design(t, λ)` | every t-subset in exactly λ blocks |
| `is_uniform(k)`, `is_regular(r)` | the usual two |
| `intersecting()` | all pairs of blocks meet — the Erdős–Ko–Rado shape |
| `covers()` | every point used |
| `SetFamily.all_families(n, k, size)` | the domain to sweep |
| `family_from_masks(n, masks)` | a mask system, with an id and a canonical form |

The value of a native type here is not that it holds data — a tuple does that.
It is that it supplies the three things the rest of the tool asks for:
`key()`, `canonical()` and `reductions()`. So `key`, `canonicalize` and
`reduce` can all be left at `"auto"`, and anyone's own class joins by having
those three methods.

Two families get the same canonical form **exactly when** a relabelling of the
ground set carries one to the other. Points are refined into classes no
relabelling can mix — degree, then the block sizes through each point, then the
same again on the refined classes — and the form is minimised over the
permutations respecting that refinement. On a highly regular family that
degenerates towards `n!`, so there is a cap; hitting it **raises** rather than
falling back to a cheaper invariant, because an invariant that merged two
non-isomorphic families would merge two orbits and nothing downstream would
notice.

## A spec that executes nothing

`load_spec` compiles and runs the `.py` it is handed. For a person editing
their own file that is the trust an editor already has. For an **agent** it is
the thinnest part of the surface: a model that writes a spec writes a program,
and the loader cannot tell a linear program from anything else Python can do.

Most of the corpus does not need it. Write the spec as **data** instead:

```json
{
  "type": "LPSpec",
  "sense": "max",
  "var_names": ["x", "y"],
  "bounds": {"x": [0, 10], "y": [0, 10]},
  "obj": {"x": 2, "y": 3},
  "cons": [["cap_a", {"x": 1, "y": 1}, "<=", 1]]
}
```

```bash
certo opt spec.json          # a .json spec never executes anything
certo opt spec.py --safe     # refuses: this file would be executed
CERTO_NO_EXEC=1 certo-mcp    # the whole server, in one line of .mcp.json
```

Buildable from data: `LPSpec`, `PackingSpec`, `MatrixSpec`,
`LinearSystemSpec`, `ConeSpec`, `CycleSpec`, `CoverSpec`, `CNFSpec`,
`NumberSpec`, `EquitableQuotientSpec`. Anything carrying a z3 formula or a
callable is absent on purpose — there is no way to write one in JSON, and
inventing an expression language is what this project decided not to do.

**What it guarantees, exactly: no code from the file runs.** Nothing more. A
JSON `LPSpec` can still encode the wrong program, and `lint`, the scope
warnings and `verify`'s re-derivation are what work on that. A mode that made
people stop reading their own spec would trade a small risk for a larger one.

**Numbers are exact or refused.** `"7/12"` is a `Fraction`; `0.583` raises,
because a float here is a float in the certificate and `verify` would call it
not citable.

**An unknown key is refused, not ignored.** A field name silently dropped is
how a constraint goes missing — this project has paid for that once already. A
key starting with `_` is a comment, since JSON has none and no spec field
begins with one.

## One table behind every count

```bash
certo commands --table              # command, spec, engine, certificate
certo commands --table --markdown   # as the documents carry it
certo commands --table --json
```

Derived from the parser, the routing map and the verifier registry, and the
tests compare every document against it rather than against each other. The
README table once said twenty-eight while listing twenty-nine with thirty-nine
in the CLI; the project page said forty-three the day after the forty-sixth
command shipped. None of that is a hard problem. Each is a number nobody
recomputed.

## Options and exit codes

Common options go **after** the subcommand:

| Option | Does |
|---|---|
| `--json` | machine-readable result on stdout |
| `--cert FILE` | write the certificate here |
| `--lang` | `en` or `es`; or set `CERTO_LANG` |
| `--timeout-ms` | wall clock, a backstop rather than the budget |
| `--rlimit` | Z3's work budget — this is the reproducible one |
| `--max-memory-mb` | hard ceiling |
| `--seed` | for the engines that take one |
| `--enumerate-timeout-s` | clock for an external enumeration (`geng`), separate from a solver's; default 120 |
| `--max-output-mb` | how much an external enumeration may print before it is stopped; default 64 |

**What the budget reaches.** `--timeout-ms` is handed to z3, to HiGHS and
CBC, to Clarabel inside `sos`, to the SAT binaries, and to `drat-trim` when it
cross-checks a proof. An external enumeration has its own clock, because
enumerating every graph on `n` vertices and deciding a formula are different
jobs. `export --check` compiles Lean with `--check-timeout-s` (default 900),
since a build against Mathlib is minutes. Two things are **not** bounded by
it, deliberately or unavoidably: `doctor`'s probes and the provenance `git`
call keep short fixed bounds of their own, and cddlib's facet computation runs
in-process, where nothing can interrupt a C call short of the process.

Exit codes: `0` conclusive, `2` inconclusive, `1` invalid certificate, `3`
error. `lint` differs: `0` clean or notes only, `1` errors, `2` warnings.

## The schema is frozen

The certificate schema is **frozen from 0.4**: existing payloads do not move,
so a certificate produced for a paper still verifies against a later certo.
New certificate kinds stay additive and always will. New fields on an existing
kind are optional, which is how `unsat_core` gained its Farkas multipliers
without a 0.5 reader noticing.
