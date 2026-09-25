"""Lean 4 export: three exporters, and the shortness is the policy.

certo emits Lean for a LINEAR Farkas certificate, for an exact LP bound, and
for a SMITH normal form, and for nothing else. That is not a gap waiting to be filled -- it is where
the line landed after compiling generated files against a real Mathlib, and it
follows from one rule:

    emit Lean only when the output is a SMALL SELF-CONTAINED ARTEFACT whose
    content IS the certificate's data, closed by a tactic that DECIDES the
    fragment its goal lives in

A linear Farkas certificate is exactly that. certo has already verified the
multipliers exactly, `linarith` is complete for linear arithmetic over an
ordered field, and the file is thirty-eight lines: an `example`, its
hypotheses, and one tactic call. If Lean disagrees you find out here rather
than three weeks in.

An exact LP bound is the same shape: weak duality instantiated, the rows its
dual uses and the signs its reduced costs need as hypotheses, the bound as the
goal, closed by `linarith`. Added when two users asked for LP certificates in
Lean, and registered only after a maximisation and a minimisation with
rational coefficients both compiled against the pinned Mathlib.

A Smith certificate is the same shape with a different tactic. The matrices go
out as `!![...]` literals and `decide` re-does the arithmetic: `U * A * V = S`,
both inverses, the determinants, the invariant diagonal. Nothing is asserted
about `A` that Lean does not recompute, and uniqueness of the normal form --
which would make it THE Smith form rather than A factorisation -- is not
claimed, because that is a theorem and this is data. It was added when a user
formalising toric charts wrote that a declaration accompanied by `True` is not
enough. It was not: `integer_matrix` had no exporter, so it went out hollow.

WHAT WAS REMOVED AND WHY. Exporters for classifications, compose proofs, unsat
cores, symbolic quotients and equitable quotients. Each failed the rule in one
of two ways. Some emitted a HEURISTIC -- `nlinarith` adds products and squares
and tries -- so "it should compile" could not be said honestly. Others emitted
enough Lean syntax that the ENCODING became the risk: the equitable-quotient
exporter was first written as a structure with fields, three theorems and
typeclass binders, and compiled against a real Mathlib it produced a wall of
errors in four minutes -- every one of them in the scaffolding and none in the
data.

Rewriting that one as pure data got it compiling in 12.8 seconds. It was still
removed, because certo's job is the step BEFORE the proof assistant: what a
formalisation needs from a session of exploration is the numbers and the
statement, and the certificate already carries both. Somebody formalising a
result writes the structure their own project wants and cannot use this
module's namespace layout anyway.

CERTO DOES NOT WRITE LEAN IT IS NOT CONFIDENT COMPILES. `NotExportable` is the
mechanism rather than the intention: a nonlinear Farkas certificate is refused
here, with the reason and a pointer at the multipliers, instead of rendered
hopefully. A file that fails to elaborate costs its reader more than no file at
all, and teaches them not to trust the next one.

`--check` IS NOT A RELEASE GATE. Building against Mathlib costs minutes,
depends on a toolchain version, and fails in ways that say nothing about
whether certo's mathematics is right. It is a tool for the person touching an
exporter, run once, by hand -- `tests/run_lean.py`.

READING Lean stays, and it is a different capability: `hollow_count` and
`certo status` find hollow statements in files certo did not write, which is
how a `theorem X : True` that passes a build gate and a `sorry` audit gets
caught.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

from . import __version__


class NotExportable(ValueError):
    """certo will not write Lean it is not confident compiles.

    The rule the exports follow: emit only when the output is a small
    self-contained artefact whose content IS the certificate's data. A
    certificate whose data would need a tactic call certo cannot predict the
    behaviour of is refused here rather than rendered hopefully -- a file that
    fails to elaborate costs its reader more than no file at all, and teaches
    them not to trust the next one.
    """
from .i18n import t

HEADER = """\
/-
  Emitted by certo {version} from a {kind} certificate.
  digest {digest}{source}

  What this file is: the STATEMENTS, the data, and the proof steps certo
  established, transcribed. What it is not: a proof that certo is right. Each
  `sorry` below marks a place where something outside Lean was relied on, and
  they are listed at the end.
-/
{imports}

namespace Certo
"""

FOOTER = """
end Certo
"""


# Importing all of Mathlib costs minutes per file and pulls in everything that
# could ever be broken in a local build. Each exporter asks for what it needs.
IMPORTS = {
    # Linarith alone does not bring the ordered-field instances for R or Q,
    # so the hypotheses would not even elaborate. Found by --check, which is
    # the whole reason it exists.
    "farkas": ["Mathlib.Data.Real.Basic", "Mathlib.Tactic.Linarith"],
    "lp_dual": ["Mathlib.Data.Real.Basic", "Mathlib.Tactic.Linarith"],
    # `!![...]` is `Matrix.of ![...]`. The module it lives in MOVED: it is
    # `Mathlib.LinearAlgebra.Matrix.Notation` in 4.28-era Mathlib, not
    # `Mathlib.Data.Matrix.Notation`, and multiplication is in `.Mul` rather
    # than `.Basic`. Found by compiling, which is the whole reason this is a
    # table rather than a guess.
    "smith": ["Mathlib.LinearAlgebra.Matrix.Notation",
              "Mathlib.Data.Matrix.Mul",
              # Without this, `certo_U.det` does not resolve and Lean reports
              # it as an unknown CONSTANT rather than a missing import -- an
              # error that sends the reader hunting for a typo in a name that
              # is spelled correctly.
              "Mathlib.LinearAlgebra.Matrix.Determinant.Basic"],
}


def _header(kind, digest, source="", imports=None):
    mods = imports if imports is not None else IMPORTS.get(kind, ["Mathlib"])
    return HEADER.format(
        version=__version__, kind=kind, digest=digest,
        imports="\n".join("import " + m for m in mods),
        source="\n  source " + source if source else "")


# ---------------------------------------------------------------------------
# farkas -> a linarith example
# ---------------------------------------------------------------------------


def _mono_to_lean(mono) -> str:
    if not mono:
        return "1"
    return " * ".join(mono)


def _poly_to_lean(poly: dict) -> str:
    """A polynomial as Lean source. Rationals stay rationals."""
    parts = []
    for mono, coef in sorted(poly.items()):
        c = Fraction(coef)
        if c == 0:
            continue
        term = _mono_to_lean(mono)
        if term == "1":
            piece = _rat(c)
        elif c == 1:
            piece = term
        elif c == -1:
            piece = "-" + term
        else:
            piece = "{} * {}".format(_rat(c), term)
        parts.append(piece)
    if not parts:
        return "0"
    out = parts[0]
    for p in parts[1:]:
        out += (" - " + p[1:]) if p.startswith("-") else (" + " + p)
    return out


def _rat(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else \
        "({}/{} : ℚ)".format(c.numerator, c.denominator)


#: The marker a hollow statement carries, in its name and in the file. Grep
#: for it: that is the point.
HOLLOW = "HOLLOW"


def hollow_count(text: str) -> int:
    """How many placeholders a generated file carries."""
    return text.count(" : True := by")


def farkas_to_lean(data: dict, source="") -> str:
    """A Farkas certificate as a runnable `example` with its `linarith` call.

    The multipliers are not passed to Lean -- `linarith` rediscovers them, and
    quickly, once it is given the right hypotheses. Which hypotheses those are
    is precisely what the certificate found out, and precisely what is lost
    when someone retypes the lemma and hands linarith everything in scope.
    """
    from . import linarith

    p = data["payload"]

    # A degree-2 Positivstellensatz certificate would go out as `nlinarith`,
    # and `nlinarith` is a HEURISTIC: it adds products and squares and tries.
    # Every other tactic certo emits DECIDES the fragment its goal lives in,
    # so this is the one case where "it should compile" could not be said
    # honestly -- and it is refused rather than written hopefully. The
    # multipliers are in the certificate and can be transcribed.
    if p.get("nonlinear"):
        raise NotExportable(t("lean.farkas.nonlinear"))

    rows = linarith.parse_rows(p["rows"])
    lams = [Fraction(x) for x in p["multipliers"]]
    sorts = p.get("sorts") or {}

    used = [(n, poly, rel, lam) for (n, poly, rel), lam in zip(rows, lams) if lam]
    hyps = [(n, poly, rel) for n, poly, rel, _ in used if n != "__goal__"
            and not n.startswith("sq_") and "*" not in n and "^" not in n]

    # Only the variables that actually appear in the used rows: binding the
    # rest would leave Lean with unused binders that say nothing.
    variables = sorted({v for _, poly, _, _ in used for m in poly for v in m})
    binder = " ".join(variables) or "_x"
    types = "ℝ" if not any(sorts.get(v) == "Int" for v in variables) else "ℤ"

    lines = [_header("farkas", data.get("digest", "?"), source), ""]
    lines.append("/-- The hypotheses the certificate actually used, and the")
    lines.append("goal they close. `linarith` is given exactly those: the")
    lines.append("certificate's whole content is which ones matter. -/")
    lines.append("example ({} : {})".format(binder, types))
    for name, poly, rel in hyps:
        lines.append("    ({} : {} {} 0)".format(
            _safe(name), _poly_to_lean(poly), _op(rel)))

    goal = next(((poly, rel) for n, poly, rel, _ in used if n == "__goal__"),
                None)
    if goal is None:
        # No goal row: there is nothing to state, so this is a placeholder and
        # is marked as one rather than closed with `trivial`.
        lines.append("    : True := by")
        lines.append("      sorry    -- certo: {} no goal row in the "
                     "certificate".format(HOLLOW))
    else:
        # The stored row is the NEGATED goal. Emitting the goal positively
        # rather than as `¬ (row)` is what linarith expects, and it is what
        # the lemma actually says.
        poly, rel = goal
        lines.append("    : {} {} 0 := by".format(
            _poly_to_lean(poly), _positive(rel)))
        # `linarith` is handed exactly the hypotheses the certificate used --
        # not everything in scope. Narrowing the list is the difference
        # between a call that closes and one that times out when somebody
        # retypes the lemma later with more around it.
        hints = [_safe(n) for n, _, _ in hyps]
        lines.append("  linarith{}".format(
            " [{}]".format(", ".join(hints)) if hints else ""))

    lines.append("")
    lines.append(FOOTER)
    return _trim_header("\n".join(lines))


#: Beyond this many hypotheses or variables, "linarith closes it" stops being
#: a promise worth making about the time it takes.
LP_LEAN_MAX = 200

_LEAN_WORDS = {"at", "by", "do", "else", "end", "fun", "have", "if", "in",
               "let", "match", "open", "show", "then", "with", "where", "from",
               "theorem", "example", "def", "lemma", "namespace", "section",
               "variable", "calc", "suffices", "this", "Type", "Prop", "Sort"}


def _real(c: Fraction) -> str:
    """A rational constant AS A REAL. `_rat` writes `(p/q : ℚ)`, which is right
    beside rational variables and a coercion puzzle beside real ones."""
    return str(c.numerator) if c.denominator == 1 else         "({}/{} : ℝ)".format(c.numerator, c.denominator)


def _linear(coeffs, names) -> str:
    """`sum c_j x_j` as Lean, subtraction for negative terms, `0` if empty."""
    out = ""
    for j, c in coeffs:
        if not c:
            continue
        mag = abs(c)
        term = names[j] if mag == 1 else "{} * {}".format(_real(mag), names[j])
        if not out:
            out = term if c > 0 else "-{}".format(
                term if mag == 1 else "({})".format(term))
        else:
            out += (" + " if c > 0 else " - ") + term
    return out or "0"


def lp_to_lean(data: dict, source="") -> str:
    """An exact LP bound as an `example` closed by `linarith`: weak duality,
    instantiated.

    The hypotheses are what the dual USES -- the rows with a non-zero
    multiplier, and `0 <= x_j` only where the reduced cost is positive --
    which is the certificate's whole content, as with Farkas. `linarith` is
    complete for linear arithmetic over an ordered field, so it rediscovers
    the multipliers; they are not transcribed. The statement is over the
    reals, which bounds the rational and the integer programs as well.
    """
    p = data["payload"]
    if not p.get("exact"):
        raise NotExportable(t("lean.lp.not_exact"))
    A = [[Fraction(v) for v in r] for r in p["A"]]
    b = [Fraction(v) for v in p["b"]]
    c = [Fraction(v) for v in p["c"]]
    y = [Fraction(v) for v in p["dual"]]
    n, m = len(c), len(A)
    rows_used = [i for i in range(m) if y[i]]
    reduced = [sum((A[i][j] * y[i] for i in range(m)), Fraction(0)) - c[j]
               for j in range(n)]
    signs = [j for j in range(n) if reduced[j]]
    if len(rows_used) + len(signs) > LP_LEAN_MAX or n > LP_LEAN_MAX:
        raise NotExportable(t("lean.lp.too_large", hyps=len(rows_used)
                              + len(signs), vars=n, limit=LP_LEAN_MAX))
    raw = list(p.get("var_names") or ["x{}".format(j) for j in range(n)])
    names, seen = [], set()
    for j, v in enumerate(raw):
        nm = _safe(str(v))
        if nm in _LEAN_WORDS or nm in seen:
            nm = "x{}_{}".format(j, nm)
        seen.add(nm)
        names.append(nm)
    row_names = list(p.get("names") or ["r{}".format(i) for i in range(m)])
    bound = sum((b[i] * y[i] for i in range(m)), Fraction(0))
    used_vars = sorted({j for i in rows_used for j in range(n) if A[i][j]}
                       | {j for j in range(n) if c[j]} | set(signs))
    binder = " ".join(names[j] for j in used_vars) or "_x"

    lines = [_header("lp_dual", data.get("digest", "?"), source), ""]
    lines.append("/-- Weak duality, instantiated: the rows the dual uses and the")
    lines.append("signs its reduced costs need, and the bound they give. -/")
    lines.append("example ({} : ℝ)".format(binder))
    hyps = []
    for j in signs:
        h = "h_{}".format(names[j])
        hyps.append(h)
        lines.append("    ({} : 0 ≤ {})".format(h, names[j]))
    for k, i in enumerate(rows_used):
        name = str(row_names[i])
        if name.endswith("_geq"):
            # Stored negated, as `-a.x <= -b`; written the way it was declared.
            h = "r{}_{}".format(k, _safe(name[:-4]))
            lines.append("    ({} : {} ≥ {})".format(
                h, _linear([(j, -v) for j, v in enumerate(A[i])], names),
                _real(-b[i])))
        else:
            h = "r{}_{}".format(k, _safe(name))
            lines.append("    ({} : {} ≤ {})".format(
                h, _linear(list(enumerate(A[i])), names), _real(b[i])))
        hyps.append(h)
    if p.get("sense") == "min":
        # The system maximises `-w.x`; the lemma a reader wants is `bound' <= w.x`.
        lines.append("    : {} ≤ {} := by".format(
            _real(-bound), _linear([(j, -cj) for j, cj in enumerate(c)], names)))
    else:
        lines.append("    : {} ≤ {} := by".format(
            _linear(list(enumerate(c)), names), _real(bound)))
    lines.append("  linarith{}".format(" [{}]".format(", ".join(hyps))
                                        if hyps else ""))
    lines.append("")
    lines.append(FOOTER)
    return _trim_header("\n".join(lines))


def _trim_header(text: str) -> str:
    """Drop the promise to list `sorry`s when the file carries none.

    A small thing, and the kind of small thing that makes a generated file
    feel unread by whoever generated it.
    """
    body = text.split("-/", 1)[1] if "-/" in text else text
    if "sorry" in body:
        return text
    # The replacement used to name MULTIPLIERS and `linarith`, which is the
    # farkas file talking. A second exporter inherited that sentence and
    # shipped a Smith file explaining itself in terms of a tactic it does not
    # call -- caught by a test asserting the word `sorry` is absent, which it
    # was not, because the sentence saying so contains it.
    return text.replace(
        "is right. Each\n"
        "  `sorry` below marks a place where something outside Lean was"
        " relied on, and\n"
        "  they are listed at the end.",
        "is right.\n"
        "  Nothing here is left open: every statement is closed by a tactic"
        " that\n"
        "  DECIDES the fragment its goal lives in.")


def _op(rel) -> str:
    return {"<=": "≤", "<": "<", "=": "="}[rel]


def _positive(rel) -> str:
    """The negation of a stored row's relation: `p < 0` negated is `p ≥ 0`."""
    return {"<": "≥", "<=": ">", "=": "≠"}[rel]


def _safe(name) -> str:
    out = "".join(c if c.isalnum() or c == "_" else "_" for c in name)
    return ("h_" + out) if not out or out[0].isdigit() else out


# ---------------------------------------------------------------------------
# manifest
# ---------------------------------------------------------------------------


def manifest(paths) -> dict:
    """What produced this Lean file, hashed, so the two can be tied together."""
    out = {"certo_version": __version__, "files": []}
    for path in paths:
        p = Path(path)
        if not p.is_file():
            continue
        raw = p.read_bytes()
        entry = {"path": str(p), "sha256": hashlib.sha256(raw).hexdigest(),
                 "bytes": len(raw)}
        if p.suffix == ".lean":
            # How many of its theorems state nothing. A manifest that recorded
            # only a hash would tie the file to its source and still let a
            # hollow one travel as evidence.
            n = hollow_count(raw.decode("utf-8", errors="replace"))
            entry["hollow"] = n
            if n:
                entry["note"] = ("{} theorem(s) state `True` and are closed "
                                 "with `sorry`: transcribe them before "
                                 "citing this file".format(n))
        if p.suffix == ".json":
            try:
                d = json.loads(raw.decode("utf-8"))
                entry["kind"] = d.get("kind")
                entry["digest"] = d.get("payload") and _digest_of(d)
                entry["provenance"] = d.get("provenance")
            except (json.JSONDecodeError, UnicodeDecodeError):
                pass
        out["files"].append(entry)
    return out


def _digest_of(d):
    from .certificate import Certificate

    return Certificate.from_dict(d).digest()


# ---------------------------------------------------------------------------
# compiling it
# ---------------------------------------------------------------------------


def check(path, project=None, timeout=900) -> dict:
    """Run the Lean toolchain over the emitted file, if there is one.

    "It should compile" is not a claim anyone should have to take on trust
    from a text generator, and it is the claim most likely to be wrong: three
    rounds against a real compiler is what it took to get the graph export
    right. Without a toolchain this says so rather than staying quiet.
    """
    p = Path(path)
    lake = shutil.which("lake")
    if not lake:
        return {"ran": False, "reason": t("lean.check.no_lake")}
    root = Path(project) if project else p.parent
    if not (root / "lakefile.lean").exists() and \
       not (root / "lakefile.toml").exists():
        return {"ran": False, "reason": t("lean.check.no_project", path=str(root))}
    try:
        # ABSOLUTE: the file is named relative to wherever the user ran certo,
        # and lake runs with cwd inside the Lean project. Passing it through
        # as given made lake look for `.github/lean/.github/lean/...` and
        # report "no such file or directory" -- which read as a compile
        # failure, so `--check` had never actually compiled anything in CI.
        out = subprocess.run([lake, "env", "lean", str(p.resolve())],
                             cwd=str(root),
                             capture_output=True, text=True, timeout=timeout,
                             encoding="utf-8", errors="replace")
    except (OSError, subprocess.SubprocessError) as e:
        return {"ran": False, "reason": "{}: {}".format(type(e).__name__, e)}
    text = (out.stdout or "") + (out.stderr or "")
    sorries = text.count("declaration uses 'sorry'")
    # Compiling was never the question. A file whose theorems all state `True`
    # builds cleanly and says nothing, so the count travels beside `ok` and
    # the caller is expected to treat it as a failure.
    hollow = hollow_count(p.read_text(encoding="utf-8", errors="replace"))
    return {"ran": True, "ok": out.returncode == 0, "sorries": sorries,
            "hollow": hollow, "output": text.strip()[:4000]}


#: kind -> the function that writes it. ONE entry, and the shortness is the
#: policy rather than an accident -- see the module docstring.
# ---------------------------------------------------------------------------
# integer_matrix -> literal matrices and the identities that pin them
# ---------------------------------------------------------------------------


def _matrix_to_lean(M) -> str:
    """`!![a, b; c, d]`, Mathlib's literal. Integers, so no coercion games."""
    return "!![" + "; ".join(", ".join(str(int(v)) for v in row)
                             for row in M) + "]"


def smith_to_lean(data: dict, source="") -> str:
    """A Smith certificate as literal matrices and the identities over them.

    WHY THIS EXISTS AS A SEPARATE EXPORTER. A user formalising toric charts
    wrote: "it is not enough to emit a declaration accompanied by `True`".
    They were right -- `integer_matrix` had no exporter at all, so it went out
    as a hollow placeholder, honestly marked and useless. Everything the
    identities need was already in the payload.

    WHAT LEAN RE-ESTABLISHES, and it is the point of sending matrices rather
    than a claim about them: `decide` and `norm_num` re-do the arithmetic. If
    certo's Smith normal form were wrong, `U * A * V = S` would not close, and
    the file would fail to build rather than assert something false.

    WHAT IS NOT CLAIMED. That `S` is THE Smith normal form of `A` -- that is a
    uniqueness statement about a canonical form, and what is checked here is
    that this particular factorisation holds with unimodular factors. The
    invariants are stated as the diagonal they are; uniqueness is a theorem
    and belongs where the theorems are.
    """
    # ONE tactic, named once. Every goal here is a finite computation over
    # concrete integers, so it is DECIDED rather than searched.
    #
    # `decide` reduces matrix multiplication through `Finset.sum` in the
    # kernel, which is where it could hit a recursion limit rather than a
    # wrong answer -- so this was first emitted as `first | decide | norm_num`
    # against that. COMPILED against Mathlib it closed on `decide` every time
    # and the linter flagged the alternative as dead in every theorem. Two
    # warnings per statement to guard a case that did not happen at 4x4 is
    # noise, so the fallback is gone. If a bigger matrix exhausts the kernel,
    # the file FAILS TO BUILD -- which is the honest failure, and the opposite
    # of this module's standing worry, the file that compiles and says
    # nothing.
    tactic = "by decide"

    p = data["payload"]
    if p.get("question") != "smith":
        raise NotExportable(t("lean.matrix.not_smith",
                              question=str(p.get("question"))))

    need = ("matrix", "u", "v", "s", "u_inv", "v_inv")
    missing = [k for k in need if not p.get(k)]
    if missing:
        raise NotExportable(t("lean.matrix.incomplete",
                              names=", ".join(missing)))

    n = len(p["matrix"])
    lines = [_header("smith", data.get("digest", "?"), source), ""]
    lines.append("/-- The matrix the certificate is about, and the unimodular")
    lines.append("factors that bring it to `S`. Every number here is")
    lines.append("literal: Lean re-does the arithmetic rather than trusting")
    lines.append("that certo did it. -/")
    for name, key in (("A", "matrix"), ("U", "u"), ("V", "v"), ("S", "s"),
                      ("Uinv", "u_inv"), ("Vinv", "v_inv")):
        lines.append("def certo_{} : Matrix (Fin {}) (Fin {}) ℤ := {}".format(
            name, n, len(p[key][0]), _matrix_to_lean(p[key])))
    lines.append("")

    lines.append("/-- The factorisation. This is the whole certificate: if it")
    lines.append("does not close, certo was wrong. -/")
    lines.append("theorem certo_smith_factorisation :")
    lines.append("    certo_U * certo_A * certo_V = certo_S := " + tactic)
    lines.append("")

    lines.append("/-- Unimodular means invertible over ℤ, and the inverses")
    lines.append("travel so that nothing has to be re-derived. -/")
    lines.append("theorem certo_U_inv : certo_U * certo_Uinv = 1 := " + tactic)
    lines.append("theorem certo_V_inv : certo_V * certo_Vinv = 1 := " + tactic)
    lines.append("")

    if p.get("det_u") is not None and p.get("det_v") is not None:
        lines.append("/-- ... which the determinants say again, in one number"
                     " each. -/")
        lines.append("theorem certo_det_U : certo_U.det = {} := {}"
                     .format(int(p["det_u"]), tactic))
        lines.append("theorem certo_det_V : certo_V.det = {} := {}"
                     .format(int(p["det_v"]), tactic))
        lines.append("")

    if p.get("det") is not None:
        lines.append("theorem certo_det_A : certo_A.det = {} := {}"
                     .format(int(p["det"]), tactic))
        lines.append("")

    inv = p.get("invariants")
    if inv:
        lines.append("/-- The invariant factors, as the diagonal they are.")
        lines.append("That this is THE Smith normal form is a uniqueness")
        lines.append("statement and is not claimed here. -/")
        for i, d in enumerate(inv):
            lines.append("theorem certo_invariant_{} : certo_S {} {} = {} := {}"
                         .format(i, i, i, int(d), tactic))
        lines.append("")

    if p.get("fingerprint") is not None:
        recipe = p.get("fingerprint_recipe") or {}
        # A PLAIN block comment, not a doc comment: `/-- -/` must attach to a
        # declaration, and this attaches to nothing. Lean's complaint lands on
        # the `end` four lines later, which is not where the mistake is.
        lines.append("/- The number both sides compute separately over their")
        lines.append("own copy of `A`. Horner, base {}, modulus {},".format(
            recipe.get("base", "?"), recipe.get("prime", "?")))
        lines.append("rows then columns after the two dimensions, and `mod`")
        lines.append("is the NON-NEGATIVE residue. Agreement means the two")
        lines.append("sides hold the same matrix. -/")
        lines.append("-- certo fingerprint: {}".format(p["fingerprint"]))
        lines.append("")

    # Close the namespace the header opened, and drop the promise to list
    # `sorry`s. The farkas exporter does both at its return; an exporter that
    # skipped them emitted a file with an unbalanced `namespace` and a header
    # advertising placeholders it does not contain.
    lines.append(FOOTER)
    return _trim_header("\n".join(lines))


EXPORTERS = {
    "farkas": farkas_to_lean,
    # Registered only after it elaborated against a real Mathlib, which took
    # three rounds and found four things no reading would have: two module
    # paths that had moved, six `:=` lost to a format string, a missing
    # determinant import that surfaced as an unknown CONSTANT, and a `/--`
    # documenting nothing whose error landed four lines away. That is the
    # whole argument for the gate.
    "integer_matrix": smith_to_lean,
    # Weak duality, instantiated. Registered after both shapes -- a packing
    # maximisation and a covering minimisation with rational coefficients --
    # compiled against the pinned Mathlib with no `sorry`.
    "lp_dual": lp_to_lean,
}


# ---------------------------------------------------------------------------
# is what we just wrote WELL FORMED? -- the gate that compiling cannot be
# ---------------------------------------------------------------------------

#: The keywords that open a declaration. Anything between one of these and the
#: next must reach a `:=`, `where` or a `by` block, or Lean stops at a token it
#: cannot place -- usually several lines below the mistake.
_DECL = re.compile(r"^\s*(theorem|lemma|example|def|instance|abbrev)\b")


def check_emission(text: str, kind: str = "") -> list:
    """Structural faults in Lean certo just wrote. No Lean, no Mathlib.

    NOT A SYNTAX CHECKER, and the distinction is the whole design. Lean 4's
    grammar is EXTENSIBLE, so what parses depends on what is imported:
    `!![1, 2; 3, 4]` without `Mathlib.LinearAlgebra.Matrix.Notation` fails with
    `unexpected token ';'` -- a PARSE error caused by a missing import. There
    is no import-independent notion of "syntactically valid Lean", and `lean`
    has no parse-only mode: it parses and elaborates together.

    So this checks something narrower and actually decidable here: the
    invariants certo's own emission must satisfy. It is the step that was
    missing between writing the text and `tests/run_lean.py`, which cannot be
    a release gate -- minutes per file, a toolchain dependency, and failures
    that say nothing about whether certo's mathematics is right.

    MEASURED AGAINST THE ONE EXPORTER THAT HAD BUGS. Adding the Smith exporter
    took four rounds against a real Mathlib and produced five emission faults.
    These rules catch three of them -- the missing `:=`, the orphaned `/--`,
    the unclosed namespace -- in milliseconds. The other two were a module
    path that had moved and an absent import, and nothing without Mathlib on
    disk can know either. That ratio is the honest claim.

    Findings are `(line, code, detail)`. Line 0 means the file as a whole.
    """
    stripped, lines = _without_block_comments(text)
    out = []

    opens = sum(1 for ln in lines if ln.strip().startswith("namespace "))
    closes = sum(1 for ln in lines if ln.strip().startswith("end"))
    if opens != closes:
        out.append((0, "namespace", "{} opened, {} closed".format(opens,
                                                                 closes)))

    # A declaration and everything up to the next one: the `:=` may be on a
    # later line, and rejecting a multi-line statement would be a linter that
    # cries wolf.
    starts = [i for i, ln in enumerate(stripped) if _DECL.match(ln)]
    for n, i in enumerate(starts):
        end = starts[n + 1] if n + 1 < len(starts) else len(stripped)
        block = "\n".join(stripped[i:end])
        if ":=" not in block and " where" not in block:
            out.append((i + 1, "unclosed_declaration",
                        lines[i].strip()[:60]))

    # `/-- ... -/` documents the NEXT declaration. Attached to nothing, Lean
    # complains at whatever command comes after -- four lines away, in the
    # case that prompted this.
    # Found on the ORIGINAL lines: `/--` begins with `/-`, so the blanking
    # above erases exactly what this rule looks for. The first version of this
    # check searched the blanked text and therefore never fired -- a rule that
    # consumes its own input, which is the failure mode of a linter nobody
    # then trusts.
    for i, ln in enumerate(lines):
        if not ln.strip().startswith("/--"):
            continue
        j = i
        while j < len(lines) and "-/" not in lines[j]:
            j += 1
        k = j + 1
        while k < len(stripped) and not stripped[k].strip():
            k += 1
        if k >= len(stripped) or not _DECL.match(stripped[k]):
            out.append((i + 1, "orphan_docstring", ln.strip()[:60]))

    if text.count("/-") != text.count("-/"):
        out.append((0, "unbalanced_comment",
                    "{} opened, {} closed".format(text.count("/-"),
                                                  text.count("-/"))))

    # The header either promises to list placeholders or states there are
    # none. Saying one and doing the other is how a file gets read as
    # complete when it is not -- and as incomplete when it is.
    body = text.split("-/", 1)[1] if "-/" in text else text
    promises = "marks a place where something outside Lean" in text
    if "sorry" in body and not promises:
        out.append((0, "unannounced_sorry", "a placeholder the header denies"))
    if promises and "sorry" not in body:
        out.append((0, "promised_sorry", "a promise the file does not keep"))

    # Not that the modules EXIST -- that needs Mathlib on disk -- but that the
    # header is the one this exporter declares. A hand-edited import is
    # otherwise invisible until somebody builds.
    want = IMPORTS.get(kind)
    if want is not None:
        got = [ln.strip()[len("import "):] for ln in lines
               if ln.strip().startswith("import ")]
        if sorted(got) != sorted(want):
            out.append((0, "imports",
                        "declared {} | emitted {}".format(
                            ", ".join(sorted(want)), ", ".join(sorted(got)))))
    return sorted(out)


def _without_block_comments(text: str):
    """The text with `/- -/` blanked, and the original lines beside it.

    Blanked rather than deleted so a finding's line number is the line the
    author would look at. A checker that reports the right problem at the
    wrong line is the thing it was written to replace.
    """
    lines = text.splitlines()
    out, depth = [], 0
    for ln in lines:
        kept, i = [], 0
        while i < len(ln):
            if ln.startswith("/-", i):
                depth += 1
                i += 2
            elif ln.startswith("-/", i):
                depth = max(0, depth - 1)
                i += 2
            else:
                kept.append(" " if depth else ln[i])
                i += 1
        out.append("".join(kept))
    return out, lines
