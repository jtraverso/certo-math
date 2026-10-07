"""Does the exported theorem say what the certificate established?

Nothing compared them. The exporter reads a certificate and writes Lean; a bug
anywhere in that path -- a dropped hypothesis, a sign, a coefficient, a goal
rendered from the wrong row -- produces a theorem that compiles, that looks
right, and that is not the one the certificate supports. And it is the exact
failure this project has already had twice, in the other direction: producer
and verifier wrong in the same place, agreeing with each other.

So this does not ask the exporter what it meant. It PARSES THE EMITTED TEXT
BACK and compares the result against the certificate, by a different route:

    certificate -> SMT-LIB2 -> z3 -> linarith rows        (what it established)
    emitted Lean text -> this parser -> linarith rows     (what it says)

Two paths, one comparison. A rendering bug shows up as a mismatch rather than
as a second opinion that happens to agree.

COMPARISON IS SEMANTIC, NOT TEXTUAL, and it has to be. `-a < 0` and `a > 0`
are the same row; the exporter deliberately states a goal positively rather
than as a negation, because that is what the lemma says and what `linarith`
expects. Both sides are normalised to `p REL 0` with a positive leading
coefficient before anything is compared.

WHAT IT DOES NOT CHECK, and says so: that the Lean statement means what you
intended in Mathlib. It checks that the statement corresponds to the
certificate. Whether the certificate encodes your problem is the question no
tool here answers, and the one `verify` has always pushed back to the reader.

The grammar parsed is only the one certo emits -- polynomials over `+ - *`,
rationals as `(p/q : ℚ)`, relations `≤ < = ≥ > ≠`, all against zero. That is
deliberate: a general Lean parser would be a different project, and a
restricted one that REFUSES what it does not recognise cannot quietly approve
something it misread.
"""
from __future__ import annotations

import re
from fractions import Fraction

from .i18n import t as _t

#: `p REL 0` as the exporter writes it, and the row relation it means.
#: The exporter states hypotheses with `_op` and the goal with `_positive`,
#: so both directions appear and both are normalised here.
RELATIONS = {"≤": "<=", "<": "<", "=": "=", "≥": ">=", ">": ">", "≠": "!="}

_HEAD = re.compile(r"^\s*(?:theorem|example|lemma)\b[^(]*\(([^:]+):")
_HYP = re.compile(r"^\s*\(([^:()]+):\s*(.+?)\s*\)\s*$")
_GOAL = re.compile(r"^\s*:\s*(.+?)\s*:=\s*by\s*$")


#: The positive form of a stored row's relation. `_positive` in the exporter,
#: kept here separately so the two can disagree and be caught rather than
#: sharing a bug.
NEGATED = {"<": ">=", "<=": ">", "=": "!=", ">=": "<", ">": "<=", "!=": "="}


class NotParseable(ValueError):
    """The text is outside the grammar certo emits. Refused, not guessed at."""


def _term(piece: str):
    """One term of a polynomial: `3 * x * y`, `-x`, `(1/2 : ℚ) * x`, `7`."""
    piece = piece.strip()
    if not piece:
        raise NotParseable(_t("leancheck.empty_term"))
    sign = Fraction(1)
    while piece.startswith(("-", "+")):
        if piece[0] == "-":
            sign = -sign
        piece = piece[1:].strip()

    factors = [f.strip() for f in piece.split("*")]
    coef, mono = sign, []
    for f in factors:
        rat = re.fullmatch(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*[ℚℝ]\s*\)", f)
        if rat:
            coef *= Fraction(int(rat.group(1)), int(rat.group(2)))
            continue
        if re.fullmatch(r"-?\d+", f):
            coef *= Fraction(int(f))
            continue
        if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", f):
            mono.append(f)
            continue
        raise NotParseable(_t("leancheck.bad_factor", got=f))
    return tuple(sorted(mono)), coef


def parse_poly(text: str) -> dict:
    """A polynomial as `{monomial: coefficient}`, the shape `linarith` uses."""
    # Split on top-level + and - only; the grammar has no brackets around
    # sums, and a rational's own `/` never appears outside `( : ℚ)`.
    pieces, depth, current = [], 0, ""
    for ch in text:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if depth == 0 and ch in "+-" and current.strip():
            pieces.append(current)
            current = ch
            continue
        current += ch
    if current.strip():
        pieces.append(current)

    out: dict = {}
    for piece in pieces:
        mono, coef = _term(piece)
        out[mono] = out.get(mono, Fraction(0)) + coef
    return {m: c for m, c in out.items() if c}


def parse_relation(text: str):
    """`<poly> REL 0` -> (polynomial, relation). Only against zero."""
    for symbol, rel in RELATIONS.items():
        if symbol in text:
            left, _, right = text.partition(symbol)
            if right.strip() != "0":
                raise NotParseable(_t("leancheck.not_zero", got=right.strip()))
            return parse_poly(left), rel
    raise NotParseable(_t("leancheck.no_relation", got=text[:60]))


def parse_statement(text: str) -> dict:
    """The binders, hypotheses and goal of the one statement in the file.

    Returns `{"variables", "hypotheses", "goal"}` with each formula as
    `(polynomial, relation)`. Raises when the text is outside the grammar --
    which for a HOLLOW file it always is, and that is the right answer there.
    """
    variables, hypotheses, goal = [], [], None
    for line in text.splitlines():
        if goal is not None:
            break
        head = _HEAD.match(line)
        if head:
            variables = head.group(1).split()
            continue
        g = _GOAL.match(line)
        if g:
            goal = parse_relation(g.group(1))
            continue
        h = _HYP.match(line)
        if h and variables:
            hypotheses.append((h.group(1).strip(),
                               parse_relation(h.group(2))))
    if goal is None:
        raise NotParseable(_t("leancheck.no_goal"))
    return {"variables": variables, "hypotheses": hypotheses, "goal": goal}


def normalise(poly: dict, rel: str):
    """`p REL 0` in one canonical form, so two spellings compare equal.

    `-a < 0` and `a > 0` are one row. The exporter states hypotheses one way
    and the goal the other, on purpose, so normalising is not tidiness -- it
    is the difference between comparing meanings and comparing strings.
    """
    flip = {"<": ">", ">": "<", "<=": ">=", ">=": "<=", "=": "=", "!=": "!="}
    if not poly:
        return (), rel
    lead = min(poly)
    if poly[lead] < 0:
        poly = {m: -c for m, c in poly.items()}
        rel = flip[rel]
    return tuple(sorted((m, str(c)) for m, c in poly.items())), rel


def rows_of(cert: dict):
    """What the certificate established, as rows. The other path."""
    from . import leanexport

    kind = cert.get("kind")
    payload = cert.get("payload") or {}
    if kind == "unsat_core":
        parsed = leanexport._core_rows(payload)
        if parsed is None:
            return None
        rows, _sorts = parsed
        return [(n, poly, rel) for n, poly, rel in rows]
    if kind == "farkas":
        from fractions import Fraction

        from . import linarith

        # Only the rows the proof USES. A hypothesis whose multiplier is zero
        # is not part of the combination -- that is the documented feature of
        # this certificate, `core` for free, and it is why the exporter leaves
        # it out of the statement. Expecting every row here made the check
        # report `missing: noise` on the one export that works, which turned a
        # correspondence check into a job that is always red. A check nobody
        # can act on is a check nobody reads.
        rows = linarith.parse_rows(payload.get("rows") or [])
        lams = [Fraction(x) for x in (payload.get("multipliers") or [])]
        if len(lams) != len(rows):
            return None          # cannot tell which were used: say so
        return [(n, poly, rel) for (n, poly, rel), lam in zip(rows, lams)
                if lam]
    return None


def correspondence(cert: dict, text: str) -> dict:
    """Does the emitted statement correspond to what the certificate says?

    Returns a report rather than a boolean, because "could not check" and
    "checked and wrong" are different answers and collapsing them is how a
    gap becomes a green tick.
    """
    if " : True := by" in text:
        return {"checked": False, "reason": _t("leancheck.hollow")}

    established = rows_of(cert)
    if established is None:
        return {"checked": False, "reason": _t("leancheck.no_rows",
                                               kind=cert.get("kind"))}
    try:
        said = parse_statement(text)
    except NotParseable as e:
        return {"checked": False, "reason": str(e)}

    want_hyp, want_goal = {}, None
    for name, poly, rel in established:
        if name == "__goal__":
            # The row stores the NEGATED goal. The exporter states it
            # positively by flipping the RELATION and keeping the polynomial
            # -- `not (p < 0)` is `p >= 0` -- so the comparison does the same.
            # Negating the polynomial instead would be a different statement
            # that happens to be equivalent, and would compare unequal.
            want_goal = normalise(poly, NEGATED[rel])
        else:
            want_hyp[name] = normalise(poly, rel)

    got_hyp = {n: normalise(p, r) for n, (p, r) in said["hypotheses"]}
    got_goal = normalise(*said["goal"])

    missing = sorted(n for n in want_hyp if n not in got_hyp)
    extra = sorted(n for n in got_hyp if n not in want_hyp)
    changed = sorted(n for n in want_hyp
                     if n in got_hyp and want_hyp[n] != got_hyp[n])
    goal_ok = want_goal is not None and want_goal == got_goal

    return {
        "checked": True,
        "ok": not missing and not extra and not changed and goal_ok,
        "goal_matches": goal_ok,
        "missing": missing, "extra": extra, "changed": changed,
        "hypotheses": len(want_hyp),
    }


# ---------------------------------------------------------------------------
# an exported semigroup: the DATA read back and compared
# ---------------------------------------------------------------------------


def _ints(text):
    return [int(x) for x in re.findall(r"-?\d+", text)]


def _matrix(text, name):
    m = re.search(r"def {} : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℤ := !!\[(.*?)\]"
                  .format(re.escape(name)), text)
    if not m:
        return None
    rows = [_ints(r) for r in m.group(3).split(";")]
    return rows


def _vector(text, name):
    m = re.search(r"def {} : Fin \d+ → ℤ := !\[(.*?)\]".format(re.escape(name)), text)
    return _ints(m.group(1)) if m else None


def semigroup_correspondence(cert: dict, text: str) -> dict:
    """Does the emitted Lean carry THIS certificate's semigroup?

    Compiling shows the file is consistent with itself; it does not show the
    data is the cone of the paper. What can be checked from here is that the
    data in the file is the certificate's, read back from the text: the
    generators in the certificate's order (and that order named), the
    dimension, the grading, each membership's point and coefficients, each
    separator really separating its generator from the others, and the
    integer inverse really inverting. Tying the generator order to the
    project's own definition is `bind`'s job; this makes sure there is one
    thing to tie.
    """
    p = cert.get("payload", {})
    names = list(p.get("generators") or {})
    want = [list(map(int, p["generators"][n])) for n in names]
    items, bad = [], []

    def check(label, ok, detail=""):
        items.append({"item": label, "ok": bool(ok), "detail": detail})
        if not ok:
            bad.append(label)

    G = _matrix(text, "certo_G")
    if G is None:
        return {"checked": False, "reason": _t("leancheck.sg.no_matrix")}
    check("generators", G == want, "{} row(s)".format(len(G)))
    order = re.search(r"in the certificate's order: (.*?)\. -/", text)
    check("order", order is not None
          and [x.strip() for x in order.group(1).split(",")] == names,
          ", ".join(names))
    check("dimension", all(len(r) == int(p.get("dimension", len(r))) for r in G),
          str(p.get("dimension")))

    u = _vector(text, "certo_u")
    if u is not None:
        grading = [int(str(x)) for x in (p.get("grading") or [])]
        degrees = [sum(a * b for a, b in zip(r, u)) for r in G]
        check("grading", u == grading and all(d > 0 for d in degrees),
              "u = {}".format(u))

    for name, pt in (p.get("points") or {}).items():
        m = re.search(r"theorem certo_mem_{} : \(!\[(.*?)\] : Fin \d+ → ℤ\) ᵥ\* certo_G "
                      r"= !\[(.*?)\]".format(re.escape(_safe(name))), text)
        if not pt.get("in_semigroup"):
            check("membership " + name, m is None, "not claimed")
            continue
        if m is None:
            check("membership " + name, False, "missing")
            continue
        coeffs, target = _ints(m.group(1)), _ints(m.group(2))
        combo = [sum(c * G[i][j] for i, c in enumerate(coeffs))
                 for j in range(len(target))]
        check("membership " + name,
              target == list(pt["point"]) and combo == target
              and all(c >= 0 for c in coeffs)
              and coeffs == [int(c) for c in pt.get("semigroup_coefficients") or []],
              str(target))

    for i in range(len(G)):
        y = _vector(text, "certo_y{}".format(i))
        if y is None:
            continue
        vals = [sum(a * b for a, b in zip(r, y)) for r in G]
        check("separator {}".format(names[i] if i < len(names) else i),
              vals[i] < 0 and all(v >= 0 for j, v in enumerate(vals) if j != i),
              "y = {}".format(y))

    Ginv = _matrix(text, "certo_Ginv")
    if Ginv is not None:
        n = len(G)
        prod = [[sum(G[i][k] * Ginv[k][j] for k in range(n)) for j in range(n)]
                for i in range(n)]
        check("inverse", prod == [[int(i == j) for j in range(n)] for i in range(n)])

    return {"checked": True, "ok": not bad, "items": items, "mismatched": bad}


def _safe(name):
    out = "".join(c if c.isalnum() or c == "_" else "_" for c in str(name))
    return ("h_" + out) if not out or out[0].isdigit() else out


# ---------------------------------------------------------------------------
# an exported ideal identity: the hypotheses, the claim and the cofactors
# read back and compared
# ---------------------------------------------------------------------------

_IDEAL_HEAD = re.compile(r"^(?:example|theorem [^\s{]+) \{(?:R|K) : Type\*\}[^(]*(?:\((.*?) : (?:R|K)\))?\s*$")
_IDEAL_HYP = re.compile(r"^\s*\((h\d+) : (.+) = 0\)\s*$")
_IDEAL_GOAL = re.compile(r"^\s*: (.+?) := by\s*$")


def _ideal_term(piece, names):
    piece = piece.strip()
    coef, exps = Fraction(1), [0] * len(names)
    for f in [x.strip() for x in piece.split(" * ")]:
        m = re.fullmatch(r"\((-?\d+)(?:/(\d+))? : [RK]\)", f)
        if m:
            coef *= Fraction(int(m.group(1)), int(m.group(2) or 1))
            continue
        if re.fullmatch(r"\d+", f):
            coef *= int(f)
            continue
        m = re.fullmatch(r"(«[^»]+»|[A-Za-z_][A-Za-z_0-9']*)(?:\^(\d+))?", f)
        if m and m.group(1) in names:
            exps[names.index(m.group(1))] += int(m.group(2) or 1)
            continue
        raise NotParseable(_t("leancheck.bad_factor", got=f))
    return tuple(exps), coef


def _ideal_poly(text, names):
    text = text.strip()
    if re.fullmatch(r"\(0 : [RK]\)", text):
        return {}
    out = {}
    depth, cur, pieces = 0, "", []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if depth == 0 and text.startswith(" + ", i):
            pieces.append(cur)
            cur = ""
            i += 3
            continue
        cur += ch
        i += 1
    pieces.append(cur)
    for piece in pieces:
        e, c = _ideal_term(piece, names)
        out[e] = out.get(e, Fraction(0)) + c
    return {e: c for e, c in out.items() if c}


def _split_combo(text):
    """`(h) * h0 + (h) * h1` -> [(cofactor text, hypothesis name)]."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(text):
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if depth == 0 and text.startswith(" + ", i):
            out.append(cur)
            cur, i = "", i + 3
            continue
        cur += ch
        i += 1
    if cur.strip():
        out.append(cur)
    pairs = []
    for part in out:
        m = re.fullmatch(r"\s*\((.*)\) \* (h\d+)\s*", part)
        if not m:
            raise NotParseable(_t("leancheck.bad_factor", got=part[:40]))
        pairs.append((m.group(1), m.group(2)))
    return pairs


def ideal_correspondence(cert: dict, text: str) -> dict:
    """Does the emitted `example` state THIS certificate's identity, with
    ITS cofactors? Read back from the text and compared exactly: each
    hypothesis `g_i = 0`, the claim (or `False`), the ring the binder names,
    and the combination `linear_combination` is handed."""
    from .leanexport import lean_name

    p = cert.get("payload", {})
    names = [lean_name(v) for v in p["variables"]]
    n = len(names)

    def parse(d):
        out = {}
        for k, v in (d or {}).items():
            c = Fraction(v)
            if c:
                out[tuple(int(x) for x in k.split())] = c
        return out

    want_g = [parse(g) for g in p["equations"]]
    want_h = [parse(h) for h in p["cofactors"]]
    want_claim = None if p.get("inconsistent") else parse(p.get("claim"))
    integral = all(c.denominator == 1 for q in want_g + want_h
                   + ([want_claim] if want_claim else []) for c in q.values())
    lines = text.splitlines()
    # `export --theorem NAME` writes `theorem NAME {` where `example {` was.
    head = next((l for l in lines if re.match(r"^(?:example|theorem [^\s{]+) \{", l)),
                None)
    if head is None:
        return {"checked": False, "reason": _t("leancheck.no_goal")}
    try:
        got_g, goal, combo = {}, None, ""
        for l in lines:
            m = _IDEAL_HYP.match(l)
            if m:
                got_g[m.group(1)] = _ideal_poly(m.group(2), names)
                continue
            m = _IDEAL_GOAL.match(l)
            if m and goal is None:
                goal = m.group(1)
            if l.strip().startswith("linear_combination"):
                combo = l.strip()[len("linear_combination"):].strip()
        got_claim = None if goal == "False" else \
            _ideal_poly(goal.rsplit(" = 0", 1)[0], names)
        got_h = {name: _ideal_poly(h, names) for h, name in _split_combo(combo)} \
            if combo else {}
    except (NotParseable, AttributeError, ValueError) as e:
        return {"checked": False, "reason": str(e)}

    items = []

    def check(label, ok):
        items.append({"item": label, "ok": bool(ok)})

    check("ring", ("[CommRing R]" in head) == integral
          and (("[Field K] [CharZero K]" in head) == (not integral)))
    check("hypotheses", [got_g.get("h{}".format(i)) for i in range(len(want_g))]
          == want_g and len(got_g) == len(want_g))
    check("claim", got_claim == want_claim)
    check("cofactors", all(got_h.get("h{}".format(i), {}) == h
                           for i, h in enumerate(want_h))
          and set(got_h) <= {"h{}".format(i) for i in range(len(want_h))})
    bad = [i["item"] for i in items if not i["ok"]]
    _ = n
    return {"checked": True, "ok": not bad, "items": items, "mismatched": bad}
