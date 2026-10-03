"""`certo find`: is this in certo, and where?

Agents kept missing what was there. A feature in certo is rarely a command of
its own: it is a FLAG of one (`opt --round`, `opt --cuts clique`,
`verify --md`, `status --root`), a FIELD of a spec (`NonnegSpec.region` is how
an algebraic endpoint is written exactly), or a certificate KIND with its own
checks. `certo commands` lists commands; the rest lived only in a reference
long enough that finding a line in it was the problem.

    certo find "is a polynomial nonnegative on a box"
    certo find "cota entera redondeada"
    certo find --exact opt.round          # one contract, exactly

The index is DERIVED, never written down -- the rule this project keeps
everywhere else, because every hand-kept list of its features has drifted:

  commands, their flags and help    the argument parser
  the question each command answers the routing table, in the active language
  spec types and their fields       the dataclasses in `certo.spec`
  certificate kinds                 the verifier registry, and each kind's note

Matching is lexical -- words and their stems, accents folded, a short English
and Spanish vocabulary of the words a mathematician uses for what certo calls
otherwise -- with no model and no dependency, so the same query returns the
same ranking on every machine.
"""
from __future__ import annotations

import argparse
import dataclasses
import inspect
import math
import re
import unicodedata

from .i18n import t

#: Words a user writes and the words certo's own text uses for them. Spanish
#: first, since half the users write it; then English paraphrases.
SYNONYMS = {
    "polinomio": "polynomial", "caja": "box", "intervalo": "interval",
    "negativo": "negative", "positivo": "positive", "noneg": "nonneg",
    "infactible": "infeasible", "factible": "feasible", "optimo": "optimum",
    "entero": "integer", "enteros": "integer", "redondear": "round",
    "redondeada": "round", "redondeado": "round", "cota": "bound",
    "certificado": "certificate", "demostrar": "prove", "probar": "prove",
    "contraejemplo": "counterexample", "grafo": "graph", "particion": "partition",
    "cubrimiento": "cover", "exportar": "export", "semigrupo": "semigroup",
    "matriz": "matrix", "determinante": "determinant", "simetria": "symmetry",
    "induccion": "induction", "umbral": "threshold", "hipotesis": "hypothesis",
    "verificar": "verify", "lote": "batch", "lotes": "batch",
    "region": "region", "raiz": "root", "raices": "root", "corte": "cut",
    "cortes": "cut", "conflicto": "conflict", "camino": "route", "ruta": "route",
    "objetivo": "target", "exacto": "exact", "exacta": "exact",
    "desigualdad": "inequality", "igualdad": "equality", "cono": "cone",
    "variable": "variable", "parametro": "parameter", "parametrica": "parametric",
    "familia": "family", "barrido": "sweep", "minimo": "minimum",
    "maximo": "maximum", "valor": "value", "fijado": "pin", "ambos": "both",
    "lados": "side", "resumen": "summary", "suma": "sum", "multiplicador": "multiplier",
    "dual": "dual", "rayo": "ray", "vacio": "empty", "falsificacion": "forge",
    "explorar": "explore", "barato": "cheap", "reducir": "reduce",
    "divisibilidad": "divisibility", "reticulo": "lattice", "suave": "smooth",
    "regular": "regular", "libre": "free", "monoide": "monoid",
    "nonnegative": "nonneg", "non": "nonneg", "floor": "round", "ceil": "round",
    "rounding": "round", "rounded": "round", "infeasibility": "infeasible",
    "lean": "lean", "mathlib": "lean", "proof": "prove", "theorem": "prove",
    "lemma": "compose", "lemmas": "compose", "obligations": "owed",
    "progress": "route", "many": "batch", "hundreds": "batch",
    "clique": "clique", "cliques": "clique", "partitions": "partition",
    "tight": "active", "slack": "active", "prices": "dual",
    "packings": "packing", "empaquetamiento": "packing", "empaquetamientos": "packing",
    "empacar": "packing", "triangulo": "triangle", "triangulos": "triangle",
    "arista": "edge", "aristas": "edge", "cubierta": "cover",
    "particiones": "partition", "fraccionario": "fractional",
    "fraccionaria": "fractional",
    "contradictorio": "contradictory", "contradictoria": "contradictory",
    "contradictorios": "contradictory", "contradictorias": "contradictory",
    "contradiction": "contradictory", "inconsistent": "contradictory",
    "contradiccion": "contradictory",
}

STOP = {"a", "an", "the", "of", "on", "in", "is", "it", "to", "for", "and",
        "or", "this", "that", "be", "are", "with", "by", "as", "at", "can",
        "how", "what", "which", "do", "does", "my", "i", "el", "la", "los",
        "las", "un", "una", "de", "del", "en", "es", "y", "o", "que", "con",
        "por", "para", "se", "su", "mi", "como", "cual", "hay", "si"}


def _fold(text) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", str(text))
                   if not unicodedata.combining(c)).lower()


#: Words whose stem is another word of the index: "packing" stemmed to
#: "pack", and a search for a triangle packing found `certo pack`, the
#: archive command.
UNSTEMMED = {"packing"}


def _stem(w) -> str:
    for suf in ("ies", "ing", "es", "ed", "s"):
        if len(w) > len(suf) + 3 and w.endswith(suf):
            w = w[: -len(suf)] + ("y" if suf == "ies" else "")
            break
    # "reduce" and "reducing", "prove" and "proving": one stem
    return w[:-1] if len(w) > 4 and w.endswith("e") else w


def tokens(text) -> list:
    out = []
    # "no negativo" is one word in English ("non-negative"), and split in
    # two it read as "negative".
    text = re.sub(r"\bno[ -]+negativ[oa]s?\b", "nonneg", _fold(text))
    for w in re.findall(r"[a-z0-9]+", text):
        if w in STOP:
            continue
        w = SYNONYMS.get(w, w)
        out.append(w if w in UNSTEMMED else _stem(w))
    return out


# --- the index ------------------------------------------------------------------


def _subparsers():
    from .cli import build_parser

    parser = build_parser()
    sub = [a for a in parser._actions if isinstance(a, argparse._SubParsersAction)][0]
    helps = {a.dest: a.help or "" for a in sub._choices_actions}
    seen, out = set(), []
    for name, p in sub.choices.items():
        if id(p) in seen:
            continue
        seen.add(id(p))
        out.append((name, helps.get(name, ""), p))
    return out


def _questions() -> dict:
    from . import routing

    out = {}
    for _group, rows in routing.BY_QUESTION:
        for key, invocation in rows:
            out.setdefault(invocation.split()[0], []).append(
                (t(key), invocation))
    return out


def _spec_classes() -> list:
    """Every spec class certo EXPORTS, wherever it is defined: reading only
    `spec.py` left out `PackingSpec` (packing.py) and `CNFSpec` (cnf.py), and
    a user searching for the packing spec by name found nothing."""
    import certo

    return [(n, c) for n, c in sorted(vars(certo).items())
            if inspect.isclass(c) and n.endswith("Spec")
            and c.__module__.startswith("certo")]


def entries() -> list:
    """Every entry the index holds: commands, flags, spec fields, kinds."""
    from . import routing
    from .certificate import VERIFIERS

    qs = _questions()
    out = []
    subs = _subparsers()
    # A flag on most commands is the shared parser's -- `--safe`, `--lang` --
    # and is indexed ONCE, not beside every command it happens to reach.
    counts = {}
    for _n, _h, p in subs:
        for a in p._actions:
            for o in a.option_strings:
                counts[o] = counts.get(o, 0) + 1
    common = {o for o, c in counts.items() if c > len(subs) // 3}
    shared = {}
    for name, help_text, p in subs:
        if name == "find":
            # Its own flags describe the index, and matched every query
            # that mentioned what they describe.
            out.append({"id": name, "type": "command", "command": name,
                        "summary": help_text, "help": help_text, "use":
                        "certo find WHAT YOU NEED", "spec": None, "kind": None,
                        "solver_free": None, "text": name + " " + help_text})
            continue
        positional = " ".join((a.metavar or a.dest).upper() for a in p._actions
                              if not a.option_strings and a.dest != "help")
        questions = qs.get(name, [])
        spec = routing.SPEC_OF.get(name)
        kind = routing.KIND_OF.get(name)
        tier = routing.TIER.get(name)
        # How to CALL it, as a flag's `use` reads: the routing table's form
        # ("range --var X") with the positional arguments put back.
        head, _, rest = (questions[0][1] if questions else name).partition(" ")
        use = " ".join(x for x in ("certo", head, positional, rest) if x)
        out.append({
            "id": name, "type": "command", "command": name,
            "summary": questions[0][0] if questions else help_text,
            "help": help_text, "use": use,
            "spec": spec, "kind": kind, "solver_free": tier,
            "text": " ".join([name, help_text] + [q for q, _ in questions]),
        })
        for a in p._actions:
            opts = [o for o in a.option_strings if o.startswith("--")]
            if not opts or a.help in (None, argparse.SUPPRESS) or opts[0] == "--help":
                continue
            if opts[0] in common:
                shared.setdefault(opts[0], a)
                continue
            choices = list(a.choices) if a.choices else None
            out.append({
                "id": "{} {}".format(name, opts[0]), "type": "flag",
                "command": name, "flag": opts[0], "summary": a.help,
                "use": "certo {} {}{}{}".format(
                    name, positional + " " if positional else "", opts[0],
                    " " + "|".join(choices) if choices else
                    ("" if a.nargs == 0 or isinstance(a, (argparse._StoreTrueAction,
                                                          argparse._StoreFalseAction))
                     else " " + (a.metavar or a.dest.upper()))),
                "default": None if a.default in (None, False, argparse.SUPPRESS)
                else a.default,
                "text": " ".join([name, opts[0].lstrip("-").replace("-", " "),
                                  a.help or ""]),
            })
    for flag, a in sorted(shared.items()):
        out.append({"id": flag, "type": "flag", "command": "*", "flag": flag,
                    "summary": a.help, "use": "certo COMMAND ... " + flag,
                    "default": None,
                    "text": " ".join([flag.lstrip("-").replace("-", " "), a.help or ""])})
    for name, cls in _spec_classes():
        doc = inspect.getdoc(cls) or ""
        first = doc.split("\n\n")[0].replace("\n", " ")
        cmds = sorted(c for c, s in routing.SPEC_OF.items() if s == name)
        out.append({"id": name, "type": "spec", "summary": first,
                    "commands": cmds, "use": "{}(...)".format(name),
                    "text": " ".join([name, doc[:900]] + cmds)})
        if dataclasses.is_dataclass(cls):
            for f in dataclasses.fields(cls):
                if f.name.startswith("_"):
                    continue          # private state, not a field to set
                # The field's own comment line, when the source has one.
                note = _field_note(cls, f.name)
                out.append({
                    "id": "{}.{}".format(name, f.name), "type": "spec_field",
                    "spec": name, "field": f.name, "commands": cmds,
                    "summary": note or "{} of {}".format(f.name, name),
                    "default": _default_text(f),
                    "use": "{}(..., {}=...)".format(name, f.name),
                    "text": " ".join([name, f.name.replace("_", " "), note, first]),
                })
    # The Python API: the public functions of the modules a caller imports.
    import importlib

    for mod_name in API_MODULES:
        mod = importlib.import_module("certo." + mod_name)
        for fname, fn in sorted(vars(mod).items()):
            if fname.startswith("_") or not inspect.isfunction(fn) \
                    or fn.__module__ != mod.__name__:
                continue
            doc = inspect.getdoc(fn) or ""
            if not doc:
                continue
            first = doc.split("\n\n")[0].replace("\n", " ")
            out.append({"id": "certo.{}.{}".format(mod_name, fname), "type": "api",
                        "summary": first,
                        "use": "from certo import {}; {}.{}{}".format(
                            mod_name, mod_name, fname, inspect.signature(fn)),
                        "text": " ".join([mod_name, fname.replace("_", " "), first])})
    for kind in sorted(VERIFIERS):
        note = t("cert.note." + kind)
        note = "" if note.startswith("cert.note.") else note
        out.append({"id": "kind:" + kind, "type": "kind", "kind": kind,
                    "summary": note or kind,
                    "commands": sorted(c for c, k in routing.KIND_OF.items()
                                       if k == kind or (isinstance(k, tuple) and kind in k)),
                    "use": "certo verify CERT.json",
                    "text": " ".join([kind.replace("_", " "), note])})
    return out


#: The modules whose public functions are indexed as the Python API.
API_MODULES = ("api", "explain", "batch", "tamper", "status_report",
               "discovery", "nosite")


def _default_text(f):
    if f.default is not dataclasses.MISSING:
        return repr(f.default)
    if f.default_factory is not dataclasses.MISSING:  # type: ignore[misc]
        return repr(f.default_factory())  # type: ignore[misc]
    return None


def _field_note(cls, field) -> str:
    """The comment on a field's line in the source, or the one just above."""
    try:
        src = inspect.getsource(cls).splitlines()
    except (OSError, TypeError):
        return ""
    for i, line in enumerate(src):
        if re.match(r"\s*{}\s*:".format(re.escape(field)), line):
            if "#" in line:
                return line.split("#", 1)[1].strip()
            j, above = i - 1, []
            while j >= 0 and src[j].strip().startswith("#"):
                above.insert(0, src[j].strip().lstrip("#").strip())
                j -= 1
            return " ".join(above)
    return ""


# --- search ---------------------------------------------------------------------

_INDEX = None


def _index():
    global _INDEX
    if _INDEX is None:
        docs = entries()
        toks = [tokens(e["text"]) + tokens(e["id"]) * 2 for e in docs]
        df = {}
        for ts in toks:
            for w in set(ts):
                df[w] = df.get(w, 0) + 1
        _INDEX = (docs, toks, df)
    return _INDEX


#: How much each kind of entry is worth when two score alike: a command is
#: what most questions want, a field the least often.
TYPE_WEIGHT = {"command": 1.0, "flag": 0.95, "spec": 0.8, "spec_field": 0.75,
               "api": 0.75, "kind": 0.7}


def find(query, n=8, types=None) -> list:
    """The `n` entries that best match `query`, best first."""
    docs, toks, df = _index()
    q = tokens(query)
    if not q:
        return []
    N = len(docs)
    avg = sum(len(ts) for ts in toks) / max(N, 1)
    scored = []
    for e, ts in zip(docs, toks):
        if types and e["type"] not in types:
            continue
        score = 0.0
        for w in set(q):
            tf = ts.count(w)
            if not tf:
                continue
            idf = math.log(1 + (N - df[w] + 0.5) / (df[w] + 0.5))
            score += idf * tf * 2.2 / (tf + 1.2 * (0.25 + 0.75 * len(ts) / avg))
        if score <= 0:
            continue
        # The entry's own name in the query is the strongest signal there is.
        if _fold(e["id"].split(":")[-1]) in _fold(query):
            score *= 1.5
        scored.append((score * TYPE_WEIGHT.get(e["type"], 1.0), e))
    scored.sort(key=lambda se: (-se[0], se[1]["id"]))
    return [dict(e, score=round(s, 3)) for s, e in scored[:n]]


def contract(name) -> dict | None:
    """One entry exactly, with everything that belongs to it: `opt`,
    `opt.round` or `opt --round`, `NonnegSpec`, `NonnegSpec.region`,
    `polynomial_nonneg`."""
    docs, _t, _d = _index()
    key = name.strip()
    if "." in key and not key.endswith("Spec") and key.split(".")[0].islower():
        cmd, flag = key.split(".", 1)
        key = "{} --{}".format(cmd, flag.replace("_", "-"))
    for e in docs:
        if e["id"] == key or e["id"] == "kind:" + key:
            out = dict(e)
            out.pop("text", None)
            if e["type"] == "command":
                out["flags"] = [{k: f[k] for k in ("flag", "summary", "use", "default")}
                                for f in docs if f["type"] == "flag"
                                and f["command"] == e["command"]]
                from . import api

                try:
                    out["api_options"] = api.options(e["command"])
                except Exception:  # noqa: BLE001 -- a command api.run does not take
                    out["api_options"] = None
            if e["type"] == "spec":
                out["fields"] = [{k: f[k] for k in ("field", "summary", "default")}
                                 for f in docs if f["type"] == "spec_field"
                                 and f["spec"] == e["id"]]
            return out
    return None


def guide_appendix() -> str:
    """Every spec and its fields, every command's flags -- for `dsl_guide`,
    so the guide can never again lag a release."""
    docs, _t, _d = _index()
    lines = ["", "## Every spec type, every field (derived from the code)"]
    for e in docs:
        if e["type"] == "spec":
            lines.append("  {} -> {}: {}".format(e["id"], ", ".join(e["commands"]) or "-",
                                                 e["summary"][:110]))
            for f in docs:
                if f["type"] == "spec_field" and f["spec"] == e["id"]:
                    lines.append("      .{} = {}{}".format(
                        f["field"], f["default"] if f["default"] is not None else "(required)",
                        "  # " + f["summary"][:80] if f["summary"] and not
                        f["summary"].endswith(" of " + e["id"]) else ""))
    lines.append("")
    lines.append("## Every command's flags (derived from the parser)")
    for e in docs:
        if e["type"] == "flag":
            lines.append("  certo {} {}: {}".format(e["command"], e["flag"],
                                                   (e["summary"] or "")[:110]))
    lines.append("")
    lines.append("Search all of this with the `find` tool: find(query), or "
                 "find(exact='opt.round') for one contract.")
    return "\n".join(lines)
