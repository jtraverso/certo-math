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
    "reparar": "repair", "reparacion": "repair", "congelado": "frozen",
    "congelados": "frozen", "propietario": "owner", "propietarios": "owner",
    "forma": "form", "cerrada": "closed", "conjetura": "conjecture",
    "identidad": "identity", "flotante": "floating",
    "packings": "packing", "empaquetamiento": "packing", "empaquetamientos": "packing",
    "empacar": "packing", "triangulo": "triangle", "triangulos": "triangle",
    "arista": "edge", "aristas": "edge", "cubierta": "cover",
    "particiones": "partition", "fraccionario": "fractional",
    "fraccionaria": "fractional",
    "contradictorio": "contradictory", "contradictoria": "contradictory",
    "contradictorios": "contradictory", "contradictorias": "contradictory",
    "contradiction": "contradictory", "inconsistent": "contradictory",
    "contradiccion": "contradictory",
    # 0.32: words from the reports that found nothing
    "perfil": "profile", "perfiles": "profile", "reconstruccion": "repair",
    "relativa": "relative", "relativo": "relative", "retirados": "withdraw",
    "retirar": "withdraw", "retirado": "withdraw", "insertados": "insert",
    "insertar": "insert", "prerrequisito": "prerequisite",
    "prerrequisitos": "prerequisite", "prerequisites": "prerequisite",
    "pendiente": "pending", "pendientes": "pending", "cobertura": "covering",
    "coberturas": "covering", "cajas": "box", "frontera": "boundary",
    "fronteras": "boundary", "boundaries": "boundary", "divisor": "denominator",
    "divisores": "denominator", "denominador": "denominator",
    "denominadores": "denominator", "signo": "sign", "rango": "rank",
    "reducido": "reduction", "reducida": "reduction", "reduced": "reduction",
    "minimize": "minimum", "minimise": "minimum", "minimizar": "minimum",
    "minimiza": "minimum", "maximize": "maximum", "maximise": "maximum",
    "maximizar": "maximum", "sintetizar": "synth", "sintetizado": "synth",
    "sintesis": "synth", "synthesis": "synth", "synthesise": "synth",
    "roles": "role", "rol": "role", "grafo": "graph", "automorfismo": "automorphism",
    "condicionada": "conditioned", "condicionadas": "conditioned",
    "hojas": "leaf", "hoja": "leaf", "leaves": "leaf",
    "isabelle": "coq", "agda": "coq", "hol": "coq", "rocq": "coq",
    "obligacion": "obligation", "obligaciones": "obligation",
    # 0.33
    "paso": "step", "pasos": "step", "sustitucion": "substitution",
    "sustituciones": "substitution", "sustituir": "substitution",
    "monotona": "monotonicity", "monotono": "monotonicity",
    "monotonia": "monotonicity", "monotone": "monotonicity",
    "estimar": "estimate", "estimacion": "estimate", "memoria": "memory",
    "expandir": "expansion", "expansion": "expansion", "tabla": "table",
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
        doc = _doc_for(name)
        out.append({
            "id": name, "type": "command", "command": name,
            "summary": questions[0][0] if questions else help_text,
            "help": help_text, "use": use,
            "spec": spec, "kind": kind, "solver_free": tier,
            "question": doc.get("question"), "answers": doc.get("answers"),
            "not_established": doc.get("not_established"),
            "example": (doc_contracts().get("examples") or {}).get(name),
            "text": " ".join([name, help_text] + [q for q, _ in questions]
                             + [doc.get("question") or "", doc.get("answers") or ""]),
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
                "example": (doc_contracts().get("examples") or {}).get(
                    "{} {}".format(name, opts[0])),
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
        cmds = sorted({c for c, s in routing.SPEC_OF.items() if s == name}
                      | {c for c, takes in routing.ALSO_TAKES.items() if name in takes})
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
        # The spec's own METHODS: `ProofSpec.pending`, `Spec.regime` -- a
        # feature that is a method was invisible to a search of fields.
        for mname, fn in sorted(vars(cls).items()):
            if mname.startswith("_") or not inspect.isfunction(fn):
                continue
            mdoc = inspect.getdoc(fn) or ""
            if not mdoc:
                continue
            mfirst = mdoc.split("\n\n")[0].replace("\n", " ")
            out.append({"id": "{}.{}".format(name, mname), "type": "spec_method",
                        "spec": name, "commands": cmds, "summary": mfirst,
                        "use": "{}(...).{}{}".format(name, mname, _sig(fn)),
                        "text": " ".join([name, mname.replace("_", " "), mfirst])})
    for na in NOT_AVAILABLE:
        out.append({"id": "na:" + na["id"], "type": "not_available",
                    "summary": na["what"], "why": na["why"], "instead": na["instead"],
                    "use": na["instead"],
                    "text": " ".join([na["id"].replace("_", " "), na["what"], na["why"]])})
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


def _sig(fn) -> str:
    try:
        params = list(inspect.signature(fn).parameters)
    except (TypeError, ValueError):
        return "(...)"
    return "({})".format(", ".join(p for p in params if p != "self"))


#: WHAT CERTO DOES NOT DO, said where a search lands. A model that finds
#: nothing guesses; one that finds "not here, and this instead" does not.
#: Each entry names the BACKLOG line it stands for, and a test keeps the two
#: together: an item that ships has to leave this list in the same commit.
NOT_AVAILABLE = [
    {"id": "sos_rank_reduction", "backlog": "Rational SOS certificates on a lower-rank sub-face",
     "what": "a rational sum of squares on a lower-rank face (rank reduction, facial reduction)",
     "why": "research-grade: the face's projector is irrational in general",
     "instead": "certo nonneg on a box (Bernstein), or certo sos for full-rank cases"},
    {"id": "lean_branch_bound", "backlog": "Branch-and-bound trees to Lean",
     "what": "branch-and-bound trees or finite sweeps exported to Lean",
     "why": "only linear Farkas certificates export to Lean today",
     "instead": "certo export --lean on a farkas certificate; verify the tree with certo verify"},
    {"id": "chow_ring", "backlog": "Chow ring and toric intersection",
     "what": "Chow rings and toric intersection numbers",
     "why": "an engine, not a checker; not built",
     "instead": "certo cone and certo semigroup for the local toric data"},
    {"id": "ports", "backlog": "Composition with PORTS",
     "what": "projection contracts for ports, a Kempe trace with lists, balances derived from the trace",
     "why": "planned; 0.35 checks the gluing itself (ports once, one owner per interior)",
     "instead": "certo compose with a ConstructionSpec: the glue, lift and hosting contracts"},
    {"id": "parametric_feasibility", "backlog": "Parametric feasibility certificates",
     "what": "a family of bases with rational formulas over regions covering a parameter domain",
     "why": "planned",
     "instead": "certo parametric, certo profile (one parameter), certo atlas, certo covering"},
    {"id": "atlas_charts", "backlog": "Charts in `atlas`",
     "what": "atlas pieces natively in other coordinate charts (the atlas command itself)",
     "why": "planned: the atlas command covers a domain in one chart",
     "instead": "certo compose with a ConstructionSpec: the charts and substitution contracts"},
    {"id": "declarative_notation", "backlog": "A declarative spec notation that is not code",
     "what": "a spec notation that is not Python (no exec), or SMT-LIB input",
     "why": "planned; specs other than the JSON types are executed",
     "instead": "the JSON spec types (nothing executed), CERTO_NO_EXEC=1"},
    {"id": "normality", "backlog": "The boundary, stated",
     "what": "proving an affine semigroup NORMAL",
     "why": "a witness refutes normality; establishing it is Normaliz's job",
     "instead": "certo semigroup for witnesses and memberships, SemigroupSpec.profiles"},
    {"id": "cegis_provenance", "backlog": "CEGIS witnesses tied to physical resources",
     "what": "CEGIS that produces the matching or cut witness on the same source",
     "why": "planned; 0.35 checks a synthesised parameter against a resource another step certified",
     "instead": "certo compose with a ConstructionSpec: the cegis contract (backed_by); SynthSpec.scope"},
    {"id": "packing_upper_bound", "backlog": "A certified integer UPPER bound for packings",
     "what": "a certified integer upper bound for large packings beyond branch and bound",
     "why": "open: needs cuts or another certificate of the integer value",
     "instead": "certo opt --gap, certo cover --maximum (SAT with DRUP), certo mixed --prove-optimal"},
    {"id": "other_provers", "backlog": "The boundary, stated",
     "what": "exporting to Coq (Rocq), Isabelle, Agda or HOL",
     "why": "the one formal target is Lean 4 with Mathlib",
     "instead": "certo export --lean, certo bind"},
    {"id": "model_families", "backlog": "Integer-parameter model families",
     "what": "families of models in an integer parameter derived from one schema, with the specialisation checked",
     "why": "planned",
     "instead": "certo parametric for a family of LPs; certo induct for statements in n"},
]


#: How certo reads each spec type under each command it takes, and what to
#: know before running it -- what `find --spec` answers.
CONVERTED = {"HypergraphSpec": {"opt": "to_lp", "mixed": "to_lp",
                                "cover": "to_packing (matching) / to_cover (transversal)",
                                "exists": "to_cover (transversal)"},
             "PackingSpec": {"opt": "to_lp", "mixed": "to_lp", "farkas": "as hypotheses"},
             "LPSpec": {"farkas": "as hypotheses"}}


#: The modules whose public functions are indexed as the Python API.
API_MODULES = ("api", "explain", "batch", "tamper", "status_report",
               "discovery", "nosite", "closedform", "scope", "existence",
               "obligation", "evidence", "hardness", "outcome")


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
            # The comment block above AND the one on the line: `repair` said
            # "a dict, or a LIST of steps" inline and what it IS above, and
            # only the inline half was indexed.
            j, above = i - 1, []
            while j >= 0 and src[j].strip().startswith("#"):
                above.insert(0, src[j].strip().lstrip("#").strip())
                j -= 1
            inline = line.split("#", 1)[1].strip() if "#" in line else ""
            return " ".join(x for x in (inline, " ".join(above)) if x)
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
               "spec_method": 0.75, "api": 0.75, "kind": 0.7, "not_available": 0.6}


#: Questions whose words lead to the WRONG entry, and what to say instead.
#: "cubierta" is `cover` to the index, and `cover` partitions a graph into
#: cliques: a user looking for a hitting set took that detour.
NOTES = [
    (re.compile(r"hitting|transversal|set[ -]?cover|vertex[ -]?cover|"
                r"cubierta (por|de) (conjuntos|vertices)|"
                r"cubrimiento (por|de) (conjuntos|vertices)|"
                r"conjunto de impacto"), "find.note.hitting_set"),
    # A timeout is not a missing feature: since 0.32 the result itself reads
    # the question's structure.
    (re.compile(r"time ?out|timed out|tiempo (agotado|limite)|unknown|inconclus"),
     "find.note.timeout"),
]


def notes(query) -> list:
    """What to know before reading the ranking: a word that leads astray."""
    q = _fold(query)
    return [t(key) for pattern, key in NOTES if pattern.search(q)]


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
        matched = sorted(w for w in set(q) if w in ts)
        scored.append((score * TYPE_WEIGHT.get(e["type"], 1.0), matched, e))
    scored.sort(key=lambda se: (-se[0], se[2]["id"]))
    informative = [w for w in set(q) if w in df]
    out = []
    for s, matched, e in scored[:n]:
        # Every word of the query counts, known or not: a word certo has
        # never seen ("coq") is evidence that the question is not about it.
        cover = len(matched) / max(1, len(set(q)))
        out.append(dict(e, score=round(s, 3), matched=matched,
                        confidence=_confidence(s, cover, len(informative))))
    return out


#: Calibrated on the golden queries (tests): every one of them reaches
#: `medium` or better, and the queries about what certo does NOT do stay low.
HIGH, MEDIUM = 7.0, 4.0


def _confidence(score, cover, informative) -> str:
    if informative == 0:
        return "low"
    if score >= HIGH and cover >= 0.5:
        return "high"
    if score >= MEDIUM and cover >= 0.3:
        return "medium"
    return "low"


def answer(query, n=8, surface="cli") -> dict:
    """What a model needs from a search: `found`, `not_available` (certo
    does not do this -- why, and what to use instead) or `not_in_certo`,
    with each result's calls ready for `surface` and how sure the match is."""
    rows = find(query, n=n)
    # Most certain first: a high-confidence entry below a low one was read as
    # second best by a model that stops at the first.
    rank = {"high": 0, "medium": 1, "low": 2}
    rows.sort(key=lambda r: (rank[r["confidence"]], -r["score"]))
    for r in rows:
        r.pop("text", None)
        if r["type"] in ("command", "flag", "spec", "spec_field", "spec_method"):
            r["call"] = calls(r)
    top = rows[0] if rows else None
    # A "not here" entry wins when it matches what the best result does NOT:
    # "export to coq" finds `export`, and "coq" is the word that decides.
    found_words = set().union(*[set(r["matched"]) for r in rows
                                if r["type"] != "not_available"] or [set()])
    na = next((r for r in rows if r["type"] == "not_available"
               and (r["confidence"] != "low" or set(r["matched"]) - found_words)),
              None)
    if top is None or top["confidence"] == "low":
        verdict = "not_available" if na else "not_in_certo"
    elif top["type"] == "not_available" or (
            na is not None and set(na["matched"]) - found_words):
        verdict = "not_available"
    else:
        verdict = "found"
    out = {"ok": verdict == "found", "verdict": verdict, "query": query,
           "results": rows}
    if verdict == "not_available":
        out["not_available"] = {k: na[k] for k in ("id", "summary", "why", "instead")} \
            if na else None
    said = notes(query)
    if said:
        out["notes"] = said
    return out


def _mcp_params():
    """`{tool: [parameters]}` of the MCP server, when it can be imported."""
    global _MCP
    if _MCP is None:
        try:
            from . import mcp_server

            got = {}
            for name, obj in vars(mcp_server).items():
                fn = getattr(obj, "fn", obj)
                if inspect.iscoroutinefunction(fn) and not name.startswith("_"):
                    got[name] = list(inspect.signature(fn).parameters)
            _MCP = got
        except Exception:  # noqa: BLE001 -- no `mcp` installed: no MCP calls
            _MCP = {}
    return _MCP


_MCP = None


def calls(e) -> dict:
    """How to call an entry from each surface: the CLI line, the MCP tool
    call, and `certo.api.run`. Derived from the parser, the tools'
    signatures and the engines' -- never written by hand."""
    from . import api

    out = {"cli": e.get("use")}
    cmd = e.get("command")
    if e["type"] in ("spec", "spec_field", "spec_method"):
        cmds = e.get("commands") or []
        cmd = cmds[0] if cmds else None
        if cmd:
            out["cli"] = "certo {} SPEC".format(cmd)
    if not cmd or cmd == "*":
        return out
    dest = (e.get("flag") or "").lstrip("-").replace("-", "_") or None
    try:
        opts = set(api.options(cmd))
        runnable = cmd in api.runnable()
    except Exception:  # noqa: BLE001
        opts, runnable = set(), False
    if runnable and (dest is None or dest in opts):
        out["api"] = "certo.api.run({!r}, spec{})".format(
            cmd, ", {}=True".format(dest) if dest else "")
    tools = _mcp_params()
    if cmd in tools and (dest is None or dest in tools[cmd]):
        out["mcp"] = "{}(spec_path=...{})".format(cmd, ", {}=true".format(dest) if dest else "")
    elif "run" in tools and runnable and (dest is None or dest in opts):
        out["mcp"] = "run(command={!r}, spec_path=...{})".format(
            cmd, ", options={{{!r}: true}}".format(dest) if dest else "")
    return out


def for_spec(spec) -> dict:
    """What can be done with THIS spec object: every command that takes it,
    how it is read there, the flags, the calls, and what to know first."""
    from . import routing

    name = type(spec).__name__
    cmds = [c for c, s in routing.SPEC_OF.items() if s == name]
    cmds += [c for c, takes in routing.ALSO_TAKES.items() if name in takes]
    conv = CONVERTED.get(name, {})
    cmds += [c for c in conv if c not in cmds]
    rows = []
    for c in cmds:
        got = contract(c) or {}
        rows.append({"command": c, "read_as": conv.get(c, name),
                     "question": got.get("question") or got.get("summary"),
                     "not_established": got.get("not_established"),
                     "flags": [f["flag"] for f in got.get("flags") or []],
                     "call": calls(dict(got, type="command")) if got else {}})
    return {"spec": name, "commands": rows, "notes": _spec_notes(spec)}


def _spec_notes(spec) -> list:
    """What to know before running this particular spec."""
    name = type(spec).__name__
    out = []
    if name == "CoverSpec":
        if not spec.candidates:
            out.append(t("find.spec.cover_no_candidates"))
        try:
            if len(list(spec.universe)) > 62:
                out.append(t("find.spec.cover_sat"))
        except TypeError:
            pass
    if name == "HypergraphSpec":
        out.append(t("find.spec.hypergraph_matching") if spec.problem == "matching"
                   else t("find.spec.hypergraph_transversal"))
        if spec.weights:
            out.append(t("find.spec.hypergraph_weighted"))
    if name == "LPSpec" and any(k in ("integer", "binary") for k in spec.kinds.values()):
        out.append(t("find.spec.lp_discrete"))
    if name == "NonnegSpec" and any(spec.box[n][1] is None for n in spec.box):
        out.append(t("find.spec.nonneg_ray"))
    if name == "SemigroupSpec" and spec.profiles:
        out.append(t("find.spec.semigroup_profiles"))
    if name == "IdealSpec" and not spec.clear_denominators:
        out.append(t("find.spec.ideal_divisions"))
    if name == "SynthSpec":
        out.append(t("find.spec.synth_scope"))
    return out


# --- the docs' contracts, shipped -------------------------------------------------

DOC_FIELDS = {"Question": "question", "Pregunta": "question",
              "Answers": "answers", "Responde": "answers",
              "Certificate": "certificate", "Certificado": "certificate",
              "Not established": "not_established", "No establece": "not_established",
              "Spec": "spec"}


def parse_commands_doc(text) -> dict:
    """`{command: {question, answers, certificate, not_established}}` from a
    COMMANDS.md: the five-line head of each `### certo X` section."""
    out, cmd, field, buf = {}, None, None, []

    def flush():
        if cmd and field:
            out.setdefault(cmd, {})[field] = " ".join(" ".join(buf).split())

    for line in text.splitlines():
        m = re.match(r"^### `certo ([a-z]+)", line)
        if m:
            flush()
            cmd, field, buf = m.group(1), None, []
            if cmd in out:              # a second section: the first is the head
                cmd = None
            continue
        if cmd is None:
            continue
        m = re.match(r"^\*\*([^*]+)\*\* — (.*)$", line)
        if m and m.group(1) in DOC_FIELDS:
            flush()
            field, buf = DOC_FIELDS[m.group(1)], [m.group(2)]
            continue
        if not line.strip():
            flush()
            if field:
                cmd = None              # the head ends at its first blank line
            field, buf = None, []
            continue
        if field:
            buf.append(line.strip())
    flush()
    return out


def build_doc_contracts(root) -> dict:
    """What `data/doc_contracts.json` holds, rebuilt from the repository:
    both COMMANDS.md and which example exercises each command and flag."""
    import ast
    import pathlib

    root = pathlib.Path(root)
    out = {"en": parse_commands_doc((root / "docs" / "COMMANDS.md").read_text("utf-8")),
           "es": parse_commands_doc((root / "docs" / "es" / "COMMANDS.md").read_text("utf-8")),
           "examples": {}}
    tree = ast.parse((root / "tests" / "run_examples.py").read_text("utf-8"))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(getattr(t_, "id", "") == "CASES"
                                                for t_ in node.targets):
            for row in ast.literal_eval(node.value):
                ex, cmd, flags = row[0], row[1], row[2]
                out["examples"].setdefault(cmd, ex)
                for f in flags:
                    if str(f).startswith("--"):
                        out["examples"].setdefault("{} {}".format(cmd, f), ex)
    out["examples"] = dict(sorted(out["examples"].items()))
    return out


_DOC = None


def doc_contracts() -> dict:
    global _DOC
    if _DOC is None:
        import json
        import pathlib

        p = pathlib.Path(__file__).parent / "data" / "doc_contracts.json"
        try:
            _DOC = json.loads(p.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            _DOC = {}
    return _DOC


def _doc_for(command) -> dict:
    from . import i18n

    d = doc_contracts()
    return (d.get(i18n.current()) or {}).get(command) or (d.get("en") or {}).get(command) or {}


if __name__ == "__main__":  # python -m certo.discovery: rebuild the shipped contracts
    import json
    import pathlib
    import sys

    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    target = pathlib.Path(__file__).parent / "data" / "doc_contracts.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(build_doc_contracts(root), indent=1, ensure_ascii=False,
                                 sort_keys=True) + "\n", encoding="utf-8")
    print("wrote", target)


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
