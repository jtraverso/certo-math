"""One table: command, spec type, engine, certificate kind. Derived, not typed.

Four surfaces describe the same forty-six commands -- the README in two
languages, the command reference in two languages, the project page, the
routing table the terminal prints, and the MCP tool list -- and every one of
them has drifted at least once. The README table said twenty-eight while
listing twenty-nine with thirty-nine in the CLI. The Spanish README ran two
releases behind. The project page still said forty-three the day after the
forty-sixth command shipped.

None of those was a hard problem. Each was a number somebody wrote down and
nobody recomputed, which is the failure this whole project exists to refuse
everywhere else. So the table is computed here, from the parser, the routing
map and the verifier registry, and the tests compare the documents against it
rather than against each other.

WHAT IS DERIVED AND WHAT IS DECLARED. The command list, its aliases, the spec
type, the engine module and whether a command is solver-free all come from code
that has to be right for the tool to work at all -- there is no second place to
get them wrong. The certificate KIND is declared in `routing.KIND_OF`, because
an engine can emit different kinds on different paths, and `tests/run_examples`
checks the declaration against what the engines actually produce.
"""
from __future__ import annotations

import argparse


def commands() -> list:
    """Every subcommand, with its aliases, in the order the parser has them."""
    from .cli import build_parser

    sub = [a for a in build_parser()._actions
           if isinstance(a, argparse._SubParsersAction)][0]
    seen, out = {}, []
    for name, parser in sub.choices.items():
        if id(parser) in seen:
            seen[id(parser)]["aliases"].append(name)
            continue
        row = {"name": name, "aliases": [], "help": parser.description or ""}
        seen[id(parser)] = row
        out.append(row)
    return out


def rows() -> list:
    """The whole table, one entry per command."""
    from . import routing

    questions = {}
    for _head, items in routing.BY_QUESTION:
        for key, shown in items:
            questions[shown.split()[0]] = key

    out = []
    for row in commands():
        name = row["name"]
        runner = routing.RUNNERS.get(name)
        out.append({
            "command": name,
            "aliases": row["aliases"],
            "help": row["help"],
            "spec": routing.SPEC_OF.get(name),
            "engine": runner[0].rsplit(".", 1)[-1] if runner else None,
            "entry": runner[1] if runner else None,
            "kind": _one_kind(routing.KIND_OF.get(name)),
            "solver_free": name in routing.SOLVER_FREE,
            "tier": routing.TIER.get(name),
            "question_key": questions.get(name),
        })
    return out


def _one_kind(v):
    """The kind a command usually emits; a tuple names the common one first."""
    return v if v is None or isinstance(v, str) else "/".join(v)


def kinds() -> list:
    """Every certificate kind the verifier registry knows."""
    from .certificate import VERIFIERS

    return sorted(VERIFIERS)


def counts() -> dict:
    """The numbers the documents state, computed once."""
    return {"commands": len(rows()), "kinds": len(kinds()),
            "spec_types": len({r["spec"] for r in rows()
                               if r["spec"] and r["spec"] != "*"})}


#: The numerals the documents spell out, so a test can compare a heading to a
#: count without a second table of words to keep in step.
WORDS_EN = {
    28: "twenty-eight", 29: "twenty-nine", 30: "thirty", 31: "thirty-one",
    32: "thirty-two", 33: "thirty-three", 34: "thirty-four",
    35: "thirty-five", 36: "thirty-six", 37: "thirty-seven",
    38: "thirty-eight", 39: "thirty-nine", 40: "forty", 41: "forty-one",
    42: "forty-two", 43: "forty-three", 44: "forty-four", 45: "forty-five",
    46: "forty-six", 47: "forty-seven", 48: "forty-eight",
    49: "forty-nine", 50: "fifty", 51: "fifty-one", 52: "fifty-two",
    53: "fifty-three", 54: "fifty-four", 55: "fifty-five",
    56: "fifty-six", 57: "fifty-seven", 58: "fifty-eight",
    59: "fifty-nine", 60: "sixty",
}

WORDS_ES = {
    28: "veintiocho", 29: "veintinueve", 30: "treinta",
    31: "treinta y un", 32: "treinta y dos", 33: "treinta y tres",
    34: "treinta y cuatro", 35: "treinta y cinco", 36: "treinta y seis",
    37: "treinta y siete", 38: "treinta y ocho", 39: "treinta y nueve",
    40: "cuarenta", 41: "cuarenta y un", 42: "cuarenta y dos",
    43: "cuarenta y tres", 44: "cuarenta y cuatro",
    45: "cuarenta y cinco", 46: "cuarenta y seis", 47: "cuarenta y siete",
    48: "cuarenta y ocho", 49: "cuarenta y nueve", 50: "cincuenta",
    51: "cincuenta y un", 52: "cincuenta y dos", 53: "cincuenta y tres",
    54: "cincuenta y cuatro", 55: "cincuenta y cinco",
    56: "cincuenta y seis", 57: "cincuenta y siete",
    58: "cincuenta y ocho", 59: "cincuenta y nueve", 60: "sesenta",
}


def as_markdown(lang: str = "en") -> str:
    """The table, as the documents carry it."""
    head = ("| Command | Spec | Engine | Certificate | Solver-free |"
            if lang == "en" else
            "| Comando | Spec | Motor | Certificado | Sin solver |")
    lines = [head, "|---|---|---|---|---|"]
    for r in sorted(rows(), key=lambda r: r["command"]):
        lines.append("| `{}` | {} | {} | {} | {} |".format(
            r["command"],
            "`{}`".format(r["spec"]) if r["spec"] and r["spec"] != "*"
            else "—",
            "`{}`".format(r["engine"]) if r["engine"] else "—",
            "`{}`".format(r["kind"]) if r["kind"] else "—",
            _tier_word(r["tier"], lang)))
    return "\n".join(lines)


def _tier_word(tier, lang="en") -> str:
    if tier is None:
        return "—"
    if lang == "es":
        return {"yes": "sí", "depends": "depende", "no": "no"}[tier]
    return tier


def as_text() -> str:
    """The same table for a terminal, aligned."""
    out = []
    for r in sorted(rows(), key=lambda r: r["command"]):
        out.append("{:<11} {:<24} {:<18} {:<22} {}".format(
            r["command"], r["spec"] or "-", r["engine"] or "-",
            r["kind"] or "-",
            "" if r["tier"] is None else "solver-free: " + r["tier"]))
    return "\n".join(out)
