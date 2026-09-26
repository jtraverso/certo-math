"""Los siete estados de resultado y el veredicto.

Regla transversal 2: nunca colapsar en tres estados. Un LLM que lee
"unknown" escribe "no existe solucion"; hay que distinguir por que.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any


class Status(str, Enum):
    UNSAT = "unsat"
    SAT = "sat"
    UNKNOWN_SOLVER = "unknown_solver"          # el solver termino sin concluir
    TIMEOUT = "timeout"                        # se agoto el reloj
    RESOURCE_EXHAUSTED = "resource_exhausted"  # rlimit / memoria
    OUT_OF_THEORY = "out_of_theory"            # fuera del fragmento decidible
    # A cheap look, not an answer: `--explore` solved it in floating point or
    # on a sample, and certified nothing. Never conclusive, so it exits 2.
    EXPLORED = "explored"

    @property
    def conclusive(self) -> bool:
        return self in (Status.UNSAT, Status.SAT)


#: z3's own words for why it stopped, in words that do not blame the reader.
#: "canceled" is what it says when a timeout or an rlimit fires, and a user
#: seeing it reasonably wonders what they cancelled.
_REASONS = {
    "canceled": "reason.limit",
    "cancelled": "reason.limit",
    "timeout": "reason.timeout",
    "max. memory exceeded": "reason.memory",
    "smt tactic failed to show goal to be sat/unsat": "reason.fragment",
    "(incomplete (theory arithmetic))": "reason.arith",
}


def readable_reason(raw) -> str:
    """A solver's stop reason, said in a way a reader can act on."""
    from .i18n import t

    key = _REASONS.get(str(raw).strip().lower())
    return t(key) if key else str(raw)


class Verdict(str, Enum):
    PROVED = "proved"
    REFUTED = "refuted"
    SATISFIABLE = "satisfiable"
    UNSATISFIABLE = "unsatisfiable"
    INCONCLUSIVE = "inconclusive"
    ERROR = "error"
    # What `--explore` found, uncertified: the claim held where it was
    # looked at. Never PROVED; `certo promote` is how it becomes one.
    LIKELY = "likely"


def classify_unknown(reason: str) -> Status:
    """Traduce el reason_unknown() de z3 a uno de los estados."""
    r = (reason or "").lower()
    if "timeout" in r or "canceled" in r:
        return Status.TIMEOUT
    if "resource" in r or "memory" in r or "max. memory" in r:
        return Status.RESOURCE_EXHAUSTED
    if "incomplete" in r or "tactic failed" in r or "unsupported" in r:
        return Status.OUT_OF_THEORY
    return Status.UNKNOWN_SOLVER


@dataclass
class Result:
    command: str
    status: Status
    verdict: Verdict
    engine: str
    elapsed_ms: float
    certificate: Any = None          # Certificate | None
    detail: str = ""
    meta: dict = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            "command": self.command,
            "status": self.status.value,
            "verdict": self.verdict.value,
            "engine": self.engine,
            "elapsed_ms": round(self.elapsed_ms, 2),
            "detail": self.detail,
            "meta": self.meta,
            "certificate": self.certificate.to_dict() if self.certificate else None,
        }
