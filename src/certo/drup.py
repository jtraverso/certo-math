"""Verificador DRUP/DRAT en Python puro.

Un certificado no vale nada si para comprobarlo hay que instalar otra cosa.
Aqui la comprobacion es propagacion unitaria y nada mas: no interviene ningun
SAT solver, asi que el certificado no depende de confiar en el que lo produjo.

Se comprueba RUP en cada paso y, si falla, RAT sobre el literal pivote (los
solvers con inprocesamiento emiten pasos RAT). Si `drat-trim` esta en el PATH
se puede usar como segunda opinion, mucho mas rapida para pruebas grandes.
"""
from __future__ import annotations

from .i18n import t as _t

import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass
class DratReport:
    ok: bool
    checker: str
    steps: int = 0
    rup_steps: int = 0
    rat_steps: int = 0
    deletions: int = 0
    derived_empty: bool = False
    detail: str = ""
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict:
        return {
            "ok": self.ok, "checker": self.checker, "steps": self.steps,
            "rup_steps": self.rup_steps, "rat_steps": self.rat_steps,
            "deletions": self.deletions, "derived_empty": self.derived_empty,
            "detail": self.detail, "elapsed_ms": round(self.elapsed_ms, 2),
        }


# ---------------------------------------------------------------------------


def parse_proof(lines):
    """['d 1 -2 0', '3 0'] -> [('d', [1,-2]), ('a', [3])]"""
    ops = []
    for raw in lines:
        s = raw.strip()
        if not s or s.startswith("c"):
            continue
        kind = "a"
        if s[0] == "d":
            kind = "d"
            s = s[1:]
        lits = [int(t) for t in s.split()]
        if lits and lits[-1] == 0:
            lits.pop()
        if 0 in lits:
            # One lemma per line, ended by 0. A 0 INSIDE a line is not a
            # literal, and reading `1 0 2 0` as the clause {1, 0, 2} would
            # hand the propagation a variable that does not exist.
            raise ValueError("malformed DRAT line (a 0 before its end): " + raw.strip())
        ops.append((kind, lits))
    return ops


class _Formula:
    """Clausulas activas con indice de ocurrencias."""

    def __init__(self, clauses):
        self.clauses: list = [list(c) for c in clauses]
        self.occ: dict = {}
        for i in range(len(self.clauses)):
            self._index(i)

    def _index(self, i):
        for l in self.clauses[i]:
            self.occ.setdefault(l, set()).add(i)

    def add(self, clause) -> int:
        self.clauses.append(list(clause))
        i = len(self.clauses) - 1
        self._index(i)
        return i

    def delete(self, clause) -> bool:
        want = frozenset(clause)
        if not want:
            return False
        for i in list(self.occ.get(next(iter(want)), ())):
            c = self.clauses[i]
            if c is not None and frozenset(c) == want:
                for l in c:
                    self.occ[l].discard(i)
                self.clauses[i] = None
                return True
        return False

    def propagate(self, assume) -> bool:
        """Propagacion unitaria. True si se deriva conflicto."""
        clauses = self.clauses
        n = len(clauses)
        assign: dict = {}
        sat = bytearray(n)
        cnt = [0] * n
        queue: list = []

        for i, c in enumerate(clauses):
            if c is None:
                cnt[i] = -1
                continue
            cnt[i] = len(c)
            if not c:
                return True              # la clausula vacia ya esta presente
            if len(c) == 1:
                queue.append(c[0])
        queue.extend(assume)

        while queue:
            lit = queue.pop()
            v, val = abs(lit), lit > 0
            prev = assign.get(v)
            if prev is not None:
                if prev != val:
                    return True
                continue
            assign[v] = val

            for i in self.occ.get(lit, ()):
                if clauses[i] is not None:
                    sat[i] = 1
            for i in self.occ.get(-lit, ()):
                if clauses[i] is None or sat[i]:
                    continue
                cnt[i] -= 1
                if cnt[i] == 0:
                    return True
                if cnt[i] == 1:
                    rem = None
                    for l2 in clauses[i]:
                        v2 = abs(l2)
                        a2 = assign.get(v2)
                        if a2 is None:
                            rem = l2
                            break
                        if a2 == (l2 > 0):
                            sat[i] = 1
                            rem = None
                            break
                    if rem is not None:
                        queue.append(rem)
        return False


def _is_rup(F: _Formula, clause) -> bool:
    return F.propagate([-l for l in clause])


def _is_rat(F: _Formula, clause) -> bool:
    if not clause:
        return False
    pivot = clause[0]
    cset = set(clause)
    for i in list(F.occ.get(-pivot, ())):
        D = F.clauses[i]
        if D is None:
            continue
        resolvent = cset | (set(D) - {-pivot})
        if any(-l in resolvent for l in resolvent):
            continue  # resolvente tautologico: se cumple trivialmente
        if not _is_rup(F, resolvent):
            return False
    return True


def check(clauses, proof_lines, timeout_s: float = 60.0) -> DratReport:
    """Verifica la prueba hacia adelante. Sin solver, solo propagacion."""
    t0 = time.perf_counter()
    try:
        ops = parse_proof(proof_lines)
    except ValueError as e:
        return DratReport(False, "drup-python", 0, 0, 0, 0, False, str(e),
                          (time.perf_counter() - t0) * 1000)
    F = _Formula(clauses)
    rup = rat = dels = 0
    derived_empty = False

    for k, (kind, lits) in enumerate(ops):
        if time.perf_counter() - t0 > timeout_s:
            return DratReport(
                False, "drup-python", k, rup, rat, dels, derived_empty,
                "se agoto el tiempo del verificador en el paso {}/{}".format(k, len(ops)),
                (time.perf_counter() - t0) * 1000,
            )
        if kind == "d":
            F.delete(lits)
            dels += 1
            continue
        if _is_rup(F, lits):
            rup += 1
        elif _is_rat(F, lits):
            rat += 1
        else:
            return DratReport(
                False, "drup-python", k, rup, rat, dels, derived_empty,
                _t("drup.bad_step", k=k, lits=lits),
                (time.perf_counter() - t0) * 1000,
            )
        F.add(lits)
        if not lits:
            derived_empty = True
            break

    if not derived_empty:
        # Una prueba puede ser vacia o no cerrar con la clausula vacia si la
        # formula ya es refutable por propagacion unitaria. Eso es legitimo.
        derived_empty = F.propagate([])

    ms = (time.perf_counter() - t0) * 1000
    if not derived_empty:
        return DratReport(False, "drup-python", len(ops), rup, rat, dels, False,
                          _t("drup.no_empty"), ms)
    return DratReport(True, "drup-python", len(ops), rup, rat, dels, True,
                      _t("drup.steps", rup=rup, rat=rat, dels=dels), ms)


# ---------------------------------------------------------------------------


def drat_trim_available() -> bool:
    return shutil.which("drat-trim") is not None


def check_with_drat_trim(dimacs: str, proof_lines, timeout_s: float = 60.0) -> DratReport:
    """Segunda opinion con el verificador de referencia, si esta instalado."""
    t0 = time.perf_counter()
    exe = shutil.which("drat-trim")
    if exe is None:
        return DratReport(False, "drat-trim", detail="drat-trim no esta en el PATH")
    with tempfile.TemporaryDirectory() as d:
        cnf_p, prf_p = Path(d) / "f.cnf", Path(d) / "f.drat"
        cnf_p.write_text(dimacs, encoding="utf-8")
        prf_p.write_text("\n".join(proof_lines) + "\n", encoding="utf-8")
        try:
            r = subprocess.run([exe, str(cnf_p), str(prf_p)], capture_output=True,
                               text=True, timeout=timeout_s)
        except subprocess.TimeoutExpired:
            return DratReport(False, "drat-trim", detail="drat-trim se paso del tiempo")
    ok = "s VERIFIED" in r.stdout
    return DratReport(ok, "drat-trim", detail=r.stdout.strip().splitlines()[-1] if r.stdout else "",
                      derived_empty=ok, elapsed_ms=(time.perf_counter() - t0) * 1000)
