"""Verificador DRUP/DRAT en Python puro.

Un certificado no vale nada si para comprobarlo hay que instalar otra cosa.
Aqui la comprobacion es propagacion unitaria y nada mas: no interviene ningun
SAT solver, asi que el certificado no depende de confiar en el que lo produjo.

Se comprueba RUP en cada paso y, si falla, RAT sobre el literal pivote (los
solvers con inprocesamiento emiten pasos RAT). Si `drat-trim` esta en el PATH
se puede usar como segunda opinion.

0.37: LITERALES VIGILADOS Y NUCLEO. Hasta 0.36 cada paso reiniciaba un
contador por clausula -- O(|F|) por paso -- y comprobaba todos los lemas: una
prueba de 23116 pasos del palomar de 9 no cabia en 10 minutos. Ahora cada
clausula vigila dos literales, las asignaciones de nivel 0 se conservan, y la
prueba se recorre hacia atras comprobando solo los lemas de los que depende la
refutacion (ver `check`). La eliminacion de una clausula que forzo una
asignacion de nivel 0 se ignora, como en drat-trim, y se cuenta en el
informe: cada clausula conservada se siguio de la formula (o preserva su
satisfacibilidad, si es RAT), asi que conservarla no puede refutar una
formula satisfacible. `check_simple` es el verificador anterior, para
contrastar.
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
    # Stopped by the clock, not refuted: a step not reached is not a bad step.
    timed_out: bool = False
    # deletions of a level-0 reason, ignored (see the module's docstring)
    ignored_deletions: int = 0
    total_steps: int = 0

    def to_dict(self) -> dict:
        return {
            "ok": self.ok, "checker": self.checker, "steps": self.steps,
            "rup_steps": self.rup_steps, "rat_steps": self.rat_steps,
            "deletions": self.deletions, "derived_empty": self.derived_empty,
            "detail": self.detail, "elapsed_ms": round(self.elapsed_ms, 2),
            "ignored_deletions": self.ignored_deletions,
            "timed_out": self.timed_out, "total_steps": self.total_steps,
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
        if not lits or lits[-1] != 0:
            # 0.36 read `1 -2` as the clause {1, -2}: a proof cut mid-line
            # (a full disk, a killed solver) passed as one with a last lemma
            raise ValueError(_t("drup.unterminated", line=raw.strip()[:80]))
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


def check_simple(clauses, proof_lines, timeout_s: float = 60.0) -> DratReport:
    """El verificador de 0.36: hacia adelante, O(|F|) por paso. Se conserva
    para contrastar `check` en las pruebas."""
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
                _t("drup.timeout", k=k, n=len(ops), need=_need(t0, k, len(ops), 1)),
                (time.perf_counter() - t0) * 1000, timed_out=True,
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


class _Watched:
    """Clausulas con dos literales vigilados y la traza de nivel 0.

    `val[v]` es 1, -1 o 0 y `reason[v]` la clausula que forzo `v` (-1 para
    un supuesto). Las asignaciones de un chequeo RUP se deshacen al terminar;
    las de nivel 0 (unidades, y lo que propagan) quedan. La lista de
    vigilancia de un literal guarda las clausulas que lo vigilan, y se recorre
    cuando se vuelve falso. Una entrada que ya no vigila ese literal (una
    clausula quitada y repuesta) se descarta al pasar: nunca se lee como si
    vigilara.
    """

    def __init__(self, nvars):
        self.nvars = nvars
        self.val = [0] * (nvars + 1)
        self.reason = [-1] * (nvars + 1)
        self.pos = [0] * (nvars + 1)          # posicion en la traza
        self.watches = [[] for _ in range(2 * nvars + 2)]
        self.clauses = []
        self.alive = []
        self.trail = []
        self.qhead = 0
        self.by_key = {}
        self.conflict = -2           # -2: ninguno; -1: sin clausula; i: la clausula

    def grow(self, v):
        if v > self.nvars:
            extra = v - self.nvars
            self.val.extend([0] * extra)
            self.reason.extend([-1] * extra)
            self.pos.extend([0] * extra)
            self.watches.extend([] for _ in range(2 * extra))
            self.nvars = v

    @staticmethod
    def _w(lit):
        return 2 * lit if lit > 0 else -2 * lit + 1

    def value(self, lit):
        x = self.val[lit if lit > 0 else -lit]
        return x if lit > 0 else -x

    def _assign(self, lit, why):
        v = lit if lit > 0 else -lit
        self.val[v] = 1 if lit > 0 else -1
        self.reason[v] = why
        self.pos[v] = len(self.trail)
        self.trail.append(lit)

    def new(self, lits):
        """Registra una clausula (sin vigilarla); None si es tautologia."""
        c = list(dict.fromkeys(lits))
        if any(-l in c for l in c):
            return None               # nunca restringe nada
        for l in c:
            self.grow(abs(l))
        i = len(self.clauses)
        self.clauses.append(c)
        self.alive.append(False)
        self.by_key.setdefault(tuple(sorted(c)), []).append(i)
        return i

    def attach(self, i) -> None:
        """Pone la clausula `i` en la formula; si es unitaria en el nivel 0,
        propaga, y un conflicto queda en `conflict`."""
        self.alive[i] = True
        c = self.clauses[i]
        if self.conflict != -2:
            return
        if not c:
            self.conflict = i
            return
        # vigilar los dos mejores: verdaderos o libres antes que falsos
        c.sort(key=lambda l: -self.value(l))
        if len(c) >= 2:
            self.watches[self._w(c[0])].append(i)
            self.watches[self._w(c[1])].append(i)
        a = self.value(c[0])
        if a == 1:
            return
        if a == -1:
            self.conflict = i        # todos falsos en el nivel 0
            return
        if len(c) == 1 or self.value(c[1]) == -1:
            self._assign(c[0], i)
            got = self.propagate()
            if got != -2:
                self.conflict = got

    def detach(self, i) -> None:
        """Quita la clausula `i`. Si forzaba una asignacion de nivel 0, la
        traza vuelve a antes de ella y se repropaga lo que aun se siga."""
        self.alive[i] = False
        c = self.clauses[i]
        for l in c[:2]:
            wl = self.watches[self._w(l)]
            try:
                wl.remove(i)
            except ValueError:
                pass
        cut = None
        for l in c:
            v = abs(l)
            if self.val[v] != 0 and self.reason[v] == i:
                cut = self.pos[v] if cut is None else min(cut, self.pos[v])
        if cut is not None:
            for l in self.trail[cut:]:
                v = l if l > 0 else -l
                self.val[v] = 0
                self.reason[v] = -1
            del self.trail[cut:]
            self.qhead = 0
            if self.propagate() != -2:
                self.conflict = -1   # no deberia ocurrir: lo que habia no chocaba

    def is_reason(self, i) -> bool:
        return any(self.val[abs(l)] != 0 and self.reason[abs(l)] == i
                   for l in self.clauses[i])

    def find(self, lits):
        """La clausula viva con estos literales, o None."""
        for i in self.by_key.get(tuple(sorted(dict.fromkeys(lits))), ()):
            if self.alive[i]:
                return i
        return None

    def propagate(self) -> int:
        """Desde `qhead`; la clausula en conflicto, o -2 si no lo hay."""
        val, watches, clauses, alive = self.val, self.watches, self.clauses, self.alive
        reason, pos, trail = self.reason, self.pos, self.trail
        while self.qhead < len(trail):
            lit = trail[self.qhead]
            self.qhead += 1
            false_lit = -lit
            # las clausulas que vigilan `false_lit`, ahora falso
            wl = watches[2 * false_lit if false_lit > 0 else -2 * false_lit + 1]
            j = k = 0
            n = len(wl)
            while k < n:
                i = wl[k]
                k += 1
                if not alive[i]:
                    continue                    # se borra de la lista
                c = clauses[i]
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                elif c[1] != false_lit:
                    continue                    # entrada vieja: no vigila esto
                first = c[0]
                fv = val[first if first > 0 else -first]
                if first < 0:
                    fv = -fv
                if fv == 1:
                    wl[j] = i
                    j += 1
                    continue
                moved = False
                for m in range(2, len(c)):
                    l2 = c[m]
                    x = val[l2 if l2 > 0 else -l2]
                    if l2 < 0:
                        x = -x
                    if x != -1:
                        c[1], c[m] = l2, c[1]
                        watches[2 * l2 if l2 > 0 else -2 * l2 + 1].append(i)
                        moved = True
                        break
                if moved:
                    continue
                wl[j] = i
                j += 1
                if fv == -1:
                    while k < n:                 # conflicto: el resto queda
                        wl[j] = wl[k]
                        j += 1
                        k += 1
                    del wl[j:]
                    return i
                v = first if first > 0 else -first
                val[v] = 1 if first > 0 else -1
                reason[v] = i
                pos[v] = len(trail)
                trail.append(first)
            del wl[j:]
        return -2

    def analyze(self, clause, var, core) -> None:
        """Marca en `core` las clausulas de las que depende un conflicto:
        la clausula en conflicto (o la variable que choco con un supuesto)
        y las razones de cada literal, hasta los supuestos."""
        seen = set()
        stack = []
        if clause >= 0:
            core[clause] = 1
            stack.extend(abs(l) for l in self.clauses[clause])
        if var:
            stack.append(var)
        reason, clauses = self.reason, self.clauses
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            r = reason[v]
            if r >= 0:
                core[r] = 1
                stack.extend(abs(l) for l in clauses[r])

    def rup(self, lits, core=None) -> bool:
        """¿Deriva la propagacion un conflicto al negar `lits`? Con `core`,
        marca las clausulas que uso."""
        if self.conflict != -2:
            return True
        mark, head = len(self.trail), self.qhead
        hit, clash = -2, 0
        for l in lits:
            a = self.value(l)
            if a == 1:
                clash = abs(l)        # ya verdadero: negarlo choca
                break
            if a == 0:
                self._assign(-l, -1)
        if not clash:
            hit = self.propagate()
        ok = bool(clash) or hit != -2
        if ok and core is not None:
            self.analyze(hit, clash, core)
        for l in self.trail[mark:]:
            v = l if l > 0 else -l
            self.val[v] = 0
            self.reason[v] = -1
        del self.trail[mark:]
        self.qhead = head
        return ok

    def rat(self, lits, core=None) -> bool:
        """RAT sobre el primer literal: cada resolvente con una clausula
        viva que contiene su negacion es RUP. Raro en la practica, y por eso
        recorre las clausulas en vez de mantener un indice de ocurrencias."""
        if not lits:
            return False
        pivot = lits[0]
        cset = set(lits)
        for i, D in enumerate(self.clauses):
            if not self.alive[i] or -pivot not in D:
                continue
            res = cset | (set(D) - {-pivot})
            if any(-l in res for l in res):
                continue
            if core is not None:
                core[i] = 1
            if not self.rup(list(res), core):
                return False
        return True


def _need(t0, done, total, passes) -> int:
    """Segundos que probablemente basten para terminar, al ritmo medido
    (con margen): lo que el aviso de tiempo agotado propone pedir."""
    spent = time.perf_counter() - t0
    rate = spent / max(done, 1)
    return int(rate * total * passes * 1.5) + 1


def check(clauses, proof_lines, timeout_s: float = 60.0) -> DratReport:
    """Verifica la prueba HACIA ATRAS, solo el nucleo.

    Hacia adelante, sin chequear nada: se agregan los lemas y se aplican las
    eliminaciones hasta que la propagacion de nivel 0 choca. Ese conflicto
    marca las clausulas de las que depende; luego, de atras hacia adelante,
    cada lema marcado se quita y se comprueba RUP (o RAT) contra lo que habia
    antes de el, marcando a su vez lo que usa. Un lema no marcado no
    interviene en la refutacion y no se comprueba: es lo que drat-trim hace,
    y por que una prueba de CDCL -- con muchos lemas que nadie uso -- cuesta
    una fraccion de su largo.
    """
    t0 = time.perf_counter()
    stop = t0 + timeout_s
    try:
        ops = parse_proof(proof_lines)
    except ValueError as e:
        return DratReport(False, "drup-python", 0, 0, 0, 0, False, str(e),
                          (time.perf_counter() - t0) * 1000)
    n = len(ops)
    nv = 0
    for c in clauses:
        for l in c:
            nv = max(nv, abs(l))
    F = _Watched(nv)
    for c in clauses:
        i = F.new(c)
        if i is not None:
            F.attach(i)
    dels = ignored = 0

    def report(ok, steps, rup, rat, detail, **kw):
        return DratReport(ok, "drup-python", steps, rup, rat, dels, ok, detail,
                          (time.perf_counter() - t0) * 1000, ignored_deletions=ignored,
                          total_steps=n, **kw)

    # --- hacia adelante: hasta el conflicto ------------------------------------
    ids = [None] * n               # la clausula de cada paso (o la eliminada)
    end = -1                       # el paso cuyo lema cerro la refutacion
    if F.conflict == -2:
        for k, (kind, lits) in enumerate(ops):
            if (k & 255) == 0 and time.perf_counter() > stop:
                return report(False, 0, 0, 0, _t("drup.timeout_forward", k=k, n=n,
                                                 need=_need(t0, k, n, 2)),
                              timed_out=True)
            if kind == "d":
                dels += 1
                i = F.find(lits)
                if i is None:
                    continue
                if F.is_reason(i):
                    ignored += 1
                    continue
                F.detach(i)
                ids[k] = i
                continue
            if not lits:
                # la clausula vacia es RUP solo si el nivel 0 ya choca, y
                # eso se habria visto al agregar el lema anterior
                return report(False, k, 0, 0, _t("drup.bad_step", k=k, lits=lits))
            i = F.new(lits)
            ids[k] = i
            if i is None:
                continue
            F.attach(i)
            if F.conflict != -2:
                end = k
                break
        else:
            return report(False, n, 0, 0, _t("drup.no_empty"))
    core = bytearray(len(F.clauses) + 1)
    if F.conflict >= 0:
        F.analyze(F.conflict, 0, core)
    F.conflict = -2

    # --- hacia atras: solo lo marcado --------------------------------------------
    rup = rat = 0
    checked = 0
    for k in range(end, -1, -1):
        if ((end - k) & 63) == 0 and time.perf_counter() > stop:
            return report(False, checked, rup, rat,
                          _t("drup.timeout", k=end - k, n=end + 1,
                             need=_need(t0, end - k, end + 1, 1)), timed_out=True)
        kind, lits = ops[k]
        i = ids[k]
        if i is None:
            continue
        if kind == "d":
            F.attach(i)                # vuelve lo que se habia eliminado
        else:
            F.detach(i)
        if F.conflict != -2:
            # The formula before step k did not contradict itself at level 0
            # -- the replay went past it. A conflict here is a fault of this
            # checker, and `rup` would then accept anything: fail closed.
            return report(False, checked, rup, rat, _t("drup.internal", k=k))
        if kind == "d" or not core[i]:
            continue
        checked += 1
        if F.rup(lits, core):
            rup += 1
        elif F.rat(lits, core):
            rat += 1
        else:
            return report(False, checked, rup, rat, _t("drup.bad_step", k=k, lits=lits))
    outside = sum(1 for k in range(end + 1) if ops[k][0] == "a" and ids[k] is not None
                  and not core[ids[k]])
    detail = _t("drup.core_steps", rup=rup, rat=rat, outside=outside, dels=dels)
    if ignored:
        detail += "; " + _t("drup.ignored", n=ignored)
    return report(True, checked, rup, rat, detail)


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
            return DratReport(False, "drat-trim", detail="drat-trim se paso del tiempo",
                              timed_out=True)
    ok = "s VERIFIED" in r.stdout
    return DratReport(ok, "drat-trim", detail=r.stdout.strip().splitlines()[-1] if r.stdout else "",
                      derived_empty=ok, elapsed_ms=(time.perf_counter() - t0) * 1000)
