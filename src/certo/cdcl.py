"""CDCL con registro DRUP.

Por que un solver propio habiendo pysat: el proof logging de pysat no
funciona en Windows (pasa un tempfile de Python a la extension C y el buffer
del CRT nunca se vuelve a leer: devuelve 0 lineas), y el binario de z3 no
escribe el fichero DRAT. Sin prueba, `cases` no tiene certificado, que es lo
unico que justifica el comando.

Este solver es lento comparado con cadical, pero:
  - funciona en cualquier plataforma, sin binarios externos;
  - la numeracion de variables es la del DIMACS de entrada, sin traducciones;
  - y si tuviera un fallo, el verificador DRUP lo caza: una prueba mal
    formada no pasa la comprobacion RUP. El checker audita al solver.

Para instancias grandes, usa un binario externo (cadical, kissat) con
`--solver-binary`: lee DIMACS y escribe DRAT con la misma numeracion.

Implementacion: dos literales vigilados, aprendizaje 1UIP, VSIDS con decaimiento,
reinicios geometricos, y (0.37) reduccion de la base de aprendidas por LBD:
cada tanto se borra la mitad menos util, y cada borrado va a la prueba como
`d ...`. Sin eso la formula solo crecia, y resolver y verificar el palomar de
9 costaban lo mismo: minutos.
"""
from __future__ import annotations

import time
from dataclasses import dataclass

UNSAT, SAT, UNKNOWN = "unsat", "sat", "unknown"


@dataclass
class CdclResult:
    status: str
    model: list | None = None      # literales verdaderos
    proof: list | None = None      # lineas DRUP
    conflicts: int = 0
    decisions: int = 0
    propagations: int = 0
    elapsed_ms: float = 0.0
    detail: str = ""


class Cdcl:
    def __init__(self, nvars: int, clauses, emit_proof: bool = True):
        self.n = nvars
        self.emit_proof = emit_proof
        self.proof: list = []

        self.clauses: list = []
        self.watches: dict = {}
        self.value: list = [0] * (nvars + 1)     # 0 sin asignar, 1 cierto, -1 falso
        self.level: list = [0] * (nvars + 1)
        self.reason: list = [None] * (nvars + 1)
        self.activity: list = [0.0] * (nvars + 1)
        self.trail: list = []
        self.trail_lim: list = []
        self.qhead = 0
        self.dl = 0
        self.var_inc = 1.0
        self.conflicts = self.decisions = self.propagations = 0
        self.ok = True
        self.learnts: list = []                  # indices de aprendidas vivas
        self.lbd: dict = {}
        self.deleted = 0

        for c in clauses:
            if not self._add_original(c):
                self.ok = False

    # -- clausulas ---------------------------------------------------------

    def _watch(self, ci):
        c = self.clauses[ci]
        self.watches.setdefault(c[0], []).append(ci)
        if len(c) > 1:
            self.watches.setdefault(c[1], []).append(ci)

    def _add_original(self, clause) -> bool:
        cl = list(dict.fromkeys(clause))
        if any(-l in cl for l in cl):
            return True                      # tautologia
        if not cl:
            return False
        if len(cl) == 1:
            return self._enqueue(cl[0], None)
        self.clauses.append(cl)
        self._watch(len(self.clauses) - 1)
        return True

    def _add_learnt(self, cl) -> int:
        self.clauses.append(list(cl))
        ci = len(self.clauses) - 1
        self._watch(ci)
        self.learnts.append(ci)
        self.lbd[ci] = len({self.level[abs(l)] for l in cl})
        return ci

    def _reduce(self):
        """Borra la mitad de las aprendidas de LBD > 2 que no son razon de
        nada, las de peor LBD primero, y lo anota en la prueba."""
        clauses, value, reason = self.clauses, self.value, self.reason
        live, cand = [], []
        for ci in self.learnts:
            c = clauses[ci]
            if c is None:
                continue
            live.append(ci)
            v = abs(c[0])
            locked = value[v] != 0 and reason[v] == ci
            if self.lbd[ci] > 2 and not locked:
                cand.append(ci)
        cand.sort(key=lambda ci: (self.lbd[ci], len(clauses[ci])), reverse=True)
        gone = set(cand[:len(cand) // 2])
        for ci in gone:
            if self.emit_proof:
                self.proof.append("d " + " ".join(map(str, clauses[ci])) + " 0")
            clauses[ci] = None           # sus vigilancias se caen al pasar
            del self.lbd[ci]
        self.deleted += len(gone)
        self.learnts = [ci for ci in live if ci not in gone]

    def _log(self, cl):
        if self.emit_proof:
            self.proof.append(" ".join(map(str, cl)) + " 0")

    # -- asignacion --------------------------------------------------------

    def _lit_value(self, l):
        v = self.value[abs(l)]
        return 0 if v == 0 else (v if l > 0 else -v)

    def _enqueue(self, l, reason) -> bool:
        val = self._lit_value(l)
        if val == 1:
            return True
        if val == -1:
            return False
        v = abs(l)
        self.value[v] = 1 if l > 0 else -1
        self.level[v] = self.dl
        self.reason[v] = reason
        self.trail.append(l)
        return True

    def _propagate(self):
        value, clauses, watches = self.value, self.clauses, self.watches
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            self.propagations += 1
            ws = watches.get(-p, [])
            keep, i = [], 0
            while i < len(ws):
                ci = ws[i]
                i += 1
                c = clauses[ci]
                if c is None:
                    continue                 # borrada por `_reduce`
                if c[0] == -p:
                    c[0], c[1] = c[1], c[0]
                l0 = c[0]
                x = value[l0 if l0 > 0 else -l0]
                if (x if l0 > 0 else -x) == 1:
                    keep.append(ci)
                    continue
                found = False
                for k in range(2, len(c)):
                    lk = c[k]
                    x = value[lk if lk > 0 else -lk]
                    if (x if lk > 0 else -x) != -1:
                        c[1], c[k] = lk, c[1]
                        watches.setdefault(lk, []).append(ci)
                        found = True
                        break
                if found:
                    continue
                keep.append(ci)
                if not self._enqueue(c[0], ci):
                    self.watches[-p] = keep + ws[i:]
                    return ci
            self.watches[-p] = keep
        return None

    # -- aprendizaje 1UIP --------------------------------------------------

    def _analyze(self, confl_ci):
        seen = bytearray(self.n + 1)
        learnt = [0]
        counter = 0
        p = None
        idx = len(self.trail) - 1
        cl = self.clauses[confl_ci]

        while True:
            for q in cl:
                if p is not None and q == p:
                    continue
                v = abs(q)
                if seen[v] or self.level[v] == 0:
                    continue
                seen[v] = 1
                self._bump(v)
                if self.level[v] >= self.dl:
                    counter += 1
                else:
                    learnt.append(q)
            while not seen[abs(self.trail[idx])]:
                idx -= 1
            p = self.trail[idx]
            idx -= 1
            seen[abs(p)] = 0
            counter -= 1
            if counter <= 0:
                break
            cl = self.clauses[self.reason[abs(p)]]

        learnt[0] = -p
        bt = 0 if len(learnt) == 1 else max(self.level[abs(l)] for l in learnt[1:])
        if len(learnt) > 1:
            # el literal de mayor nivel va en la segunda posicion vigilada
            j = max(range(1, len(learnt)), key=lambda k: self.level[abs(learnt[k])])
            learnt[1], learnt[j] = learnt[j], learnt[1]
        return learnt, bt

    def _bump(self, v):
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            for i in range(1, self.n + 1):
                self.activity[i] *= 1e-100
            self.var_inc *= 1e-100

    # -- busqueda ----------------------------------------------------------

    def _backtrack(self, level):
        if self.dl <= level:
            return
        lim = self.trail_lim[level]
        for l in self.trail[lim:]:
            v = abs(l)
            self.value[v] = 0
            self.reason[v] = None
            self.level[v] = 0
        del self.trail[lim:]
        del self.trail_lim[level:]
        self.qhead = len(self.trail)
        self.dl = level

    def _decide(self):
        best, ba = 0, -1.0
        for v in range(1, self.n + 1):
            if self.value[v] == 0 and self.activity[v] > ba:
                best, ba = v, self.activity[v]
        if best == 0:
            return False
        self.decisions += 1
        self.dl += 1
        self.trail_lim.append(len(self.trail))
        self._enqueue(-best, None)   # polaridad negativa por defecto
        return True

    def solve(self, max_conflicts: int = 10_000_000,
              timeout_s: float = 60.0) -> CdclResult:
        t0 = time.perf_counter()
        if not self.ok:
            self._log([])
            return CdclResult(UNSAT, None, self.proof, 0, 0, 0,
                              (time.perf_counter() - t0) * 1000,
                              "contradiccion entre clausulas unitarias de entrada")

        restart_limit, restart_base = 100, 100
        reduce_at, reduce_step = 2000, 2000
        while True:
            confl = self._propagate()
            if confl is not None:
                self.conflicts += 1
                if self.dl == 0:
                    self._log([])
                    return CdclResult(UNSAT, None, self.proof, self.conflicts,
                                      self.decisions, self.propagations,
                                      (time.perf_counter() - t0) * 1000)
                learnt, bt = self._analyze(confl)
                self._log(learnt)
                self._backtrack(bt)
                if len(learnt) == 1:
                    self._enqueue(learnt[0], None)
                else:
                    ci = self._add_learnt(learnt)
                    self._enqueue(learnt[0], ci)
                self.var_inc /= 0.95
                if self.conflicts >= reduce_at:
                    reduce_step += 300
                    reduce_at = self.conflicts + reduce_step
                    self._reduce()
                if self.conflicts >= max_conflicts:
                    return CdclResult(UNKNOWN, None, None, self.conflicts,
                                      self.decisions, self.propagations,
                                      (time.perf_counter() - t0) * 1000,
                                      "presupuesto de conflictos agotado")
                if self.conflicts >= restart_limit:
                    restart_base = int(restart_base * 1.5)
                    restart_limit = self.conflicts + restart_base
                    self._backtrack(0)
            else:
                if time.perf_counter() - t0 > timeout_s:
                    return CdclResult(UNKNOWN, None, None, self.conflicts,
                                      self.decisions, self.propagations,
                                      (time.perf_counter() - t0) * 1000,
                                      "tiempo agotado")
                if not self._decide():
                    model = [v if self.value[v] == 1 else -v
                             for v in range(1, self.n + 1)]
                    return CdclResult(SAT, model, None, self.conflicts,
                                      self.decisions, self.propagations,
                                      (time.perf_counter() - t0) * 1000)


def solve(nvars, clauses, max_conflicts=10_000_000, timeout_s=60.0,
          emit_proof=True) -> CdclResult:
    return Cdcl(nvars, clauses, emit_proof).solve(max_conflicts, timeout_s)
