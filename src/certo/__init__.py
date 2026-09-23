"""certo: a laboratory for supporting mathematical proofs.

Three cross-cutting rules, true of every command:

  1. Every command returns a certificate, or says explicitly why not.
  2. Six result states: unsat / sat / unknown_solver / timeout /
     resource_exhausted / out_of_theory. Only the first two are conclusive;
     the rest mean "no answer", each for a different reason.
  3. Determinism by work budget (z3 rlimit, SAT conflict budget), not by
     clock, so the same command gives the same answer on another machine.
     That covers our engines, not a user-supplied predicate.
"""
from __future__ import annotations

from .certificate import Certificate, VerifyReport, verify
from .cnf import CNF, CNFSpec
from .graphs import Graph
from . import api, doctor, reducers
from .structures import SetFamily, family_from_masks, mask_to_set, set_to_mask
from .packing import PackingSpec, loads_from_dual
from .i18n import set_lang, t
from .limits import Limits
from .polynomials import Poly
from .spec import (BisectSpec, BoundSpec, DomainSpec, IdealSpec,
                   InductSpec, Lemma, LPSpec, NumberSpec, OrderSpec,
                   BindSpec, ConeSpec, CoverSpec, SemigroupSpec, ProfileSpec, CycleSpec, EliminateSpec, EquitableQuotientSpec, LinearSystemSpec, MatrixSpec, ParametricSymmetrySpec, EntrySpec, FamilySpec, MomentSpec, ParametricSpec, SymmetrySpec, PeakSpec, RatioSpec,
                   SOSSpec,
                   MultiSpec, Outcome, ProofSpec, Spec, SweepSpec,
                   SynthSpec, load_spec)
from .status import Result, Status, Verdict

__version__ = "0.15.2"

__all__ = [
    "Spec", "SynthSpec", "LPSpec", "SweepSpec", "CNF", "CNFSpec",
    "BisectSpec", "BoundSpec", "DomainSpec", "IdealSpec", "InductSpec",
    "NumberSpec", "OrderSpec", "SOSSpec", "EliminateSpec", "ParametricSpec", "PeakSpec", "FamilySpec", "RatioSpec", "MomentSpec", "EntrySpec", "SymmetrySpec", "CoverSpec", "ConeSpec", "SemigroupSpec", "ProfileSpec", "CycleSpec", "BindSpec", "EquitableQuotientSpec", "MatrixSpec", "LinearSystemSpec", "ParametricSymmetrySpec", "Poly", "MultiSpec",
    "ProofSpec", "Lemma",
    "Outcome", "load_spec",
    "Limits", "Status", "Verdict", "Result",
    "Certificate", "VerifyReport", "verify",
    "Graph", "PackingSpec", "loads_from_dual", "doctor", "reducers", "SetFamily",
    "family_from_masks", "mask_to_set", "set_to_mask", "set_lang", "t",
    "api",
    "__version__",
]
