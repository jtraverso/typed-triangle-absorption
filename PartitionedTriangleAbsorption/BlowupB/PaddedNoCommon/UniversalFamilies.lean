/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Lattice
public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Supersets

@[expose] public section

/-!
# `UniversalCert` for the six bases and the fourteen census families

Bases: `universalCert_of_trivial_walk` with the witness bound `|F| (2·168 + 4)` of
`PaddedNoCommon/Lattice.lean` (at most `8 · 340 = 2720`; terminal order `≤ 291652`, terminal size
`≤ 882600`, both `≤ 2^21`).

Census families: a family `F ⊇ F0` with the same allowed pairs inherits the universal absorbers of
`F0` (`universalCert_of_overBase`): an `F0`-decomposition is an `F`-decomposition, and an
`F`-divisible loopless set is `Even3` with allowed support, hence `F0`-divisible by the trivial
lattice of `F0`.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral

theorem universalCert_of_base (F : Finset (Multiset (Fin 4))) (hF : BaseFacts F)
    (htriv : TrivialLattice F) (hB : WitnessBoundK F 168 (F.card * (2 * 168 + 4)))
    (hcard8 : F.card ≤ 8) : UniversalCert F := by
  refine universalCert_of_trivial_walk F hF.card hF.three hF.walk htriv _ hB ?_ ?_
  · unfold terminalOrder; have := Nat.mul_le_mul_right (2 * 168 + 4) hcard8; omega
  · unfold terminalSize; have := Nat.mul_le_mul_right (2 * 168 + 4) hcard8; omega

theorem universalCert_FnA : UniversalCert FnA :=
  universalCert_of_base FnA baseFacts_FnA (lattice_FnA 168).1 (lattice_FnA 168).2
    (by unfold FnA; decide)
theorem universalCert_FnB : UniversalCert FnB :=
  universalCert_of_base FnB baseFacts_FnB (lattice_FnB 168).1 (lattice_FnB 168).2
    (by unfold FnB; decide)
theorem universalCert_FnC : UniversalCert FnC :=
  universalCert_of_base FnC baseFacts_FnC (lattice_FnC 168).1 (lattice_FnC 168).2
    (by unfold FnC; decide)
theorem universalCert_FnD : UniversalCert FnD :=
  universalCert_of_base FnD baseFacts_FnD (lattice_FnD 168).1 (lattice_FnD 168).2
    (by unfold FnD; decide)
theorem universalCert_FnE : UniversalCert FnE :=
  universalCert_of_base FnE baseFacts_FnE (lattice_FnE 168).1 (lattice_FnE 168).2
    (by unfold FnE; decide)
theorem universalCert_FnF : UniversalCert FnF :=
  universalCert_of_base FnF baseFacts_FnF (lattice_FnF 168).1 (lattice_FnF 168).2
    (by unfold FnF; decide)

theorem allowed_fun_eq_of_overBase {F0 F : Finset (Multiset (Fin 4))} (h : OverBase F0 F) :
    (fun i j : Fin 4 => ∃ k, Link F i j k) = (fun i j => ∃ k, Link F0 i j k) :=
  funext fun i => funext fun j => propext (h.allowed i j)

/-- **Transfer of universal absorbers to a superset with the same allowed pairs.** -/
theorem universalCert_of_overBase {F0 F : Finset (Multiset (Fin 4))} (h : OverBase F0 F)
    (htriv : TrivialLattice F0) (hU : UniversalCert F0) : UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hG' : ∀ u v, G.Adj u v → ∃ k, Link F0 (p u) (p v) k :=
    fun u v huv => (h.allowed _ _).mp (hG u v huv)
  rw [allowed_fun_eq_of_overBase h] at hs
  have U := hU V p G ω hG' hs hω hω1 hn
  intro X hXG hX
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hL⟩ := U X hXG hX
  refine ⟨A, hAG, hAX, PaddedFbit.hasDecomp_of_subset h.sub hAdec, hAdeg, ?_⟩
  intro L hLX hLdiv
  have hloop : ∀ e ∈ L, ¬ e.IsDiag :=
    fun e he => G.not_isDiag_of_mem_edgeFinset (hXG (hLX he))
  have hcard := h.facts.card_three
  have h3 := PaddedTrivial.even3_of_isIntDiv hcard p hloop hLdiv
  have hact : ActiveEdges F0 p L := fun a b hab =>
    (h.allowed _ _).mp (active_of_isIntDiv hcard hLdiv a b hab)
  exact PaddedFbit.hasDecomp_of_subset h.sub (hL L hLX ((htriv p L hloop).mpr ⟨hact, h3⟩))

end PaddedNoCommon

#print axioms PaddedNoCommon.universalCert_FnA
#print axioms PaddedNoCommon.universalCert_FnB
#print axioms PaddedNoCommon.universalCert_FnC
#print axioms PaddedNoCommon.universalCert_FnD
#print axioms PaddedNoCommon.universalCert_FnE
#print axioms PaddedNoCommon.universalCert_FnF
#print axioms PaddedNoCommon.universalCert_of_overBase
