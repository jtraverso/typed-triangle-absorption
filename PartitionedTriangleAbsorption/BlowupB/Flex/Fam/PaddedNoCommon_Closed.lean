/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Closed
public import PartitionedTriangleAbsorption.BlowupB.Flex.Fam.PaddedNoCommon_UniversalFamilies

@[expose] public section

/-!
# Flexible certificates of the census families over a base (`NC5`, `NC9`)

`universalCertFlex_of_overBase`: the flexible version of `PaddedNoCommon.universalCert_of_overBase`
(a family `F ⊇ F0` with the same allowed pairs inherits the universal absorbers of `F0` when the
lattice of `F0` is trivial). Whole-family certificates, hence component certificates for the
constant labelling.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral

theorem universalCertFlex_of_overBase {F0 F : Finset (Multiset (Fin 4))} (h : OverBase F0 F)
    (htriv : TrivialLattice F0) (hU : PartitionedTriangleAbsorption.BlowupB.Flex.UniversalCertFlex F0) :
    PartitionedTriangleAbsorption.BlowupB.Flex.UniversalCertFlex F := by
  intro V _ _ p G _ ω δ ρ hfl hG hs
  have hG' : ∀ u v, G.Adj u v → ∃ k, Link F0 (p u) (p v) k :=
    fun u v huv => (h.allowed _ _).mp (hG u v huv)
  rw [allowed_fun_eq_of_overBase h] at hs
  have U := hU V p G ω δ ρ hfl hG' hs
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

theorem universalFlex_NC5 : PartitionedTriangleAbsorption.BlowupB.Flex.UniversalCertFlex NC5 :=
  universalCertFlex_of_overBase overBase_NC5 (lattice_FnB 168).1 universalFlex_FnB

theorem compFlex_NC5 : ∀ k, PartitionedTriangleAbsorption.BlowupB.Flex.ComponentUniversalCertFlex NC5
    (fun _ => 0) k :=
  PartitionedTriangleAbsorption.BlowupB.Flex.compFlex_of_universalFlex universalFlex_NC5

theorem universalFlex_NC9 : PartitionedTriangleAbsorption.BlowupB.Flex.UniversalCertFlex NC9 :=
  universalCertFlex_of_overBase overBase_NC9 (lattice_FnC 168).1 universalFlex_FnC

theorem compFlex_NC9 : ∀ k, PartitionedTriangleAbsorption.BlowupB.Flex.ComponentUniversalCertFlex NC9
    (fun _ => 0) k :=
  PartitionedTriangleAbsorption.BlowupB.Flex.compFlex_of_universalFlex universalFlex_NC9

end PaddedNoCommon

#print axioms PaddedNoCommon.compFlex_NC5
#print axioms PaddedNoCommon.compFlex_NC9
