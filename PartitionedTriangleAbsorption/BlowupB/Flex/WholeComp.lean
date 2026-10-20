/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.WholeCerts
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.UniversalFamilies

@[expose] public section

/-!
# Whole-family flexible certificates as component certificates

`compFlex_of_universalFlex`: a whole-family flexible certificate is a flexible component
certificate for the constant labelling `fun _ => 0` (one component, every class). Also the
flexible version of `PaddedNoCommon.universalCert_of_base`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedComponents PaddedNoCommon

theorem compFlex_of_universalFlex {F : Finset (Multiset (Fin 4))} (h : UniversalCertFlex F) :
    ∀ k, ComponentUniversalCertFlex F (fun _ => 0) k := by
  intro k
  by_cases hk : k = 0
  · subst hk
    intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX _
    obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ := h V p G ω δ ρ hfl hG hs X hXG hX
    refine ⟨A, hAG, hAX, fun e _ => ?_, hAdec, hAdeg, hAL⟩
    induction e using Sym2.ind with
    | _ a b => exact (insideE_mk p (fun _ => 0) 0 a b).mpr ⟨rfl, rfl⟩
  · exact componentUniversalCertFlex_empty F (fun _ => 0) k (fun _ h0 => hk h0.symm)

theorem compLabel_const (F : Finset (Multiset (Fin 4))) : CompLabel F (fun _ => 0) :=
  fun _ _ _ => rfl

theorem typesInside_const (F : Finset (Multiset (Fin 4))) : TypesInside F (fun _ => 0) :=
  fun _ _ _ _ _ _ => rfl

theorem universalCert_of_base_flex (F : Finset (Multiset (Fin 4))) (hF : BaseFacts F)
    (htriv : TrivialLattice F) (hB : WitnessBoundK F 168 (F.card * (2 * 168 + 4)))
    (hcard8 : F.card ≤ 8) : UniversalCertFlex F := by
  refine universalCert_of_trivial_walk_flex F hF.card hF.three hF.walk htriv _ hB ?_ ?_
  · unfold terminalOrder; have := Nat.mul_le_mul_right (2 * 168 + 4) hcard8; omega
  · unfold terminalSize; have := Nat.mul_le_mul_right (2 * 168 + 4) hcard8; omega

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.compFlex_of_universalFlex
#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.universalCert_of_base_flex
