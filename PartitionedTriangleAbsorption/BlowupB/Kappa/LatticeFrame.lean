/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.LatticeFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Collapse

@[expose] public section

/-! # Aristotle's scalar lattice frame under `FiveStepLinks`

Copies of `PaddedNoCommon.trivialLattice_of_scalar` and `lattice_inputs_of_scalar` with
`isIntDiv_iff` (ThreeStepLinks) replaced by `isIntDiv_iff_five`. -/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12 PaddedGeneral

theorem trivialLattice_of_scalar_five (F : Finset (Multiset (Fin 4))) (hfive : FiveStepLinks F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u → ∃ c, LatEq F u c) : TrivialLattice F := by
  intro V _ _ p E hloop
  constructor
  · intro h
    exact ⟨active_of_isIntDiv hcard h, PaddedTrivial.even3_of_isIntDiv hcard p hloop h⟩
  · rintro ⟨hact, h3, hev⟩
    rw [isIntDiv_iff_five hfive hcard hloop]
    refine ⟨hact, hev, ?_⟩
    have hS : ScalarHyp F (unorderedCount p E) :=
      ⟨unorderedCount_swap p E, unorderedCount_nonneg p E, counts_forbid hact,
        counts_parity p E hloop hev, by rw [totalU_counts]; exact_mod_cast h3⟩
    obtain ⟨c, hc⟩ := hsol _ hS
    exact ⟨c, (latEq_counts_iff F p E c).mp hc⟩

theorem lattice_inputs_of_scalar_five (F : Finset (Multiset (Fin 4))) (hfive : FiveStepLinks F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -(2 * totalU u + 4) ≤ c τ) (K : ℕ) :
    TrivialLattice F ∧ WitnessBoundK F K (F.card * (2 * K + 4)) := by
  refine ⟨trivialLattice_of_scalar_five F hfive hcard fun u hu => ?_,
    witnessBound_of_scalar F hcard K _ fun u hu hK => ?_⟩
  · obtain ⟨c, hc, -⟩ := hsol u hu; exact ⟨c, hc⟩
  · obtain ⟨c, hc, hm⟩ := hsol u hu
    refine ⟨c, hc, negativeMass_le_of_lower F c _ fun τ hτ => ?_⟩
    have := hm τ hτ
    push_cast
    omega

end PaddedNoCommon

#print axioms PaddedNoCommon.lattice_inputs_of_scalar_five
