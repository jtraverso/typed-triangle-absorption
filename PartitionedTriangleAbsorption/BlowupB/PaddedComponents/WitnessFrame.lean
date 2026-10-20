/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ComponentLattice

@[expose] public section

/-!
# Witness bound with a general linear lower bound on the coefficients

`witnessBound_of_latEq_lowerK`: if every integral witness can be replaced by one whose coefficients
are at least `-(K₀ e + 4)` (`e` the number of edges), the witness bound is `|F| (K₀ K + 4)`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12 PaddedGeneral PaddedNoCommon

theorem witnessBound_of_latEq_lowerK (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (K0 : ℕ)
    (hsol : ∀ u c0, ScalarHyp F u → LatEq F u c0 →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -((K0 : ℤ) * totalU u + 4) ≤ c τ) (K : ℕ) :
    WitnessBoundK F K (F.card * (K0 * K + 4)) := by
  apply witnessBound_of_latEq F hcard K
  intro u c0 hu hc0 hK
  obtain ⟨c, hc, hm⟩ := hsol u c0 hu hc0
  refine ⟨c, hc, negativeMass_le_of_lower F c _ fun τ hτ => ?_⟩
  have := hm τ hτ
  have hT : (0 : ℤ) ≤ totalU u := by
    unfold totalU
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => by
      split_ifs
      · exact hu.nonneg i j
      · exact le_refl 0
  push_cast
  nlinarith

end PaddedComponents

#print axioms PaddedComponents.witnessBound_of_latEq_lowerK
