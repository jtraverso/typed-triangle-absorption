/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs

@[expose] public section

/-!
# `UniversalCert` for the isolated-monochromatic `ℤ/3` families, part 4

For each family: the component lattices are `Even3` (explicit canonical witness), every integral
witness can be replaced by the canonical one with coefficients `≥ -(K₀ e + 4)`, and
`universalCert_of_even3_components` gives `UniversalCert`.
-/

set_option Elab.async false

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- The canonical integral witness for `FM27`. -/
def canon_FM27 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({1,1,2}, (4 * u 1 1 + 1 * u 1 2 - 2 * u 1 3 - 2 * u 2 2 + 1 * u 2 3 + 4 * u 3 3) / 6), ({1,1,3}, (2 * u 1 1 - 1 * u 1 2 + 2 * u 1 3 + 2 * u 2 2 - 1 * u 2 3 - 4 * u 3 3) / 6), ({1,2,2}, (-2 * u 1 1 + 1 * u 1 2 + 1 * u 1 3 + 4 * u 2 2 - 2 * u 2 3 - 2 * u 3 3) / 6), ({1,2,3}, (-2 * u 1 1 + 1 * u 1 2 + 1 * u 1 3 - 2 * u 2 2 + 1 * u 2 3 - 2 * u 3 3) / 3), ({1,3,3}, (1 * u 3 3) / 1), ({2,2,3}, (2 * u 1 1 - 1 * u 1 2 - 1 * u 1 3 + 2 * u 2 2 + 2 * u 2 3 + 2 * u 3 3) / 6), ({0,0,0}, u 0 0 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM27 (k : Fin 4) : ∀ u, ScalarHyp FM27 u → CountsInside cM0 k u →
    ∃ w, LatEq FM27 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link FM27; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FM27; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM27; decide)
  have hsplit : u 0 0 = 0 ∨ (u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 1 3 = 0 ∧ u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) := by
    by_cases hk : k = cM0 0
    · subst hk
      right
      exact ⟨hin 1 1 (by left; decide),
        hin 1 2 (by left; decide),
        hin 1 3 (by left; decide),
        hin 2 2 (by left; decide),
        hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · left
      exact hin 0 0 (by left; simpa [cM0] using Ne.symm hk)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM27 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM27, canon_FM27, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM27 (k : Fin 4) : Even3Inside FM27 cM0 k :=
  even3Inside_of_scalar FM27 cM0 k FM27_three FM27_card (scalar_inside_FM27 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM27 : ∀ u c0, ScalarHyp FM27 u → LatEq FM27 u c0 →
    ∃ c, LatEq FM27 u c ∧ ∀ τ ∈ FM27, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link FM27; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FM27; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM27; decide)
  have e00 := hc0 0 0
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e13 := hc0 1 3
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM27, typeEdgeVec, sum_insert] at e00 e11 e12 e13 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM27 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM27, canon_FM27, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM27, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM27, coeffList] <;> omega

/-- **`UniversalCert FM27`.** -/
theorem universalCert_FM27 : UniversalCert FM27 := by
  have hB : WitnessBoundK FM27 168 1376 := by
    rw [show (1376 : ℕ) = FM27.card * (1 * 168 + 4) by rw [FM27_card_eq]]
    exact witnessBound_of_latEq_lowerK FM27 FM27_card 1 scalar_witness_FM27 168
  exact universalCert_of_even3_components FM27 cM0 compLabel_FM27 typesInside_FM27
    FM27_card FM27_three localWalk4_FM27 even3Inside_FM27 1376 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])


end PaddedComponents

#print axioms PaddedComponents.universalCert_FM27
