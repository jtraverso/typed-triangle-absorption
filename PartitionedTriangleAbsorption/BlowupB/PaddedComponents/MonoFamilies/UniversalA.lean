/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs

@[expose] public section

/-!
# `UniversalCert` for the isolated-monochromatic `ℤ/3` families, part 1

For each family: the component lattices are `Even3` (explicit canonical witness), every integral
witness can be replaced by the canonical one with coefficients `≥ -(K₀ e + 4)`, and
`universalCert_of_even3_components` gives `UniversalCert`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- The canonical integral witness for `FM01`. -/
def canon_FM01 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1) / 2), ({0,0,2}, (1 * u 0 2) / 2), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM01 (k : Fin 4) : ∀ u, ScalarHyp FM01 u → CountsInside cM3 k u →
    ∃ w, LatEq FM01 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM01; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link FM01; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM01; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM01; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM01; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM01; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM01 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM01, canon_FM01, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM01 (k : Fin 4) : Even3Inside FM01 cM3 k :=
  even3Inside_of_scalar FM01 cM3 k FM01_three FM01_card (scalar_inside_FM01 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM01 : ∀ u c0, ScalarHyp FM01 u → LatEq FM01 u c0 →
    ∃ c, LatEq FM01 u c ∧ ∀ τ ∈ FM01, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM01; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link FM01; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM01; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM01; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM01; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM01; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM01, typeEdgeVec, sum_insert] at e00 e01 e02 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM01 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM01, canon_FM01, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM01, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM01, coeffList] <;> omega

/-- **`UniversalCert FM01`.** -/
theorem universalCert_FM01 : UniversalCert FM01 := by
  have hB : WitnessBoundK FM01 168 688 := by
    rw [show (688 : ℕ) = FM01.card * (1 * 168 + 4) by rw [FM01_card_eq]]
    exact witnessBound_of_latEq_lowerK FM01 FM01_card 1 scalar_witness_FM01 168
  exact universalCert_of_even3_components FM01 cM3 compLabel_FM01 typesInside_FM01
    FM01_card FM01_three localWalk4_FM01 even3Inside_FM01 688 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM02`. -/
def canon_FM02 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,0,2}, (1 * u 0 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM02 (k : Fin 4) : ∀ u, ScalarHyp FM02 u → CountsInside cM3 k u →
    ∃ w, LatEq FM02 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM02; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM02; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM02; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM02; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM02; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 1 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM02 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM02, canon_FM02, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM02 (k : Fin 4) : Even3Inside FM02 cM3 k :=
  even3Inside_of_scalar FM02 cM3 k FM02_three FM02_card (scalar_inside_FM02 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM02 : ∀ u c0, ScalarHyp FM02 u → LatEq FM02 u c0 →
    ∃ c, LatEq FM02 u c ∧ ∀ τ ∈ FM02, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM02; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM02; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM02; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM02; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM02; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM02, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM02 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM02, canon_FM02, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM02, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM02, coeffList] <;> omega

/-- **`UniversalCert FM02`.** -/
theorem universalCert_FM02 : UniversalCert FM02 := by
  have hB : WitnessBoundK FM02 168 860 := by
    rw [show (860 : ℕ) = FM02.card * (1 * 168 + 4) by rw [FM02_card_eq]]
    exact witnessBound_of_latEq_lowerK FM02 FM02_card 1 scalar_witness_FM02 168
  exact universalCert_of_even3_components FM02 cM3 compLabel_FM02 typesInside_FM02
    FM02_card FM02_three localWalk4_FM02 even3Inside_FM02 860 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM03`. -/
def canon_FM03 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({0,1,2}, (1 * u 1 2) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM03 (k : Fin 4) : ∀ u, ScalarHyp FM03 u → CountsInside cM3 k u →
    ∃ w, LatEq FM03 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM03; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link FM03; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM03; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM03; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM03; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM03 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM03, canon_FM03, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM03 (k : Fin 4) : Even3Inside FM03 cM3 k :=
  even3Inside_of_scalar FM03 cM3 k FM03_three FM03_card (scalar_inside_FM03 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM03 : ∀ u c0, ScalarHyp FM03 u → LatEq FM03 u c0 →
    ∃ c, LatEq FM03 u c ∧ ∀ τ ∈ FM03, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM03; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link FM03; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM03; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM03; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM03; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM03, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM03 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM03, canon_FM03, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM03, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM03, coeffList] <;> omega

/-- **`UniversalCert FM03`.** -/
theorem universalCert_FM03 : UniversalCert FM03 := by
  have hB : WitnessBoundK FM03 168 860 := by
    rw [show (860 : ℕ) = FM03.card * (1 * 168 + 4) by rw [FM03_card_eq]]
    exact witnessBound_of_latEq_lowerK FM03 FM03_card 1 scalar_witness_FM03 168
  exact universalCert_of_even3_components FM03 cM3 compLabel_FM03 typesInside_FM03
    FM03_card FM03_three localWalk4_FM03 even3Inside_FM03 860 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM04`. -/
def canon_FM04 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 + 2 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM04 (k : Fin 4) : ∀ u, ScalarHyp FM04 u → CountsInside cM3 k u →
    ∃ w, LatEq FM04 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM04; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM04; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM04; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM04; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 1 (by left; decide),
        hin 1 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM04 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM04, canon_FM04, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM04 (k : Fin 4) : Even3Inside FM04 cM3 k :=
  even3Inside_of_scalar FM04 cM3 k FM04_three FM04_card (scalar_inside_FM04 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM04 : ∀ u c0, ScalarHyp FM04 u → LatEq FM04 u c0 →
    ∃ c, LatEq FM04 u c ∧ ∀ τ ∈ FM04, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM04; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM04; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM04; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM04; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM04, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM04 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM04, canon_FM04, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM04, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM04, coeffList] <;> omega

/-- **`UniversalCert FM04`.** -/
theorem universalCert_FM04 : UniversalCert FM04 := by
  have hB : WitnessBoundK FM04 168 1032 := by
    rw [show (1032 : ℕ) = FM04.card * (1 * 168 + 4) by rw [FM04_card_eq]]
    exact witnessBound_of_latEq_lowerK FM04 FM04_card 1 scalar_witness_FM04 168
  exact universalCert_of_even3_components FM04 cM3 compLabel_FM04 typesInside_FM04
    FM04_card FM04_three localWalk4_FM04 even3Inside_FM04 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM05`. -/
def canon_FM05 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 + 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM05 (k : Fin 4) : ∀ u, ScalarHyp FM05 u → CountsInside cM3 k u →
    ∃ w, LatEq FM05 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM05; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM05; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM05; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM05; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 2 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 1 (by left; decide),
        hin 2 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM05 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM05, canon_FM05, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM05 (k : Fin 4) : Even3Inside FM05 cM3 k :=
  even3Inside_of_scalar FM05 cM3 k FM05_three FM05_card (scalar_inside_FM05 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM05 : ∀ u c0, ScalarHyp FM05 u → LatEq FM05 u c0 →
    ∃ c, LatEq FM05 u c ∧ ∀ τ ∈ FM05, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM05; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM05; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM05; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM05; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM05, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM05 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM05, canon_FM05, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM05, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM05, coeffList] <;> omega

/-- **`UniversalCert FM05`.** -/
theorem universalCert_FM05 : UniversalCert FM05 := by
  have hB : WitnessBoundK FM05 168 1032 := by
    rw [show (1032 : ℕ) = FM05.card * (1 * 168 + 4) by rw [FM05_card_eq]]
    exact witnessBound_of_latEq_lowerK FM05 FM05_card 1 scalar_witness_FM05 168
  exact universalCert_of_even3_components FM05 cM3 compLabel_FM05 typesInside_FM05
    FM05_card FM05_three localWalk4_FM05 even3Inside_FM05 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM06`. -/
def canon_FM06 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,0,2}, (1 * u 0 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM06 (k : Fin 4) : ∀ u, ScalarHyp FM06 u → CountsInside cM3 k u →
    ∃ w, LatEq FM06 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM06; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM06; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM06; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM06; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM06; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 1 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM06 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM06, canon_FM06, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM06 (k : Fin 4) : Even3Inside FM06 cM3 k :=
  even3Inside_of_scalar FM06 cM3 k FM06_three FM06_card (scalar_inside_FM06 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM06 : ∀ u c0, ScalarHyp FM06 u → LatEq FM06 u c0 →
    ∃ c, LatEq FM06 u c ∧ ∀ τ ∈ FM06, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM06; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FM06; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM06; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM06; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM06; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM06, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM06 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM06, canon_FM06, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM06, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM06, coeffList] <;> omega

/-- **`UniversalCert FM06`.** -/
theorem universalCert_FM06 : UniversalCert FM06 := by
  have hB : WitnessBoundK FM06 168 1032 := by
    rw [show (1032 : ℕ) = FM06.card * (1 * 168 + 4) by rw [FM06_card_eq]]
    exact witnessBound_of_latEq_lowerK FM06 FM06_card 1 scalar_witness_FM06 168
  exact universalCert_of_even3_components FM06 cM3 compLabel_FM06 typesInside_FM06
    FM06_card FM06_three localWalk4_FM06 even3Inside_FM06 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM07`. -/
def canon_FM07 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 0 2 + 2 * u 1 1 - 1 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 0 2 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,1,1}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,1,2}, (-1 * u 0 2 + 1 * u 1 2) / 2), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM07 (k : Fin 4) : ∀ u, ScalarHyp FM07 u → CountsInside cM3 k u →
    ∃ w, LatEq FM07 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM07; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM07; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM07; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM07; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
        hin 1 1 (by left; decide),
        hin 1 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM07 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM07, canon_FM07, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM07 (k : Fin 4) : Even3Inside FM07 cM3 k :=
  even3Inside_of_scalar FM07 cM3 k FM07_three FM07_card (scalar_inside_FM07 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM07 : ∀ u c0, ScalarHyp FM07 u → LatEq FM07 u c0 →
    ∃ c, LatEq FM07 u c ∧ ∀ τ ∈ FM07, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM07; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM07; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FM07; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM07; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM07, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM07 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM07, canon_FM07, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM07, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM07, coeffList] <;> omega

/-- **`UniversalCert FM07`.** -/
theorem universalCert_FM07 : UniversalCert FM07 := by
  have hB : WitnessBoundK FM07 168 1032 := by
    rw [show (1032 : ℕ) = FM07.card * (1 * 168 + 4) by rw [FM07_card_eq]]
    exact witnessBound_of_latEq_lowerK FM07 FM07_card 1 scalar_witness_FM07 168
  exact universalCert_of_even3_components FM07 cM3 compLabel_FM07 typesInside_FM07
    FM07_card FM07_three localWalk4_FM07 even3Inside_FM07 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The canonical integral witness for `FM08`. -/
def canon_FM08 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 2), ({1,1,2}, (1 * u 1 2 - 2 * u 2 2) / 2), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, u 3 3 / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_FM08 (k : Fin 4) : ∀ u, ScalarHyp FM08 u → CountsInside cM3 k u →
    ∃ w, LatEq FM08 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FM08; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM08; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM08; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM08; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 1 1 (by left; decide),
        hin 1 2 (by left; decide),
        hin 2 2 (by left; decide)⟩
    · left
      exact hin 3 3 (by left; simpa [cM3] using Ne.symm hk)
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
  refine ⟨canon_FM08 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FM08, canon_FM08, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FM08 (k : Fin 4) : Even3Inside FM08 cM3 k :=
  even3Inside_of_scalar FM08 cM3 k FM08_three FM08_card (scalar_inside_FM08 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_FM08 : ∀ u c0, ScalarHyp FM08 u → LatEq FM08 u c0 →
    ∃ c, LatEq FM08 u c ∧ ∀ τ ∈ FM08, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FM08; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FM08; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FM08; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FM08; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FM08, typeEdgeVec, sum_insert] at e00 e01 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_FM08 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FM08, canon_FM08, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FM08, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_FM08, coeffList] <;> omega

/-- **`UniversalCert FM08`.** -/
theorem universalCert_FM08 : UniversalCert FM08 := by
  have hB : WitnessBoundK FM08 168 1032 := by
    rw [show (1032 : ℕ) = FM08.card * (1 * 168 + 4) by rw [FM08_card_eq]]
    exact witnessBound_of_latEq_lowerK FM08 FM08_card 1 scalar_witness_FM08 168
  exact universalCert_of_even3_components FM08 cM3 compLabel_FM08 typesInside_FM08
    FM08_card FM08_three localWalk4_FM08 even3Inside_FM08 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_FM01
#print axioms PaddedComponents.universalCert_FM02
#print axioms PaddedComponents.universalCert_FM03
#print axioms PaddedComponents.universalCert_FM04
#print axioms PaddedComponents.universalCert_FM05
#print axioms PaddedComponents.universalCert_FM06
#print axioms PaddedComponents.universalCert_FM07
#print axioms PaddedComponents.universalCert_FM08
