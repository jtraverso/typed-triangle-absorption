/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.FamilyB1

@[expose] public section

/-!
# The other disconnected `ℤ/3` families without an isolated monochromatic class

Census rows `Y | N | 2 | N | Z/3` whose classes all see another class (labels `cB1 = (0,0,2,2)`):

| family | types |
|---|---|
| `FB2` | 000 001 011 222 223 |
| `FB3` | 000 001 011 222 223 233 |
| `FB4` | 000 001 011 111 222 223 |
| `FB5` | 000 001 011 111 222 223 233 |
| `FB6` | 000 001 011 111 222 223 233 333 |

(`FB1 = {000, 001, 222, 223}` is in `FamilyB1.lean`.) For each family: the finite facts
(`decide`), the component lattices are `Even3` (explicit witnesses
`c₀₁₁ = u₁₁, c₀₀₁ = u₀₁/2 - u₁₁, c₀₀₀ = (u₀₀ - u₀₁/2 + u₁₁)/3` and the same on `{2,3}`), the
witness bound `|F|(2·168+4)`, and `UniversalCert` from `universalCert_of_even3_components`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- The canonical witness on both components. -/
def canonZ3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (u 0 0 - u 0 1 / 2 + u 1 1) / 3), ({0,0,1}, u 0 1 / 2 - u 1 1),
    ({0,1,1}, u 1 1), ({2,2,2}, (u 2 2 - u 2 3 / 2 + u 3 3) / 3), ({2,2,3}, u 2 3 / 2 - u 3 3),
    ({2,3,3}, u 3 3)]

/-- The family `{000 001 011 222 223}`. -/
noncomputable def FB2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {2, 2, 3}}

theorem FB2_card : ∀ τ ∈ FB2, Multiset.card τ = 3 := by unfold FB2; decide

theorem FB2_three : ThreeStepLinks FB2 := by unfold ThreeStepLinks Link FB2; decide

theorem familyFacts_FB2 : FamilyFacts FB2 :=
  ⟨FB2_card, by unfold Link FB2; decide,
    by intro i; fin_cases i <;> (unfold Link FB2; decide)⟩

theorem compLabel_FB2 : CompLabel FB2 cB1 := by unfold CompLabel Link FB2 cB1; decide

theorem typesInside_FB2 : TypesInside FB2 cB1 := by unfold TypesInside FB2 cB1; decide

theorem localWalk4_FB2 (k : Fin 4) : LocalWalk4 FB2 cB1 k := by
  revert k; unfold LocalWalk4 Link FB2 cB1; decide

set_option maxHeartbeats 8000000 in
theorem scalar_inside_FB2 (k : Fin 4) : ∀ u, ScalarHyp FB2 u → CountsInside cB1 k u →
    ∃ w, LatEq FB2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FB2; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk),
        hin 1 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB2, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FB2 (k : Fin 4) : Even3Inside FB2 cB1 k :=
  even3Inside_of_scalar FB2 cB1 k FB2_three FB2_card (scalar_inside_FB2 k)

set_option maxHeartbeats 8000000 in
theorem scalar_witness_FB2 : ∀ u c0, ScalarHyp FB2 u → LatEq FB2 u c0 →
    ∃ c, LatEq FB2 u c ∧ ∀ τ ∈ FB2, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FB2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FB2, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FB2, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FB2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canonZ3, coeffList] <;> omega

theorem FB2_card_eq : FB2.card = 5 := by unfold FB2; decide

/-- **`UniversalCert FB2`.** -/
theorem universalCert_FB2 : UniversalCert FB2 := by
  have hB : WitnessBoundK FB2 168 1700 := by
    rw [show (1700 : ℕ) = FB2.card * (2 * 168 + 4) by rw [FB2_card_eq]]
    exact witnessBound_of_latEq_lower FB2 FB2_card scalar_witness_FB2 168
  exact universalCert_of_even3_components FB2 cB1 compLabel_FB2 typesInside_FB2
    FB2_card FB2_three localWalk4_FB2 even3Inside_FB2 1700 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The family `{000 001 011 222 223 233}`. -/
noncomputable def FB3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {2, 2, 3}, {2, 3, 3}}

theorem FB3_card : ∀ τ ∈ FB3, Multiset.card τ = 3 := by unfold FB3; decide

theorem FB3_three : ThreeStepLinks FB3 := by unfold ThreeStepLinks Link FB3; decide

theorem familyFacts_FB3 : FamilyFacts FB3 :=
  ⟨FB3_card, by unfold Link FB3; decide,
    by intro i; fin_cases i <;> (unfold Link FB3; decide)⟩

theorem compLabel_FB3 : CompLabel FB3 cB1 := by unfold CompLabel Link FB3 cB1; decide

theorem typesInside_FB3 : TypesInside FB3 cB1 := by unfold TypesInside FB3 cB1; decide

theorem localWalk4_FB3 (k : Fin 4) : LocalWalk4 FB3 cB1 k := by
  revert k; unfold LocalWalk4 Link FB3 cB1; decide

set_option maxHeartbeats 8000000 in
theorem scalar_inside_FB3 (k : Fin 4) : ∀ u, ScalarHyp FB3 u → CountsInside cB1 k u →
    ∃ w, LatEq FB3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB3; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk),
        hin 1 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB3, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FB3 (k : Fin 4) : Even3Inside FB3 cB1 k :=
  even3Inside_of_scalar FB3 cB1 k FB3_three FB3_card (scalar_inside_FB3 k)

set_option maxHeartbeats 8000000 in
theorem scalar_witness_FB3 : ∀ u c0, ScalarHyp FB3 u → LatEq FB3 u c0 →
    ∃ c, LatEq FB3 u c ∧ ∀ τ ∈ FB3, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FB3, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FB3, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FB3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canonZ3, coeffList] <;> omega

theorem FB3_card_eq : FB3.card = 6 := by unfold FB3; decide

/-- **`UniversalCert FB3`.** -/
theorem universalCert_FB3 : UniversalCert FB3 := by
  have hB : WitnessBoundK FB3 168 2040 := by
    rw [show (2040 : ℕ) = FB3.card * (2 * 168 + 4) by rw [FB3_card_eq]]
    exact witnessBound_of_latEq_lower FB3 FB3_card scalar_witness_FB3 168
  exact universalCert_of_even3_components FB3 cB1 compLabel_FB3 typesInside_FB3
    FB3_card FB3_three localWalk4_FB3 even3Inside_FB3 2040 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The family `{000 001 011 111 222 223}`. -/
noncomputable def FB4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 1}, {2, 2, 2}, {2, 2, 3}}

theorem FB4_card : ∀ τ ∈ FB4, Multiset.card τ = 3 := by unfold FB4; decide

theorem FB4_three : ThreeStepLinks FB4 := by unfold ThreeStepLinks Link FB4; decide

theorem familyFacts_FB4 : FamilyFacts FB4 :=
  ⟨FB4_card, by unfold Link FB4; decide,
    by intro i; fin_cases i <;> (unfold Link FB4; decide)⟩

theorem compLabel_FB4 : CompLabel FB4 cB1 := by unfold CompLabel Link FB4 cB1; decide

theorem typesInside_FB4 : TypesInside FB4 cB1 := by unfold TypesInside FB4 cB1; decide

theorem localWalk4_FB4 (k : Fin 4) : LocalWalk4 FB4 cB1 k := by
  revert k; unfold LocalWalk4 Link FB4 cB1; decide

set_option maxHeartbeats 8000000 in
theorem scalar_inside_FB4 (k : Fin 4) : ∀ u, ScalarHyp FB4 u → CountsInside cB1 k u →
    ∃ w, LatEq FB4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB4; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FB4; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk),
        hin 1 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB4, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FB4 (k : Fin 4) : Even3Inside FB4 cB1 k :=
  even3Inside_of_scalar FB4 cB1 k FB4_three FB4_card (scalar_inside_FB4 k)

set_option maxHeartbeats 8000000 in
theorem scalar_witness_FB4 : ∀ u c0, ScalarHyp FB4 u → LatEq FB4 u c0 →
    ∃ c, LatEq FB4 u c ∧ ∀ τ ∈ FB4, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB4; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FB4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FB4, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FB4, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FB4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canonZ3, coeffList] <;> omega

theorem FB4_card_eq : FB4.card = 6 := by unfold FB4; decide

/-- **`UniversalCert FB4`.** -/
theorem universalCert_FB4 : UniversalCert FB4 := by
  have hB : WitnessBoundK FB4 168 2040 := by
    rw [show (2040 : ℕ) = FB4.card * (2 * 168 + 4) by rw [FB4_card_eq]]
    exact witnessBound_of_latEq_lower FB4 FB4_card scalar_witness_FB4 168
  exact universalCert_of_even3_components FB4 cB1 compLabel_FB4 typesInside_FB4
    FB4_card FB4_three localWalk4_FB4 even3Inside_FB4 2040 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The family `{000 001 011 111 222 223 233}`. -/
noncomputable def FB5 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 1}, {2, 2, 2}, {2, 2, 3}, {2, 3, 3}}

theorem FB5_card : ∀ τ ∈ FB5, Multiset.card τ = 3 := by unfold FB5; decide

theorem FB5_three : ThreeStepLinks FB5 := by unfold ThreeStepLinks Link FB5; decide

theorem familyFacts_FB5 : FamilyFacts FB5 :=
  ⟨FB5_card, by unfold Link FB5; decide,
    by intro i; fin_cases i <;> (unfold Link FB5; decide)⟩

theorem compLabel_FB5 : CompLabel FB5 cB1 := by unfold CompLabel Link FB5 cB1; decide

theorem typesInside_FB5 : TypesInside FB5 cB1 := by unfold TypesInside FB5 cB1; decide

theorem localWalk4_FB5 (k : Fin 4) : LocalWalk4 FB5 cB1 k := by
  revert k; unfold LocalWalk4 Link FB5 cB1; decide

set_option maxHeartbeats 8000000 in
theorem scalar_inside_FB5 (k : Fin 4) : ∀ u, ScalarHyp FB5 u → CountsInside cB1 k u →
    ∃ w, LatEq FB5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB5; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB5; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk),
        hin 1 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB5, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FB5 (k : Fin 4) : Even3Inside FB5 cB1 k :=
  even3Inside_of_scalar FB5 cB1 k FB5_three FB5_card (scalar_inside_FB5 k)

set_option maxHeartbeats 8000000 in
theorem scalar_witness_FB5 : ∀ u c0, ScalarHyp FB5 u → LatEq FB5 u c0 →
    ∃ c, LatEq FB5 u c ∧ ∀ τ ∈ FB5, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB5; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB5; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FB5, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FB5, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FB5, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canonZ3, coeffList] <;> omega

theorem FB5_card_eq : FB5.card = 7 := by unfold FB5; decide

/-- **`UniversalCert FB5`.** -/
theorem universalCert_FB5 : UniversalCert FB5 := by
  have hB : WitnessBoundK FB5 168 2380 := by
    rw [show (2380 : ℕ) = FB5.card * (2 * 168 + 4) by rw [FB5_card_eq]]
    exact witnessBound_of_latEq_lower FB5 FB5_card scalar_witness_FB5 168
  exact universalCert_of_even3_components FB5 cB1 compLabel_FB5 typesInside_FB5
    FB5_card FB5_three localWalk4_FB5 even3Inside_FB5 2380 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- The family `{000 001 011 111 222 223 233 333}`. -/
noncomputable def FB6 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 1}, {2, 2, 2}, {2, 2, 3}, {2, 3, 3}, {3, 3, 3}}

theorem FB6_card : ∀ τ ∈ FB6, Multiset.card τ = 3 := by unfold FB6; decide

theorem FB6_three : ThreeStepLinks FB6 := by unfold ThreeStepLinks Link FB6; decide

theorem familyFacts_FB6 : FamilyFacts FB6 :=
  ⟨FB6_card, by unfold Link FB6; decide,
    by intro i; fin_cases i <;> (unfold Link FB6; decide)⟩

theorem compLabel_FB6 : CompLabel FB6 cB1 := by unfold CompLabel Link FB6 cB1; decide

theorem typesInside_FB6 : TypesInside FB6 cB1 := by unfold TypesInside FB6 cB1; decide

theorem localWalk4_FB6 (k : Fin 4) : LocalWalk4 FB6 cB1 k := by
  revert k; unfold LocalWalk4 Link FB6 cB1; decide

set_option maxHeartbeats 8000000 in
theorem scalar_inside_FB6 (k : Fin 4) : ∀ u, ScalarHyp FB6 u → CountsInside cB1 k u →
    ∃ w, LatEq FB6 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB6; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide),
        hin 3 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk),
        hin 1 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB6, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_FB6 (k : Fin 4) : Even3Inside FB6 cB1 k :=
  even3Inside_of_scalar FB6 cB1 k FB6_three FB6_card (scalar_inside_FB6 k)

set_option maxHeartbeats 8000000 in
theorem scalar_witness_FB6 : ∀ u c0, ScalarHyp FB6 u → LatEq FB6 u c0 →
    ∃ c, LatEq FB6 u c ∧ ∀ τ ∈ FB6, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB6; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [FB6, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canonZ3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FB6, canonZ3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [FB6, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canonZ3, coeffList] <;> omega

theorem FB6_card_eq : FB6.card = 8 := by unfold FB6; decide

/-- **`UniversalCert FB6`.** -/
theorem universalCert_FB6 : UniversalCert FB6 := by
  have hB : WitnessBoundK FB6 168 2720 := by
    rw [show (2720 : ℕ) = FB6.card * (2 * 168 + 4) by rw [FB6_card_eq]]
    exact witnessBound_of_latEq_lower FB6 FB6_card scalar_witness_FB6 168
  exact universalCert_of_even3_components FB6 cB1 compLabel_FB6 typesInside_FB6
    FB6_card FB6_three localWalk4_FB6 even3Inside_FB6 2720 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_FB2
#print axioms PaddedComponents.universalCert_FB3
#print axioms PaddedComponents.universalCert_FB4
#print axioms PaddedComponents.universalCert_FB5
#print axioms PaddedComponents.universalCert_FB6
