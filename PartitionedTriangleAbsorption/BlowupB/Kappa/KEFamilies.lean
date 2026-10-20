/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs

@[expose] public section

/-!
# Four disconnected `ThreeStepLinks` families whose components are all `Even3`

`KE1 = {000,111,222,333}` (census class `ℤ/27`) and the three-component `ℤ/9` classes
`KE2 = {000,001,222,333}`, `KE3 = {000,001,011,222,333}`, `KE4 = {000,001,011,111,222,333}`.
`UniversalCert` by Aristotle's `universalCert_of_even3_components`. Generator: `gen_ke.py`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- `{000 111 222 333}`. -/
noncomputable def KE1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KE1_card : ∀ τ ∈ KE1, Multiset.card τ = 3 := by unfold KE1; decide
theorem KE1_card_eq : KE1.card = 4 := by unfold KE1; decide
theorem KE1_three : ThreeStepLinks KE1 := by unfold ThreeStepLinks Link KE1; decide
theorem familyFacts_KE1 : FamilyFacts KE1 :=
  ⟨KE1_card, by unfold Link KE1; decide,
    by intro i; fin_cases i <;> (unfold Link KE1; decide)⟩

/-- Component labels of `KE1`. -/
def cKE1 : Fin 4 → Fin 4 := ![0, 1, 2, 3]
theorem compLabel_KE1 : CompLabel KE1 cKE1 := by unfold CompLabel Link KE1 cKE1; decide
theorem typesInside_KE1 : TypesInside KE1 cKE1 := by unfold TypesInside KE1 cKE1; decide
theorem localWalk4_KE1 (k : Fin 4) : LocalWalk4 KE1 cKE1 k := by
  revert k; unfold LocalWalk4 Link KE1 cKE1; decide

def canon_KE1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (1 * u 0 0) / 3), ({1,1,1}, (1 * u 1 1) / 3), ({2,2,2}, (1 * u 2 2) / 3), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE1_0 : ∀ u, ScalarHyp KE1 u → CountsInside cKE1 0 u →
    ∃ w, LatEq KE1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link KE1; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE1; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE1; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE1, canon_KE1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE1_1 : ∀ u, ScalarHyp KE1 u → CountsInside cKE1 1 u →
    ∃ w, LatEq KE1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link KE1; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE1; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE1, canon_KE1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE1_2 : ∀ u, ScalarHyp KE1 u → CountsInside cKE1 2 u →
    ∃ w, LatEq KE1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link KE1; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE1; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE1, canon_KE1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE1_3 : ∀ u, ScalarHyp KE1 u → CountsInside cKE1 3 u →
    ∃ w, LatEq KE1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link KE1; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE1; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE1; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE1, canon_KE1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KE1 (k : Fin 4) : Even3Inside KE1 cKE1 k := by
  fin_cases k
  · exact even3Inside_of_scalar KE1 cKE1 0 KE1_three KE1_card (scalar_inside_KE1_0)
  · exact even3Inside_of_scalar KE1 cKE1 1 KE1_three KE1_card (scalar_inside_KE1_1)
  · exact even3Inside_of_scalar KE1 cKE1 2 KE1_three KE1_card (scalar_inside_KE1_2)
  · exact even3Inside_of_scalar KE1 cKE1 3 KE1_three KE1_card (scalar_inside_KE1_3)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KE1 : ∀ u c0, ScalarHyp KE1 u → LatEq KE1 u c0 →
    ∃ c, LatEq KE1 u c ∧ ∀ τ ∈ KE1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link KE1; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE1; decide)
  have e00 := hc0 0 0
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KE1, typeEdgeVec, sum_insert] at e00 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KE1 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KE1, canon_KE1, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KE1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KE1, coeffList] <;> omega

/-- **`UniversalCert KE1`**. -/
theorem universalCert_KE1 : UniversalCert KE1 := by
  have hB : WitnessBoundK KE1 168 688 := by
    rw [show (688 : ℕ) = KE1.card * (1 * 168 + 4) by rw [KE1_card_eq]]
    exact witnessBound_of_latEq_lowerK KE1 KE1_card 1 scalar_witness_KE1 168
  exact universalCert_of_even3_components KE1 cKE1 compLabel_KE1 typesInside_KE1
    KE1_card KE1_three localWalk4_KE1 even3Inside_KE1 688 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 222 333}`. -/
noncomputable def KE2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KE2_card : ∀ τ ∈ KE2, Multiset.card τ = 3 := by unfold KE2; decide
theorem KE2_card_eq : KE2.card = 4 := by unfold KE2; decide
theorem KE2_three : ThreeStepLinks KE2 := by unfold ThreeStepLinks Link KE2; decide
theorem familyFacts_KE2 : FamilyFacts KE2 :=
  ⟨KE2_card, by unfold Link KE2; decide,
    by intro i; fin_cases i <;> (unfold Link KE2; decide)⟩

/-- Component labels of `KE2`. -/
def cKE2 : Fin 4 → Fin 4 := ![0, 0, 2, 3]
theorem compLabel_KE2 : CompLabel KE2 cKE2 := by unfold CompLabel Link KE2 cKE2; decide
theorem typesInside_KE2 : TypesInside KE2 cKE2 := by unfold TypesInside KE2 cKE2; decide
theorem localWalk4_KE2 (k : Fin 4) : LocalWalk4 KE2 cKE2 k := by
  revert k; unfold LocalWalk4 Link KE2 cKE2; decide

def canon_KE2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1) / 6), ({0,0,1}, (1 * u 0 1) / 2), ({2,2,2}, (1 * u 2 2) / 3), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE2_0 : ∀ u, ScalarHyp KE2 u → CountsInside cKE2 0 u →
    ∃ w, LatEq KE2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE2; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KE2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE2; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE2, canon_KE2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE2_1 : ∀ u, ScalarHyp KE2 u → CountsInside cKE2 1 u →
    ∃ w, LatEq KE2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE2; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KE2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE2; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE2, canon_KE2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE2_2 : ∀ u, ScalarHyp KE2 u → CountsInside cKE2 2 u →
    ∃ w, LatEq KE2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE2; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KE2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE2; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE2, canon_KE2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE2_3 : ∀ u, ScalarHyp KE2 u → CountsInside cKE2 3 u →
    ∃ w, LatEq KE2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE2; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KE2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE2, canon_KE2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KE2 (k : Fin 4) : Even3Inside KE2 cKE2 k := by
  fin_cases k
  · exact even3Inside_of_scalar KE2 cKE2 0 KE2_three KE2_card (scalar_inside_KE2_0)
  · exact even3Inside_of_scalar KE2 cKE2 1 KE2_three KE2_card (scalar_inside_KE2_1)
  · exact even3Inside_of_scalar KE2 cKE2 2 KE2_three KE2_card (scalar_inside_KE2_2)
  · exact even3Inside_of_scalar KE2 cKE2 3 KE2_three KE2_card (scalar_inside_KE2_3)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KE2 : ∀ u c0, ScalarHyp KE2 u → LatEq KE2 u c0 →
    ∃ c, LatEq KE2 u c ∧ ∀ τ ∈ KE2, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE2; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KE2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KE2, typeEdgeVec, sum_insert] at e00 e01 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KE2 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KE2, canon_KE2, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KE2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KE2, coeffList] <;> omega

/-- **`UniversalCert KE2`**. -/
theorem universalCert_KE2 : UniversalCert KE2 := by
  have hB : WitnessBoundK KE2 168 688 := by
    rw [show (688 : ℕ) = KE2.card * (1 * 168 + 4) by rw [KE2_card_eq]]
    exact witnessBound_of_latEq_lowerK KE2 KE2_card 1 scalar_witness_KE2 168
  exact universalCert_of_even3_components KE2 cKE2 compLabel_KE2 typesInside_KE2
    KE2_card KE2_three localWalk4_KE2 even3Inside_KE2 688 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 222 333}`. -/
noncomputable def KE3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KE3_card : ∀ τ ∈ KE3, Multiset.card τ = 3 := by unfold KE3; decide
theorem KE3_card_eq : KE3.card = 5 := by unfold KE3; decide
theorem KE3_three : ThreeStepLinks KE3 := by unfold ThreeStepLinks Link KE3; decide
theorem familyFacts_KE3 : FamilyFacts KE3 :=
  ⟨KE3_card, by unfold Link KE3; decide,
    by intro i; fin_cases i <;> (unfold Link KE3; decide)⟩

/-- Component labels of `KE3`. -/
def cKE3 : Fin 4 → Fin 4 := ![0, 0, 2, 3]
theorem compLabel_KE3 : CompLabel KE3 cKE3 := by unfold CompLabel Link KE3 cKE3; decide
theorem typesInside_KE3 : TypesInside KE3 cKE3 := by unfold TypesInside KE3 cKE3; decide
theorem localWalk4_KE3 (k : Fin 4) : LocalWalk4 KE3 cKE3 k := by
  revert k; unfold LocalWalk4 Link KE3 cKE3; decide

def canon_KE3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (1 * u 2 2) / 3), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE3_0 : ∀ u, ScalarHyp KE3 u → CountsInside cKE3 0 u →
    ∃ w, LatEq KE3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE3, canon_KE3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE3_1 : ∀ u, ScalarHyp KE3 u → CountsInside cKE3 1 u →
    ∃ w, LatEq KE3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE3, canon_KE3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE3_2 : ∀ u, ScalarHyp KE3 u → CountsInside cKE3 2 u →
    ∃ w, LatEq KE3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE3, canon_KE3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE3_3 : ∀ u, ScalarHyp KE3 u → CountsInside cKE3 3 u →
    ∃ w, LatEq KE3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE3, canon_KE3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KE3 (k : Fin 4) : Even3Inside KE3 cKE3 k := by
  fin_cases k
  · exact even3Inside_of_scalar KE3 cKE3 0 KE3_three KE3_card (scalar_inside_KE3_0)
  · exact even3Inside_of_scalar KE3 cKE3 1 KE3_three KE3_card (scalar_inside_KE3_1)
  · exact even3Inside_of_scalar KE3 cKE3 2 KE3_three KE3_card (scalar_inside_KE3_2)
  · exact even3Inside_of_scalar KE3 cKE3 3 KE3_three KE3_card (scalar_inside_KE3_3)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KE3 : ∀ u c0, ScalarHyp KE3 u → LatEq KE3 u c0 →
    ∃ c, LatEq KE3 u c ∧ ∀ τ ∈ KE3, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KE3, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KE3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KE3, canon_KE3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KE3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KE3, coeffList] <;> omega

/-- **`UniversalCert KE3`**. -/
theorem universalCert_KE3 : UniversalCert KE3 := by
  have hB : WitnessBoundK KE3 168 860 := by
    rw [show (860 : ℕ) = KE3.card * (1 * 168 + 4) by rw [KE3_card_eq]]
    exact witnessBound_of_latEq_lowerK KE3 KE3_card 1 scalar_witness_KE3 168
  exact universalCert_of_even3_components KE3 cKE3 compLabel_KE3 typesInside_KE3
    KE3_card KE3_three localWalk4_KE3 even3Inside_KE3 860 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 111 222 333}`. -/
noncomputable def KE4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KE4_card : ∀ τ ∈ KE4, Multiset.card τ = 3 := by unfold KE4; decide
theorem KE4_card_eq : KE4.card = 6 := by unfold KE4; decide
theorem KE4_three : ThreeStepLinks KE4 := by unfold ThreeStepLinks Link KE4; decide
theorem familyFacts_KE4 : FamilyFacts KE4 :=
  ⟨KE4_card, by unfold Link KE4; decide,
    by intro i; fin_cases i <;> (unfold Link KE4; decide)⟩

/-- Component labels of `KE4`. -/
def cKE4 : Fin 4 → Fin 4 := ![0, 0, 2, 3]
theorem compLabel_KE4 : CompLabel KE4 cKE4 := by unfold CompLabel Link KE4 cKE4; decide
theorem typesInside_KE4 : TypesInside KE4 cKE4 := by unfold TypesInside KE4 cKE4; decide
theorem localWalk4_KE4 (k : Fin 4) : LocalWalk4 KE4 cKE4 k := by
  revert k; unfold LocalWalk4 Link KE4 cKE4; decide

def canon_KE4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (1 * u 2 2) / 3), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE4_0 : ∀ u, ScalarHyp KE4 u → CountsInside cKE4 0 u →
    ∃ w, LatEq KE4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE4; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE4, canon_KE4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE4_1 : ∀ u, ScalarHyp KE4 u → CountsInside cKE4 1 u →
    ∃ w, LatEq KE4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE4; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE4, canon_KE4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE4_2 : ∀ u, ScalarHyp KE4 u → CountsInside cKE4 2 u →
    ∃ w, LatEq KE4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKE4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE4, canon_KE4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KE4_3 : ∀ u, ScalarHyp KE4 u → CountsInside cKE4 3 u →
    ∃ w, LatEq KE4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKE4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKE4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKE4; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKE4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KE4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KE4, canon_KE4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KE4 (k : Fin 4) : Even3Inside KE4 cKE4 k := by
  fin_cases k
  · exact even3Inside_of_scalar KE4 cKE4 0 KE4_three KE4_card (scalar_inside_KE4_0)
  · exact even3Inside_of_scalar KE4 cKE4 1 KE4_three KE4_card (scalar_inside_KE4_1)
  · exact even3Inside_of_scalar KE4 cKE4 2 KE4_three KE4_card (scalar_inside_KE4_2)
  · exact even3Inside_of_scalar KE4 cKE4 3 KE4_three KE4_card (scalar_inside_KE4_3)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KE4 : ∀ u c0, ScalarHyp KE4 u → LatEq KE4 u c0 →
    ∃ c, LatEq KE4 u c ∧ ∀ τ ∈ KE4, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KE4; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KE4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KE4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KE4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KE4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KE4, typeEdgeVec, sum_insert] at e00 e01 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KE4 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KE4, canon_KE4, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KE4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KE4, coeffList] <;> omega

/-- **`UniversalCert KE4`**. -/
theorem universalCert_KE4 : UniversalCert KE4 := by
  have hB : WitnessBoundK KE4 168 1032 := by
    rw [show (1032 : ℕ) = KE4.card * (1 * 168 + 4) by rw [KE4_card_eq]]
    exact witnessBound_of_latEq_lowerK KE4 KE4_card 1 scalar_witness_KE4 168
  exact universalCert_of_even3_components KE4 cKE4 compLabel_KE4 typesInside_KE4
    KE4_card KE4_three localWalk4_KE4 even3Inside_KE4 1032 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KE1
#print axioms PaddedComponents.universalCert_KE2
#print axioms PaddedComponents.universalCert_KE3
#print axioms PaddedComponents.universalCert_KE4
