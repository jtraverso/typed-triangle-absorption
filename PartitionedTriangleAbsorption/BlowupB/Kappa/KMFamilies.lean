/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Components
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# Five disconnected `ℤ/3` families with an isolated `333` and no `ThreeStepLinks`

`KM1`–`KM5`: a `KappaLinks` component on the classes `0, 1, 2` plus the isolated type `333`
(component labels `cM3`). Finite facts by `decide`; `UniversalCert` by the `KappaLinks` copy of the
componentwise certificate (`universalCert_of_even3_components_kappa`) with the component lattices
`Even3` (explicit canonical witnesses, `even3Inside_of_scalar_five`). Generator: `gen_km.py`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- `{000 001 011 112 333}`. -/
noncomputable def KM1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {3, 3, 3}}

theorem KM1_card : ∀ τ ∈ KM1, Multiset.card τ = 3 := by unfold KM1; decide

theorem KM1_card_eq : KM1.card = 5 := by unfold KM1; decide

theorem not_threeStep_KM1 : ¬ ThreeStepLinks KM1 := by unfold ThreeStepLinks Link KM1; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KM1 : FiveStepLinks KM1 := by
  unfold FiveStepLinks Link KM1; decide

def kappaKM1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KM1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KM1 := by
  refine ⟨kappaKM1, ?_, ?_⟩ <;> unfold Link KM1 kappaKM1 <;> decide

theorem familyFacts_KM1 : FamilyFacts KM1 :=
  ⟨KM1_card, by unfold Link KM1; decide,
    by intro i; fin_cases i <;> (unfold Link KM1; decide)⟩

theorem compLabel_KM1 : CompLabel KM1 cM3 := by
  unfold CompLabel Link KM1 cM3; decide

theorem typesInside_KM1 : TypesInside KM1 cM3 := by
  unfold TypesInside KM1 cM3; decide

theorem localWalk4_KM1 (k : Fin 4) : LocalWalk4 KM1 cM3 k := by
  revert k; unfold LocalWalk4 Link KM1 cM3; decide

theorem isolatedMono_KM1 : IsolatedMono KM1 3 := by unfold IsolatedMono KM1; decide

/-- The canonical integral witness for `KM1`. -/
def canon_KM1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1 - 1 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2) / 2), ({1,1,2}, (1 * u 1 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KM1 (k : Fin 4) : ∀ u, ScalarHyp KM1 u → CountsInside cM3 k u →
    ∃ w, LatEq KM1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KM1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KM1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM1; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
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
  refine ⟨canon_KM1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KM1, canon_KM1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KM1 (k : Fin 4) : Even3Inside KM1 cM3 k :=
  even3Inside_of_scalar_five KM1 cM3 k fiveStep_KM1 KM1_card (scalar_inside_KM1 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KM1 : ∀ u c0, ScalarHyp KM1 u → LatEq KM1 u c0 →
    ∃ c, LatEq KM1 u c ∧ ∀ τ ∈ KM1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KM1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KM1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KM1, typeEdgeVec, sum_insert] at e00 e01 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KM1 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KM1, canon_KM1, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KM1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KM1, coeffList] <;> omega

/-- **`UniversalCert KM1`** (no `ThreeStepLinks`: `KappaLinks` terminal absorbers). -/
theorem universalCert_KM1 : UniversalCert KM1 := by
  have hB : WitnessBoundK KM1 168 860 := by
    rw [show (860 : ℕ) = KM1.card * (1 * 168 + 4) by rw [KM1_card_eq]]
    exact witnessBound_of_latEq_lowerK KM1 KM1_card 1 scalar_witness_KM1 168
  exact universalCert_of_even3_components_kappa KM1 cM3 compLabel_KM1 typesInside_KM1
    KM1_card kappaLinks_KM1 localWalk4_KM1 even3Inside_KM1 860 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 012 112 333}`. -/
noncomputable def KM2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KM2_card : ∀ τ ∈ KM2, Multiset.card τ = 3 := by unfold KM2; decide

theorem KM2_card_eq : KM2.card = 6 := by unfold KM2; decide

theorem not_threeStep_KM2 : ¬ ThreeStepLinks KM2 := by unfold ThreeStepLinks Link KM2; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KM2 : FiveStepLinks KM2 := by
  unfold FiveStepLinks Link KM2; decide

def kappaKM2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KM2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KM2 := by
  refine ⟨kappaKM2, ?_, ?_⟩ <;> unfold Link KM2 kappaKM2 <;> decide

theorem familyFacts_KM2 : FamilyFacts KM2 :=
  ⟨KM2_card, by unfold Link KM2; decide,
    by intro i; fin_cases i <;> (unfold Link KM2; decide)⟩

theorem compLabel_KM2 : CompLabel KM2 cM3 := by
  unfold CompLabel Link KM2 cM3; decide

theorem typesInside_KM2 : TypesInside KM2 cM3 := by
  unfold TypesInside KM2 cM3; decide

theorem localWalk4_KM2 (k : Fin 4) : LocalWalk4 KM2 cM3 k := by
  revert k; unfold LocalWalk4 Link KM2 cM3; decide

theorem isolatedMono_KM2 : IsolatedMono KM2 3 := by unfold IsolatedMono KM2; decide

/-- The canonical integral witness for `KM2`. -/
def canon_KM2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 + 2 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 + 2 * u 1 1 - 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2) / 2), ({0,1,2}, (-2 * u 1 1 + 1 * u 1 2) / 1), ({1,1,2}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KM2 (k : Fin 4) : ∀ u, ScalarHyp KM2 u → CountsInside cM3 k u →
    ∃ w, LatEq KM2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KM2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM2; decide)
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
  refine ⟨canon_KM2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KM2, canon_KM2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KM2 (k : Fin 4) : Even3Inside KM2 cM3 k :=
  even3Inside_of_scalar_five KM2 cM3 k fiveStep_KM2 KM2_card (scalar_inside_KM2 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KM2 : ∀ u c0, ScalarHyp KM2 u → LatEq KM2 u c0 →
    ∃ c, LatEq KM2 u c ∧ ∀ τ ∈ KM2, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KM2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KM2, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KM2 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KM2, canon_KM2, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KM2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KM2, coeffList] <;> omega

/-- **`UniversalCert KM2`** (no `ThreeStepLinks`: `KappaLinks` terminal absorbers). -/
theorem universalCert_KM2 : UniversalCert KM2 := by
  have hB : WitnessBoundK KM2 168 2040 := by
    rw [show (2040 : ℕ) = KM2.card * (2 * 168 + 4) by rw [KM2_card_eq]]
    exact witnessBound_of_latEq_lowerK KM2 KM2_card 2 scalar_witness_KM2 168
  exact universalCert_of_even3_components_kappa KM2 cM3 compLabel_KM2 typesInside_KM2
    KM2_card kappaLinks_KM2 localWalk4_KM2 even3Inside_KM2 2040 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 011 012 122 333}`. -/
noncomputable def KM3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KM3_card : ∀ τ ∈ KM3, Multiset.card τ = 3 := by unfold KM3; decide

theorem KM3_card_eq : KM3.card = 7 := by unfold KM3; decide

theorem not_threeStep_KM3 : ¬ ThreeStepLinks KM3 := by unfold ThreeStepLinks Link KM3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KM3 : FiveStepLinks KM3 := by
  unfold FiveStepLinks Link KM3; decide

def kappaKM3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KM3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KM3 := by
  refine ⟨kappaKM3, ?_, ?_⟩ <;> unfold Link KM3 kappaKM3 <;> decide

theorem familyFacts_KM3 : FamilyFacts KM3 :=
  ⟨KM3_card, by unfold Link KM3; decide,
    by intro i; fin_cases i <;> (unfold Link KM3; decide)⟩

theorem compLabel_KM3 : CompLabel KM3 cM3 := by
  unfold CompLabel Link KM3 cM3; decide

theorem typesInside_KM3 : TypesInside KM3 cM3 := by
  unfold TypesInside KM3 cM3; decide

theorem localWalk4_KM3 (k : Fin 4) : LocalWalk4 KM3 cM3 k := by
  revert k; unfold LocalWalk4 Link KM3 cM3; decide

theorem isolatedMono_KM3 : IsolatedMono KM3 3 := by unfold IsolatedMono KM3; decide

/-- The canonical integral witness for `KM3`. -/
def canon_KM3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 + 2 * u 1 2 - 4 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2 - 2 * u 2 2) / 1), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KM3 (k : Fin 4) : ∀ u, ScalarHyp KM3 u → CountsInside cM3 k u →
    ∃ w, LatEq KM3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM3; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
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
  refine ⟨canon_KM3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KM3, canon_KM3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KM3 (k : Fin 4) : Even3Inside KM3 cM3 k :=
  even3Inside_of_scalar_five KM3 cM3 k fiveStep_KM3 KM3_card (scalar_inside_KM3 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KM3 : ∀ u c0, ScalarHyp KM3 u → LatEq KM3 u c0 →
    ∃ c, LatEq KM3 u c ∧ ∀ τ ∈ KM3, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KM3, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KM3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KM3, canon_KM3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KM3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KM3, coeffList] <;> omega

/-- **`UniversalCert KM3`** (no `ThreeStepLinks`: `KappaLinks` terminal absorbers). -/
theorem universalCert_KM3 : UniversalCert KM3 := by
  have hB : WitnessBoundK KM3 168 2380 := by
    rw [show (2380 : ℕ) = KM3.card * (2 * 168 + 4) by rw [KM3_card_eq]]
    exact witnessBound_of_latEq_lowerK KM3 KM3_card 2 scalar_witness_KM3 168
  exact universalCert_of_even3_components_kappa KM3 cM3 compLabel_KM3 typesInside_KM3
    KM3_card kappaLinks_KM3 localWalk4_KM3 even3Inside_KM3 2380 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 022 112 333}`. -/
noncomputable def KM4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KM4_card : ∀ τ ∈ KM4, Multiset.card τ = 3 := by unfold KM4; decide

theorem KM4_card_eq : KM4.card = 7 := by unfold KM4; decide

theorem not_threeStep_KM4 : ¬ ThreeStepLinks KM4 := by unfold ThreeStepLinks Link KM4; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KM4 : FiveStepLinks KM4 := by
  unfold FiveStepLinks Link KM4; decide

def kappaKM4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KM4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KM4 := by
  refine ⟨kappaKM4, ?_, ?_⟩ <;> unfold Link KM4 kappaKM4 <;> decide

theorem familyFacts_KM4 : FamilyFacts KM4 :=
  ⟨KM4_card, by unfold Link KM4; decide,
    by intro i; fin_cases i <;> (unfold Link KM4; decide)⟩

theorem compLabel_KM4 : CompLabel KM4 cM3 := by
  unfold CompLabel Link KM4 cM3; decide

theorem typesInside_KM4 : TypesInside KM4 cM3 := by
  unfold TypesInside KM4 cM3; decide

theorem localWalk4_KM4 (k : Fin 4) : LocalWalk4 KM4 cM3 k := by
  revert k; unfold LocalWalk4 Link KM4 cM3; decide

theorem isolatedMono_KM4 : IsolatedMono KM4 3 := by unfold IsolatedMono KM4; decide

/-- The canonical integral witness for `KM4`. -/
def canon_KM4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 4 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 4 * u 2 2) / 2), ({0,1,1}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 2), ({0,1,2}, (1 * u 0 2 - 2 * u 2 2) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KM4 (k : Fin 4) : ∀ u, ScalarHyp KM4 u → CountsInside cM3 k u →
    ∃ w, LatEq KM4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM4; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
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
  refine ⟨canon_KM4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KM4, canon_KM4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KM4 (k : Fin 4) : Even3Inside KM4 cM3 k :=
  even3Inside_of_scalar_five KM4 cM3 k fiveStep_KM4 KM4_card (scalar_inside_KM4 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KM4 : ∀ u c0, ScalarHyp KM4 u → LatEq KM4 u c0 →
    ∃ c, LatEq KM4 u c ∧ ∀ τ ∈ KM4, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KM4, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KM4 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KM4, canon_KM4, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KM4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KM4, coeffList] <;> omega

/-- **`UniversalCert KM4`** (no `ThreeStepLinks`: `KappaLinks` terminal absorbers). -/
theorem universalCert_KM4 : UniversalCert KM4 := by
  have hB : WitnessBoundK KM4 168 2380 := by
    rw [show (2380 : ℕ) = KM4.card * (2 * 168 + 4) by rw [KM4_card_eq]]
    exact witnessBound_of_latEq_lowerK KM4 KM4_card 2 scalar_witness_KM4 168
  exact universalCert_of_even3_components_kappa KM4 cM3 compLabel_KM4 typesInside_KM4
    KM4_card kappaLinks_KM4 localWalk4_KM4 even3Inside_KM4 2380 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 011 012 111 122 333}`. -/
noncomputable def KM5 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 1}, {1, 2, 2}, {3, 3, 3}}

theorem KM5_card : ∀ τ ∈ KM5, Multiset.card τ = 3 := by unfold KM5; decide

theorem KM5_card_eq : KM5.card = 8 := by unfold KM5; decide

theorem not_threeStep_KM5 : ¬ ThreeStepLinks KM5 := by unfold ThreeStepLinks Link KM5; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KM5 : FiveStepLinks KM5 := by
  unfold FiveStepLinks Link KM5; decide

def kappaKM5 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KM5 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KM5 := by
  refine ⟨kappaKM5, ?_, ?_⟩ <;> unfold Link KM5 kappaKM5 <;> decide

theorem familyFacts_KM5 : FamilyFacts KM5 :=
  ⟨KM5_card, by unfold Link KM5; decide,
    by intro i; fin_cases i <;> (unfold Link KM5; decide)⟩

theorem compLabel_KM5 : CompLabel KM5 cM3 := by
  unfold CompLabel Link KM5 cM3; decide

theorem typesInside_KM5 : TypesInside KM5 cM3 := by
  unfold TypesInside KM5 cM3; decide

theorem localWalk4_KM5 (k : Fin 4) : LocalWalk4 KM5 cM3 k := by
  revert k; unfold LocalWalk4 Link KM5 cM3; decide

theorem isolatedMono_KM5 : IsolatedMono KM5 3 := by unfold IsolatedMono KM5; decide

/-- The canonical integral witness for `KM5`. -/
def canon_KM5 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 + 2 * u 1 2 - 4 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2 - 2 * u 2 2) / 1), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KM5 (k : Fin 4) : ∀ u, ScalarHyp KM5 u → CountsInside cM3 k u →
    ∃ w, LatEq KM5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM5; decide)
  have hsplit : u 3 3 = 0 ∨ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0) := by
    by_cases hk : k = cM3 3
    · subst hk
      right
      exact ⟨hin 0 0 (by left; decide),
        hin 0 1 (by left; decide),
        hin 0 2 (by left; decide),
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
  refine ⟨canon_KM5 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KM5, canon_KM5, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KM5 (k : Fin 4) : Even3Inside KM5 cM3 k :=
  even3Inside_of_scalar_five KM5 cM3 k fiveStep_KM5 KM5_card (scalar_inside_KM5 k)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KM5 : ∀ u c0, ScalarHyp KM5 u → LatEq KM5 u c0 →
    ∃ c, LatEq KM5 u c ∧ ∀ τ ∈ KM5, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KM5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KM5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KM5; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KM5, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KM5 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KM5, canon_KM5, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KM5, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KM5, coeffList] <;> omega

/-- **`UniversalCert KM5`** (no `ThreeStepLinks`: `KappaLinks` terminal absorbers). -/
theorem universalCert_KM5 : UniversalCert KM5 := by
  have hB : WitnessBoundK KM5 168 2720 := by
    rw [show (2720 : ℕ) = KM5.card * (2 * 168 + 4) by rw [KM5_card_eq]]
    exact witnessBound_of_latEq_lowerK KM5 KM5_card 2 scalar_witness_KM5 168
  exact universalCert_of_even3_components_kappa KM5 cM3 compLabel_KM5 typesInside_KM5
    KM5_card kappaLinks_KM5 localWalk4_KM5 even3Inside_KM5 2720 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KM1
#print axioms PaddedComponents.universalCert_KM2
#print axioms PaddedComponents.universalCert_KM3
#print axioms PaddedComponents.universalCert_KM4
#print axioms PaddedComponents.universalCert_KM5
