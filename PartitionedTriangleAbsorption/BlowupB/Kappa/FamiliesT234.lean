/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.Families

@[expose] public section

/-!
# Three more connected trivial-lattice families without `ThreeStepLinks`: `KT2`, `KT3`, `KT4`

Same route as `KT1` (`Kappa/Families.lean`): explicit `κ` for `KappaLinks`, `FiveStepLinks` collapse,
explicit integral witnesses (`kappa_data.py`), Aristotle's walk refiner with the `KappaLinks` terminal
absorbers.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedGeneral

noncomputable def KT2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}}

theorem KT2_card : ∀ τ ∈ KT2, Multiset.card τ = 3 := by decide

theorem not_threeStep_KT2 : ¬ ThreeStepLinks KT2 := by
  unfold ThreeStepLinks Link KT2; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KT2 : FiveStepLinks KT2 := by
  unfold FiveStepLinks Link KT2; decide

def kappaKT2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 1, 0, 0]]

theorem kappaLinks_KT2 : BlowupB.Kappa.KappaLinks KT2 := by
  refine ⟨kappaKT2, ?_, ?_⟩ <;> unfold Link KT2 kappaKT2 <;> decide

theorem walk4_KT2 : Walk4 (fun i j : Fin 4 => ∃ k, Link KT2 i j k) := by
  unfold Walk4; beta_reduce; unfold Link KT2; decide

theorem familyFacts_KT2 : FamilyFacts KT2 :=
  ⟨KT2_card, by unfold Link KT2; decide, by intro i; fin_cases i <;> (unfold Link KT2; decide)⟩

set_option maxHeartbeats 4000000 in
theorem scalar_KT2 : ∀ u, ScalarHyp KT2 u →
    ∃ c, LatEq KT2 u c ∧ ∀ τ ∈ KT2, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KT2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KT2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KT2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KT2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3 ⊢
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3 ⊢
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - u 1 1 + u 1 3 / 2) - (u 0 2 / 2 - u 2 2)) / 3),
    ({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 3 / 2),
    ({0,0,2}, u 0 2 / 2 - u 2 2),
    ({0,1,1}, u 1 1 - u 1 3 / 2),
    ({0,2,2}, u 2 2),
    ({1,1,3}, u 1 3 / 2)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KT2, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [KT2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_KT2 (K : ℕ) :
    TrivialLattice KT2 ∧ WitnessBoundK KT2 K (KT2.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar_five KT2 fiveStep_KT2 KT2_card scalar_KT2 K

theorem KT2_budgets :
    terminalOrder 168 (KT2.card * (2 * 168 + 4)) 4 ≤ 2 ^ 21 ∧
    terminalSize 168 (KT2.card * (2 * 168 + 4)) ≤ 2 ^ 21 := by
  unfold KT2 terminalOrder terminalSize; decide

theorem universalCert_KT2 : UniversalCert KT2 :=
  universalCert_of_trivial_walk_kappa KT2 KT2_card kappaLinks_KT2 walk4_KT2
    (lattice_KT2 168).1 _ (lattice_KT2 168).2 KT2_budgets.1 KT2_budgets.2

noncomputable def KT3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 3}}

theorem KT3_card : ∀ τ ∈ KT3, Multiset.card τ = 3 := by decide

theorem not_threeStep_KT3 : ¬ ThreeStepLinks KT3 := by
  unfold ThreeStepLinks Link KT3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KT3 : FiveStepLinks KT3 := by
  unfold FiveStepLinks Link KT3; decide

def kappaKT3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 2], ![0, 0, 2, 0]]

theorem kappaLinks_KT3 : BlowupB.Kappa.KappaLinks KT3 := by
  refine ⟨kappaKT3, ?_, ?_⟩ <;> unfold Link KT3 kappaKT3 <;> decide

theorem walk4_KT3 : Walk4 (fun i j : Fin 4 => ∃ k, Link KT3 i j k) := by
  unfold Walk4; beta_reduce; unfold Link KT3; decide

theorem familyFacts_KT3 : FamilyFacts KT3 :=
  ⟨KT3_card, by unfold Link KT3; decide, by intro i; fin_cases i <;> (unfold Link KT3; decide)⟩

set_option maxHeartbeats 4000000 in
theorem scalar_KT3 : ∀ u, ScalarHyp KT3 u →
    ∃ c, LatEq KT3 u c ∧ ∀ τ ∈ KT3, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KT3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KT3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KT3; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KT3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3 ⊢
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3 ⊢
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - u 1 1 + u 1 2 / 2 - u 2 2 + u 2 3 / 2)) / 3),
    ({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 2 / 2 - u 2 2 + u 2 3 / 2),
    ({0,1,1}, u 1 1 - u 1 2 / 2 + u 2 2 - u 2 3 / 2),
    ({1,1,2}, u 1 2 / 2 - u 2 2 + u 2 3 / 2),
    ({1,2,2}, u 2 2 - u 2 3 / 2),
    ({2,2,3}, u 2 3 / 2)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KT3, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [KT3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_KT3 (K : ℕ) :
    TrivialLattice KT3 ∧ WitnessBoundK KT3 K (KT3.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar_five KT3 fiveStep_KT3 KT3_card scalar_KT3 K

theorem KT3_budgets :
    terminalOrder 168 (KT3.card * (2 * 168 + 4)) 4 ≤ 2 ^ 21 ∧
    terminalSize 168 (KT3.card * (2 * 168 + 4)) ≤ 2 ^ 21 := by
  unfold KT3 terminalOrder terminalSize; decide

theorem universalCert_KT3 : UniversalCert KT3 :=
  universalCert_of_trivial_walk_kappa KT3 KT3_card kappaLinks_KT3 walk4_KT3
    (lattice_KT3 168).1 _ (lattice_KT3 168).2 KT3_budgets.1 KT3_budgets.2

noncomputable def KT4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 3}}

theorem KT4_card : ∀ τ ∈ KT4, Multiset.card τ = 3 := by decide

theorem not_threeStep_KT4 : ¬ ThreeStepLinks KT4 := by
  unfold ThreeStepLinks Link KT4; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KT4 : FiveStepLinks KT4 := by
  unfold FiveStepLinks Link KT4; decide

def kappaKT4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2], ![0, 0, 2, 0]]

theorem kappaLinks_KT4 : BlowupB.Kappa.KappaLinks KT4 := by
  refine ⟨kappaKT4, ?_, ?_⟩ <;> unfold Link KT4 kappaKT4 <;> decide

theorem walk4_KT4 : Walk4 (fun i j : Fin 4 => ∃ k, Link KT4 i j k) := by
  unfold Walk4; beta_reduce; unfold Link KT4; decide

theorem familyFacts_KT4 : FamilyFacts KT4 :=
  ⟨KT4_card, by unfold Link KT4; decide, by intro i; fin_cases i <;> (unfold Link KT4; decide)⟩

set_option maxHeartbeats 4000000 in
theorem scalar_KT4 : ∀ u, ScalarHyp KT4 u →
    ∃ c, LatEq KT4 u c ∧ ∀ τ ∈ KT4, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KT4; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KT4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KT4; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KT4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3 ⊢
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3 ⊢
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - u 1 1) - (u 0 2 / 2 - u 2 2 + u 2 3 / 2)) / 3),
    ({0,0,1}, u 0 1 / 2 - u 1 1),
    ({0,0,2}, u 0 2 / 2 - u 2 2 + u 2 3 / 2),
    ({0,1,1}, u 1 1),
    ({0,2,2}, u 2 2 - u 2 3 / 2),
    ({1,1,1}, 0),
    ({2,2,3}, u 2 3 / 2)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KT4, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [KT4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_KT4 (K : ℕ) :
    TrivialLattice KT4 ∧ WitnessBoundK KT4 K (KT4.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar_five KT4 fiveStep_KT4 KT4_card scalar_KT4 K

theorem KT4_budgets :
    terminalOrder 168 (KT4.card * (2 * 168 + 4)) 4 ≤ 2 ^ 21 ∧
    terminalSize 168 (KT4.card * (2 * 168 + 4)) ≤ 2 ^ 21 := by
  unfold KT4 terminalOrder terminalSize; decide

theorem universalCert_KT4 : UniversalCert KT4 :=
  universalCert_of_trivial_walk_kappa KT4 KT4_card kappaLinks_KT4 walk4_KT4
    (lattice_KT4 168).1 _ (lattice_KT4 168).2 KT4_budgets.1 KT4_budgets.2

end PaddedNoCommon

#print axioms PaddedNoCommon.universalCert_KT2
#print axioms PaddedNoCommon.universalCert_KT3
#print axioms PaddedNoCommon.universalCert_KT4
