/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Families

@[expose] public section

/-!
# The six base lattices are trivial, with explicit witnesses

For each base family the integral witness is given by explicit integer formulas in the class-pair
counts (`scalar_*`); for `FnA`, `FnC`, `FnF` (one more type than allowed pairs) one coefficient is
chosen in `{0, 1, 2}` by a residue mod `3`. Every coefficient is at least `-(2e + 4)` where `e` is
the number of edges, so the negative mass is at most `|F| (2e + 4)`. `omega` checks every
equation and bound.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedGeneral

set_option maxHeartbeats 4000000 in
theorem scalar_FnA : ∀ u, ScalarHyp FnA u →
    ∃ c, LatEq FnA u c ∧ ∀ τ ∈ FnA, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnA; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnA; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FnA; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnA; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FnA; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 0 - u 0 2 / 2) % 3 - u 0 2 / 2) / 3),
    ({0,0,1}, (u 0 0 - u 0 2 / 2) % 3),
    ({0,0,2}, u 0 2 / 2),
    ({0,1,1}, u 0 1 / 2 - (u 0 0 - u 0 2 / 2) % 3),
    ({1,1,1}, (u 1 1 - (u 0 1 / 2 - (u 0 0 - u 0 2 / 2) % 3) - u 1 3 / 2) / 3),
    ({1,1,3}, u 1 3 / 2)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnA, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnA, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnA (K : ℕ) :
    TrivialLattice FnA ∧ WitnessBoundK FnA K (FnA.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnA baseFacts_FnA.three baseFacts_FnA.card scalar_FnA K

set_option maxHeartbeats 4000000 in
theorem scalar_FnB : ∀ u, ScalarHyp FnB u →
    ∃ c, LatEq FnB u c ∧ ∀ τ ∈ FnB, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnB; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnB; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link FnB; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnB; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - (u 1 1 - (u 1 3 / 2 - u 3 3))) - u 0 2 / 2) / 3),
    ({0,0,1}, (u 0 1 / 2 - (u 1 1 - (u 1 3 / 2 - u 3 3)))),
    ({0,0,2}, u 0 2 / 2),
    ({0,1,1}, (u 1 1 - (u 1 3 / 2 - u 3 3))),
    ({1,1,3}, (u 1 3 / 2 - u 3 3)),
    ({1,3,3}, u 3 3)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnB, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnB, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnB (K : ℕ) :
    TrivialLattice FnB ∧ WitnessBoundK FnB K (FnB.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnB baseFacts_FnB.three baseFacts_FnB.card scalar_FnB K

set_option maxHeartbeats 4000000 in
theorem scalar_FnC : ∀ u, ScalarHyp FnC u →
    ∃ c, LatEq FnC u c ∧ ∀ τ ∈ FnC, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnC; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnC; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnC; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FnC; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - ((u 0 0 - (u 0 2 / 2 - u 2 2)) % 3) - (u 0 2 / 2 - u 2 2)) / 3),
    ({0,0,1}, ((u 0 0 - (u 0 2 / 2 - u 2 2)) % 3)),
    ({0,0,2}, (u 0 2 / 2 - u 2 2)),
    ({0,1,1}, u 0 1 / 2 - ((u 0 0 - (u 0 2 / 2 - u 2 2)) % 3)),
    ({0,2,2}, u 2 2),
    ({1,1,1}, (u 1 1 - (u 0 1 / 2 - ((u 0 0 - (u 0 2 / 2 - u 2 2)) % 3)) - u 1 3 / 2) / 3),
    ({1,1,3}, u 1 3 / 2)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnC, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnC, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnC (K : ℕ) :
    TrivialLattice FnC ∧ WitnessBoundK FnC K (FnC.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnC baseFacts_FnC.three baseFacts_FnC.card scalar_FnC K

set_option maxHeartbeats 4000000 in
theorem scalar_FnD : ∀ u, ScalarHyp FnD u →
    ∃ c, LatEq FnD u c ∧ ∀ τ ∈ FnD, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnD; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnD; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnD; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - (u 1 1 - (u 1 3 / 2 - u 3 3))) - (u 0 2 / 2 - u 2 2)) / 3),
    ({0,0,1}, (u 0 1 / 2 - (u 1 1 - (u 1 3 / 2 - u 3 3)))),
    ({0,0,2}, (u 0 2 / 2 - u 2 2)),
    ({0,1,1}, (u 1 1 - (u 1 3 / 2 - u 3 3))),
    ({0,2,2}, u 2 2),
    ({1,1,3}, (u 1 3 / 2 - u 3 3)),
    ({1,3,3}, u 3 3)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnD, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnD, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnD (K : ℕ) :
    TrivialLattice FnD ∧ WitnessBoundK FnD K (FnD.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnD baseFacts_FnD.three baseFacts_FnD.card scalar_FnD K

set_option maxHeartbeats 4000000 in
theorem scalar_FnE : ∀ u, ScalarHyp FnE u →
    ∃ c, LatEq FnE u c ∧ ∀ τ ∈ FnE, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FnE; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnE; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FnE; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - (u 1 1 - (u 1 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))))) / 3),
    ({0,0,1}, (u 0 1 / 2 - (u 1 1 - (u 1 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))))),
    ({0,1,1}, (u 1 1 - (u 1 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3))))),
    ({1,1,2}, (u 1 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))),
    ({1,2,2}, (u 2 2 - (u 2 3 / 2 - u 3 3))),
    ({2,2,3}, (u 2 3 / 2 - u 3 3)),
    ({2,3,3}, u 3 3)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnE, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnE, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnE (K : ℕ) :
    TrivialLattice FnE ∧ WitnessBoundK FnE K (FnE.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnE baseFacts_FnE.three baseFacts_FnE.card scalar_FnE K

set_option maxHeartbeats 4000000 in
theorem scalar_FnF : ∀ u, ScalarHyp FnF u →
    ∃ c, LatEq FnF u c ∧ ∀ τ ∈ FnF, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnF; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnF; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FnF; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - ((u 0 0 - (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))) % 3) - (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))) / 3),
    ({0,0,1}, ((u 0 0 - (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))) % 3)),
    ({0,0,2}, (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))),
    ({0,1,1}, u 0 1 / 2 - ((u 0 0 - (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))) % 3)),
    ({0,2,2}, (u 2 2 - (u 2 3 / 2 - u 3 3))),
    ({1,1,1}, (u 1 1 - (u 0 1 / 2 - ((u 0 0 - (u 0 2 / 2 - (u 2 2 - (u 2 3 / 2 - u 3 3)))) % 3))) / 3),
    ({2,2,3}, (u 2 3 / 2 - u 3 3)),
    ({2,3,3}, u 3 3)], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [FnF, coeffList, typeEdgeVec, sum_insert] <;> omega
  · intro τ hτ
    simp only [FnF, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [coeffList] <;> omega

theorem lattice_FnF (K : ℕ) :
    TrivialLattice FnF ∧ WitnessBoundK FnF K (FnF.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar FnF baseFacts_FnF.three baseFacts_FnF.card scalar_FnF K

end PaddedNoCommon

#print axioms PaddedNoCommon.lattice_FnA
#print axioms PaddedNoCommon.lattice_FnB
#print axioms PaddedNoCommon.lattice_FnC
#print axioms PaddedNoCommon.lattice_FnD
#print axioms PaddedNoCommon.lattice_FnE
#print axioms PaddedNoCommon.lattice_FnF
