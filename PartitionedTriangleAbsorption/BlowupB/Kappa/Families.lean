/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.LatticeFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.UniversalWalk

@[expose] public section

/-!
# The first family without `ThreeStepLinks`: `KT1 = {000, 001, 002, 011, 113}`

Allowed pairs 00, 01, 02, 11, 13 (as `FnA`, which is `KT1 ∪ {111}`). In the link of class 1 the
pair `3, 3` has no walk of length three (only `3-1-0-0-1-3`, of length five), so `ThreeStepLinks`
fails (`not_threeStep_KT1`). `KappaLinks` holds with the explicit choice `κ` below, and
`FiveStepLinks` holds; the lattice is trivial with the unique witness

  `c113 = u13/2, c011 = u11 - u13/2, c001 = u01/2 - u11 + u13/2, c002 = u02/2,
   c000 = (u00 - c001 - c002)/3`.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedGeneral

noncomputable def KT1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}}

theorem KT1_card : ∀ τ ∈ KT1, Multiset.card τ = 3 := by decide

theorem not_threeStep_KT1 : ¬ ThreeStepLinks KT1 := by
  unfold ThreeStepLinks Link KT1; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KT1 : FiveStepLinks KT1 := by
  unfold FiveStepLinks Link KT1; decide

/-- The explicit third-class choice (Python `kappa_data.py`). -/
def kappaKT1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 1, 0, 0]]

theorem kappaLinks_KT1 : BlowupB.Kappa.KappaLinks KT1 := by
  refine ⟨kappaKT1, ?_, ?_⟩ <;> unfold Link KT1 kappaKT1 <;> decide

theorem walk4_KT1 : Walk4 (fun i j : Fin 4 => ∃ k, Link KT1 i j k) := by
  unfold Walk4; beta_reduce; unfold Link KT1; decide

theorem familyFacts_KT1 : FamilyFacts KT1 :=
  ⟨KT1_card, by unfold Link KT1; decide, by intro i; fin_cases i <;> (unfold Link KT1; decide)⟩

set_option maxHeartbeats 4000000 in
theorem scalar_KT1 : ∀ u, ScalarHyp KT1 u →
    ∃ c, LatEq KT1 u c ∧ ∀ τ ∈ KT1, -(2 * totalU u + 4) ≤ c τ := by
  intro u hu
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KT1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KT1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KT1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KT1; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KT1; decide)
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
  refine ⟨coeffList [({0,0,0}, (u 0 0 - (u 0 1 / 2 - u 1 1 + u 1 3 / 2) - u 0 2 / 2) / 3),
    ({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 3 / 2),
    ({0,0,2}, u 0 2 / 2),
    ({0,1,1}, u 1 1 - u 1 3 / 2),
    ({1,1,3}, u 1 3 / 2)], ?_, ?_⟩
  · intro i j
    rw [KT1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [coeffList, ite_true, ite_false]
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · intro τ hτ
    simp only [KT1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem lattice_KT1 (K : ℕ) :
    TrivialLattice KT1 ∧ WitnessBoundK KT1 K (KT1.card * (2 * K + 4)) :=
  lattice_inputs_of_scalar_five KT1 fiveStep_KT1 KT1_card scalar_KT1 K

theorem KT1_budgets :
    terminalOrder 168 (KT1.card * (2 * 168 + 4)) 4 ≤ 2 ^ 21 ∧
    terminalSize 168 (KT1.card * (2 * 168 + 4)) ≤ 2 ^ 21 := by
  unfold KT1 terminalOrder terminalSize; decide

/-- **`UniversalCert KT1`** — the first universal certificate for a family without
`ThreeStepLinks`. -/
theorem universalCert_KT1 : UniversalCert KT1 :=
  universalCert_of_trivial_walk_kappa KT1 KT1_card kappaLinks_KT1 walk4_KT1
    (lattice_KT1 168).1 _ (lattice_KT1 168).2 KT1_budgets.1 KT1_budgets.2

end PaddedNoCommon

#print axioms PaddedNoCommon.not_threeStep_KT1
#print axioms PaddedNoCommon.universalCert_KT1
