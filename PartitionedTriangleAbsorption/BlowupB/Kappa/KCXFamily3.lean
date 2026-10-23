/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamily1

@[expose] public section

set_option Elab.async false

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon PaddedCharge

/-- `{000 001 012 022 112 333}`. -/
noncomputable def KCX3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KCX3_card : ∀ τ ∈ KCX3, Multiset.card τ = 3 := by unfold KCX3; decide

theorem KCX3_card_eq : KCX3.card = 6 := by unfold KCX3; decide

theorem not_threeStep_KCX3 : ¬ ThreeStepLinks KCX3 := by unfold ThreeStepLinks Link KCX3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCX3 : FiveStepLinks KCX3 := by
  unfold FiveStepLinks Link KCX3; decide

def kappaKCX3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCX3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCX3 := by
  refine ⟨kappaKCX3, ?_, ?_⟩ <;> unfold Link KCX3 kappaKCX3 <;> decide

theorem familyFacts_KCX3 : FamilyFacts KCX3 :=
  ⟨KCX3_card, by unfold Link KCX3; decide,
    by intro i; fin_cases i <;> (unfold Link KCX3; decide)⟩

theorem compLabel_KCX3 : CompLabel KCX3 cM3 := by
  unfold CompLabel Link KCX3 cM3; decide

theorem typesInside_KCX3 : TypesInside KCX3 cM3 := by
  unfold TypesInside KCX3 cM3; decide

theorem localWalk4_KCX3 (k : Fin 4) : LocalWalk4 KCX3 cM3 k := by
  revert k; unfold LocalWalk4 Link KCX3 cM3; decide

theorem isolatedMono_KCX3 : IsolatedMono KCX3 3 := by unfold IsolatedMono KCX3; decide

def chiKCX3 : Fin 4 → Fin 4 → ℤ := ![![0, 0, -1, 0], ![0, -2, 1, 0], ![-1, 1, 2, 0], ![0, 0, 0, 0]]

theorem chiKCX3_bound : ∀ i j, |chiKCX3 i j| ≤ 2 := by decide
theorem chiKCX3_00 : chiKCX3 0 0 = 0 := rfl
theorem chiKCX3_01 : chiKCX3 0 1 = 0 := rfl
theorem chiKCX3_02 : chiKCX3 0 2 = -1 := rfl
theorem chiKCX3_03 : chiKCX3 0 3 = 0 := rfl
theorem chiKCX3_10 : chiKCX3 1 0 = 0 := rfl
theorem chiKCX3_11 : chiKCX3 1 1 = -2 := rfl
theorem chiKCX3_12 : chiKCX3 1 2 = 1 := rfl
theorem chiKCX3_13 : chiKCX3 1 3 = 0 := rfl
theorem chiKCX3_20 : chiKCX3 2 0 = -1 := rfl
theorem chiKCX3_21 : chiKCX3 2 1 = 1 := rfl
theorem chiKCX3_22 : chiKCX3 2 2 = 2 := rfl
theorem chiKCX3_23 : chiKCX3 2 3 = 0 := rfl
theorem chiKCX3_30 : chiKCX3 3 0 = 0 := rfl
theorem chiKCX3_31 : chiKCX3 3 1 = 0 := rfl
theorem chiKCX3_32 : chiKCX3 3 2 = 0 := rfl
theorem chiKCX3_33 : chiKCX3 3 3 = 0 := rfl

theorem kills_KCX3 : Kills chiKCX3 KCX3 := by
  unfold Kills pair KCX3 chiKCX3; decide

def TpKCX3 : Template KCX3 cM3 (cM3 0) where
  E := cycleSlots
  L := ![0, 0, 0, 1, 2, 1]
  loop := cycleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := cycleSlots_even
  card := cycleSlots_card.le
  inside := by decide

def TmKCX3 : Template KCX3 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide

def TqKCX3 : Template KCX3 cM3 (cM3 0) where
  E := quadSlots
  L := ![0, 0, 0, 0, 0, 0]
  loop := by unfold quadSlots; decide
  act := by unfold ActiveEdges Link quadSlots; decide
  even := by unfold quadSlots; decide
  card := by unfold quadSlots; decide
  inside := by decide

theorem tp_charge_KCX3 : charge chiKCX3 TpKCX3.L TpKCX3.E = 4 := by decide
theorem tm_charge_KCX3 : charge chiKCX3 TmKCX3.L TmKCX3.E = -4 := by decide
theorem tq_charge_KCX3 : charge chiKCX3 TqKCX3.L TqKCX3.E = 0 := by decide
theorem tq_value_KCX3 : psiNum psiOne TqKCX3.L TqKCX3.E % 3 = 1 := by decide

def canon_KCX3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2), ({0,1,2}, (1 * u 0 2 - 2 * u 2 2) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_ct_KCX3 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCX3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCX3 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiOne i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCX3 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX3_00, chiKCX3_01, chiKCX3_02, chiKCX3_03, chiKCX3_10, chiKCX3_11, chiKCX3_12, chiKCX3_13, chiKCX3_20, chiKCX3_21, chiKCX3_22, chiKCX3_23, chiKCX3_30, chiKCX3_31, chiKCX3_32, chiKCX3_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCX3 u, ?_⟩
  intro i j
  rw [KCX3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KCX3, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeTorsionInside_KCX3 : ChargeTorsionInside KCX3 cM3 (cM3 0) chiKCX3 psiOne := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCX3 KCX3_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hch := hg.2.2.2.1
  rw [charge_counts] at hch
  have hψ : (3 : ℤ) ∣ psiNum psiOne p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_ct_KCX3 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1) hch hψ
    (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCX3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCX3 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCX3 L) :
    psiVal psiOne p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCX3 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiOne p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e03 := h 0 3
    have e11 := h 1 1
    have e12 := h 1 2
    have e13 := h 1 3
    have e22 := h 2 2
    have e23 := h 2 3
    have e33 := h 3 3
    simp (config := {decide := true}) only [KCX3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_KCX3 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCX3 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKCX3 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCX3) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX3_00, chiKCX3_01, chiKCX3_02, chiKCX3_03, chiKCX3_10, chiKCX3_11, chiKCX3_12, chiKCX3_13, chiKCX3_20, chiKCX3_21, chiKCX3_22, chiKCX3_23, chiKCX3_30, chiKCX3_31, chiKCX3_32, chiKCX3_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCX3 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCX3 u →
    CountsInside cM3 k u → ∃ w, LatEq KCX3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX3; decide)
  have hz : u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0 := ⟨hin 0 0 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 2 2 (by left; simpa [cM3] using fun h => hk h.symm)⟩
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCX3 u, ?_⟩
  intro i j
  rw [KCX3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KCX3, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KCX3 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCX3 cM3 k :=
  even3Inside_of_scalar_five KCX3 cM3 k fiveStep_KCX3 KCX3_card (scalar_inside_KCX3 k hk)

/-- Per-type lower bounds of the canonical witness. -/
def aKCX3 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,0} then 1 else if τ = {0,0,1} then 1 else if τ = {0,1,2} then 2 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCX3 : ∀ u c0, ScalarHyp KCX3 u → LatEq KCX3 u c0 →
    ∃ c, LatEq KCX3 u c ∧ ∀ τ ∈ KCX3, -((aKCX3 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KCX3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCX3 u, ?_, ?_⟩
  · intro i j
    rw [KCX3]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KCX3, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
    generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
    generalize (1 * u 3 3) / 3 = qv2 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCX3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KCX3, coeffList, aKCX3, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KCX3 : WitnessBoundK KCX3 1230 4944 := by
  have h : WitnessBoundK KCX3 1230 (∑ τ ∈ KCX3, (aKCX3 τ * 1230 + 4)) :=
    witnessBound_of_latEq_lowerA KCX3 KCX3_card aKCX3 scalar_witness_KCX3 1230
  have hv : ∑ τ ∈ KCX3, (aKCX3 τ * 1230 + 4) = 4944 := by unfold KCX3 aKCX3; decide
  rwa [hv] at h

/-- **`UniversalCert KCX3`**. -/
theorem universalCert_KCX3 : UniversalCert KCX3 :=
  universalCert_of_ct_components KCX3 cM3 compLabel_KCX3 typesInside_KCX3 KCX3_card
    kappaLinks_KCX3 localWalk4_KCX3 even3Inside_KCX3 chiKCX3 psiOne chiKCX3_bound kills_KCX3
    chargeTorsionInside_KCX3 (fun p L hin hL => psiVal_of_isIntDiv_KCX3 p L hin hL)
    (fun p A hA hact hin h3 => four_dvd_KCX3 p A hA hact hin h3) TpKCX3 TmKCX3 TqKCX3
    tp_charge_KCX3 tm_charge_KCX3 tq_charge_KCX3 tq_value_KCX3 4944 wb_KCX3
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])


end PaddedComponents

#print axioms PaddedComponents.universalCert_KCX3
