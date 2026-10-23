/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentTorsionT2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentTorsionT2H
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentTorsionT3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# Eight disconnected `ThreeStepLinks` families with a torsion in the component `{0,1,2}`

`KTA1` (census `ℤ/9`): `ℤ/3` inside; `KTB1`–`KTB3` (census `ℤ/6`): `ℤ/2` inside with an integral
functional; `KTH1`–`KTH4` (census `ℤ/6`): `ℤ/2` inside with a half-integral functional
(`(ψ/2) mod 2`, `ψ` even on good sets). Isolated `333`. Generator: `gen_g2.py`.
-/

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

/-- `{000 001 012 022 111 112 222 333}`. -/
noncomputable def KTA1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KTA1_card : ∀ τ ∈ KTA1, Multiset.card τ = 3 := by unfold KTA1; decide

theorem KTA1_card_eq : KTA1.card = 8 := by unfold KTA1; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTA1 : FiveStepLinks KTA1 := by
  unfold FiveStepLinks Link KTA1; decide

def kappaKTA1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTA1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTA1 := by
  refine ⟨kappaKTA1, ?_, ?_⟩ <;> unfold Link KTA1 kappaKTA1 <;> decide

theorem familyFacts_KTA1 : FamilyFacts KTA1 :=
  ⟨KTA1_card, by unfold Link KTA1; decide,
    by intro i; fin_cases i <;> (unfold Link KTA1; decide)⟩

theorem compLabel_KTA1 : CompLabel KTA1 cM3 := by
  unfold CompLabel Link KTA1 cM3; decide

theorem typesInside_KTA1 : TypesInside KTA1 cM3 := by
  unfold TypesInside KTA1 cM3; decide

theorem localWalk4_KTA1 (k : Fin 4) : LocalWalk4 KTA1 cM3 k := by
  revert k; unfold LocalWalk4 Link KTA1 cM3; decide

theorem isolatedMono_KTA1 : IsolatedMono KTA1 3 := by unfold IsolatedMono KTA1; decide

theorem KTA1_three : ThreeStepLinks KTA1 := by unfold ThreeStepLinks Link KTA1; decide

def psiKTA1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 2, 0], ![0, 1, 1, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]
theorem psiKTA1_00 : psiKTA1 0 0 = 0 := rfl
theorem psiKTA1_01 : psiKTA1 0 1 = 0 := rfl
theorem psiKTA1_02 : psiKTA1 0 2 = 2 := rfl
theorem psiKTA1_03 : psiKTA1 0 3 = 0 := rfl
theorem psiKTA1_10 : psiKTA1 1 0 = 0 := rfl
theorem psiKTA1_11 : psiKTA1 1 1 = 1 := rfl
theorem psiKTA1_12 : psiKTA1 1 2 = 1 := rfl
theorem psiKTA1_13 : psiKTA1 1 3 = 0 := rfl
theorem psiKTA1_20 : psiKTA1 2 0 = 0 := rfl
theorem psiKTA1_21 : psiKTA1 2 1 = 0 := rfl
theorem psiKTA1_22 : psiKTA1 2 2 = 2 := rfl
theorem psiKTA1_23 : psiKTA1 2 3 = 0 := rfl
theorem psiKTA1_30 : psiKTA1 3 0 = 0 := rfl
theorem psiKTA1_31 : psiKTA1 3 1 = 0 := rfl
theorem psiKTA1_32 : psiKTA1 3 2 = 0 := rfl
theorem psiKTA1_33 : psiKTA1 3 3 = 0 := rfl

def TrKTA1 : Template KTA1 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTA1 : 3 ∣ TrKTA1.E.card := by unfold TrKTA1; decide
theorem tr_value_KTA1 : psiNum psiKTA1 TrKTA1.L TrKTA1.E % 3 = 1 := by decide

def canon_KTA1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2), ({0,1,2}, (1 * u 0 2 - 2 * u 2 2) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,1}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6), ({1,1,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTA1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTA1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKTA1 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTA1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTA1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTA1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTA1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTA1_00, psiKTA1_01, psiKTA1_02, psiKTA1_03, psiKTA1_10, psiKTA1_11, psiKTA1_12, psiKTA1_13, psiKTA1_20, psiKTA1_21, psiKTA1_22, psiKTA1_23, psiKTA1_30, psiKTA1_31, psiKTA1_32, psiKTA1_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTA1 u, ?_⟩
  intro i j
  rw [KTA1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTA1, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 * 6 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 * 2 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 = qv2 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem torsionInside_KTA1 : TorsionInside KTA1 cM3 (cM3 0) psiKTA1 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTA1 KTA1_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKTA1 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTA1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTA1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTA1 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTA1 L) :
    psiVal psiKTA1 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTA1 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKTA1 p L := by
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
    simp (config := {decide := true}) only [KTA1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTA1_00, psiKTA1_01, psiKTA1_02, psiKTA1_03, psiKTA1_10, psiKTA1_11, psiKTA1_12, psiKTA1_13, psiKTA1_20, psiKTA1_21, psiKTA1_22, psiKTA1_23, psiKTA1_30, psiKTA1_31, psiKTA1_32, psiKTA1_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTA1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTA1 u →
    CountsInside cM3 k u → ∃ w, LatEq KTA1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTA1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTA1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTA1; decide)
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
  refine ⟨canon_KTA1 u, ?_⟩
  intro i j
  rw [KTA1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTA1, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 * 6 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 * 2 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 = qv2 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTA1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTA1 cM3 k :=
  even3Inside_of_scalar_five KTA1 cM3 k fiveStep_KTA1 KTA1_card (scalar_inside_KTA1 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTA1 : ∀ u c0, ScalarHyp KTA1 u → LatEq KTA1 u c0 →
    ∃ c, LatEq KTA1 u c ∧ ∀ τ ∈ KTA1, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTA1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTA1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTA1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTA1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTA1 u, ?_, ?_⟩
  · intro i j
    rw [KTA1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTA1, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 * 2 = 1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 * 6 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 * 2 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6 = qv0 at *
    generalize (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2 = qv1 at *
    generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6 = qv2 at *
    generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2 = qv3 at *
    generalize (1 * u 3 3) / 3 = qv4 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTA1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTA1, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTA1 : UniversalCert KTA1 := by
  have hB : WitnessBoundK KTA1 222 3584 := by
    rw [show (3584 : ℕ) = KTA1.card * (2 * 222 + 4) by rw [KTA1_card_eq]]
    exact witnessBound_of_latEq_lowerK KTA1 KTA1_card 2 scalar_witness_KTA1 222
  exact universalCert_of_torsion_components_T3 KTA1 cM3 compLabel_KTA1 typesInside_KTA1 KTA1_card
    kappaLinks_KTA1 localWalk4_KTA1 even3Inside_KTA1 psiKTA1 torsionInside_KTA1
    (fun p L hin hL => psiVal_of_isIntDiv_KTA1 p L hin hL) TrKTA1 tr3_KTA1 tr_value_KTA1 3584 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 011 022 112 122 333}`. -/
noncomputable def KTB1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KTB1_card : ∀ τ ∈ KTB1, Multiset.card τ = 3 := by unfold KTB1; decide

theorem KTB1_card_eq : KTB1.card = 8 := by unfold KTB1; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTB1 : FiveStepLinks KTB1 := by
  unfold FiveStepLinks Link KTB1; decide

def kappaKTB1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTB1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTB1 := by
  refine ⟨kappaKTB1, ?_, ?_⟩ <;> unfold Link KTB1 kappaKTB1 <;> decide

theorem familyFacts_KTB1 : FamilyFacts KTB1 :=
  ⟨KTB1_card, by unfold Link KTB1; decide,
    by intro i; fin_cases i <;> (unfold Link KTB1; decide)⟩

theorem compLabel_KTB1 : CompLabel KTB1 cM3 := by
  unfold CompLabel Link KTB1 cM3; decide

theorem typesInside_KTB1 : TypesInside KTB1 cM3 := by
  unfold TypesInside KTB1 cM3; decide

theorem localWalk4_KTB1 (k : Fin 4) : LocalWalk4 KTB1 cM3 k := by
  revert k; unfold LocalWalk4 Link KTB1 cM3; decide

theorem isolatedMono_KTB1 : IsolatedMono KTB1 3 := by unfold IsolatedMono KTB1; decide

theorem KTB1_three : ThreeStepLinks KTB1 := by unfold ThreeStepLinks Link KTB1; decide

def psiKTB1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem psiKTB1_00 : psiKTB1 0 0 = 0 := rfl
theorem psiKTB1_01 : psiKTB1 0 1 = 0 := rfl
theorem psiKTB1_02 : psiKTB1 0 2 = 0 := rfl
theorem psiKTB1_03 : psiKTB1 0 3 = 0 := rfl
theorem psiKTB1_10 : psiKTB1 1 0 = 0 := rfl
theorem psiKTB1_11 : psiKTB1 1 1 = 0 := rfl
theorem psiKTB1_12 : psiKTB1 1 2 = 1 := rfl
theorem psiKTB1_13 : psiKTB1 1 3 = 0 := rfl
theorem psiKTB1_20 : psiKTB1 2 0 = 0 := rfl
theorem psiKTB1_21 : psiKTB1 2 1 = 0 := rfl
theorem psiKTB1_22 : psiKTB1 2 2 = 0 := rfl
theorem psiKTB1_23 : psiKTB1 2 3 = 0 := rfl
theorem psiKTB1_30 : psiKTB1 3 0 = 0 := rfl
theorem psiKTB1_31 : psiKTB1 3 1 = 0 := rfl
theorem psiKTB1_32 : psiKTB1 3 2 = 0 := rfl
theorem psiKTB1_33 : psiKTB1 3 3 = 0 := rfl

def TrKTB1 : Template KTB1 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 1, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTB1 : 3 ∣ TrKTB1.E.card := by unfold TrKTB1; decide
theorem tr_value_KTB1 : psiNum psiKTB1 TrKTB1.L TrKTB1.E % 2 = 1 := by decide

def canon_KTB1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2) / 2), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTB1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTB1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (2 : ℤ) ∣ ∑ i, ∑ j, psiKTB1 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTB1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTB1_00, psiKTB1_01, psiKTB1_02, psiKTB1_03, psiKTB1_10, psiKTB1_11, psiKTB1_12, psiKTB1_13, psiKTB1_20, psiKTB1_21, psiKTB1_22, psiKTB1_23, psiKTB1_30, psiKTB1_31, psiKTB1_32, psiKTB1_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTB1 u, ?_⟩
  intro i j
  rw [KTB1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB1, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem torsionInside_KTB1 : TorsionInsideB KTB1 cM3 (cM3 0) psiKTB1 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTB1 KTB1_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (2 : ℤ) ∣ psiNum psiKTB1 p E := by unfold psiValB at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTB1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTB1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTB1 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTB1 L) :
    psiValB psiKTB1 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTB1 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (2 : ℤ) ∣ psiNum psiKTB1 p L := by
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
    simp (config := {decide := true}) only [KTB1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTB1_00, psiKTB1_01, psiKTB1_02, psiKTB1_03, psiKTB1_10, psiKTB1_11, psiKTB1_12, psiKTB1_13, psiKTB1_20, psiKTB1_21, psiKTB1_22, psiKTB1_23, psiKTB1_30, psiKTB1_31, psiKTB1_32, psiKTB1_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValB; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTB1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTB1 u →
    CountsInside cM3 k u → ∃ w, LatEq KTB1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB1; decide)
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
  refine ⟨canon_KTB1 u, ?_⟩
  intro i j
  rw [KTB1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB1, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTB1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTB1 cM3 k :=
  even3Inside_of_scalar_five KTB1 cM3 k fiveStep_KTB1 KTB1_card (scalar_inside_KTB1 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTB1 : ∀ u c0, ScalarHyp KTB1 u → LatEq KTB1 u c0 →
    ∃ c, LatEq KTB1 u c ∧ ∀ τ ∈ KTB1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTB1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTB1 u, ?_, ?_⟩
  · intro i j
    rw [KTB1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTB1, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
    generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
    generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
    generalize (1 * u 1 2) / 2 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTB1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTB1, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTB1 : UniversalCert KTB1 := by
  have hB : WitnessBoundK KTB1 204 1664 := by
    rw [show (1664 : ℕ) = KTB1.card * (1 * 204 + 4) by rw [KTB1_card_eq]]
    exact witnessBound_of_latEq_lowerK KTB1 KTB1_card 1 scalar_witness_KTB1 204
  exact universalCert_of_torsion_components_T2 KTB1 cM3 compLabel_KTB1 typesInside_KTB1 KTB1_card
    kappaLinks_KTB1 localWalk4_KTB1 even3Inside_KTB1 psiKTB1 torsionInside_KTB1
    (fun p L hin hL => psiVal_of_isIntDiv_KTB1 p L hin hL) TrKTB1 tr3_KTB1 tr_value_KTB1 1664 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 011 022 111 112 122 333}`. -/
noncomputable def KTB2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KTB2_card : ∀ τ ∈ KTB2, Multiset.card τ = 3 := by unfold KTB2; decide

theorem KTB2_card_eq : KTB2.card = 9 := by unfold KTB2; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTB2 : FiveStepLinks KTB2 := by
  unfold FiveStepLinks Link KTB2; decide

def kappaKTB2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTB2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTB2 := by
  refine ⟨kappaKTB2, ?_, ?_⟩ <;> unfold Link KTB2 kappaKTB2 <;> decide

theorem familyFacts_KTB2 : FamilyFacts KTB2 :=
  ⟨KTB2_card, by unfold Link KTB2; decide,
    by intro i; fin_cases i <;> (unfold Link KTB2; decide)⟩

theorem compLabel_KTB2 : CompLabel KTB2 cM3 := by
  unfold CompLabel Link KTB2 cM3; decide

theorem typesInside_KTB2 : TypesInside KTB2 cM3 := by
  unfold TypesInside KTB2 cM3; decide

theorem localWalk4_KTB2 (k : Fin 4) : LocalWalk4 KTB2 cM3 k := by
  revert k; unfold LocalWalk4 Link KTB2 cM3; decide

theorem isolatedMono_KTB2 : IsolatedMono KTB2 3 := by unfold IsolatedMono KTB2; decide

theorem KTB2_three : ThreeStepLinks KTB2 := by unfold ThreeStepLinks Link KTB2; decide

def psiKTB2 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem psiKTB2_00 : psiKTB2 0 0 = 0 := rfl
theorem psiKTB2_01 : psiKTB2 0 1 = 0 := rfl
theorem psiKTB2_02 : psiKTB2 0 2 = 0 := rfl
theorem psiKTB2_03 : psiKTB2 0 3 = 0 := rfl
theorem psiKTB2_10 : psiKTB2 1 0 = 0 := rfl
theorem psiKTB2_11 : psiKTB2 1 1 = 0 := rfl
theorem psiKTB2_12 : psiKTB2 1 2 = 1 := rfl
theorem psiKTB2_13 : psiKTB2 1 3 = 0 := rfl
theorem psiKTB2_20 : psiKTB2 2 0 = 0 := rfl
theorem psiKTB2_21 : psiKTB2 2 1 = 0 := rfl
theorem psiKTB2_22 : psiKTB2 2 2 = 0 := rfl
theorem psiKTB2_23 : psiKTB2 2 3 = 0 := rfl
theorem psiKTB2_30 : psiKTB2 3 0 = 0 := rfl
theorem psiKTB2_31 : psiKTB2 3 1 = 0 := rfl
theorem psiKTB2_32 : psiKTB2 3 2 = 0 := rfl
theorem psiKTB2_33 : psiKTB2 3 3 = 0 := rfl

def TrKTB2 : Template KTB2 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 1, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTB2 : 3 ∣ TrKTB2.E.card := by unfold TrKTB2; decide
theorem tr_value_KTB2 : psiNum psiKTB2 TrKTB2.L TrKTB2.E % 2 = 1 := by decide

def canon_KTB2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2) / 2), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTB2 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTB2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (2 : ℤ) ∣ ∑ i, ∑ j, psiKTB2 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTB2 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTB2_00, psiKTB2_01, psiKTB2_02, psiKTB2_03, psiKTB2_10, psiKTB2_11, psiKTB2_12, psiKTB2_13, psiKTB2_20, psiKTB2_21, psiKTB2_22, psiKTB2_23, psiKTB2_30, psiKTB2_31, psiKTB2_32, psiKTB2_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTB2 u, ?_⟩
  intro i j
  rw [KTB2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem torsionInside_KTB2 : TorsionInsideB KTB2 cM3 (cM3 0) psiKTB2 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTB2 KTB2_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (2 : ℤ) ∣ psiNum psiKTB2 p E := by unfold psiValB at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTB2 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTB2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTB2 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTB2 L) :
    psiValB psiKTB2 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTB2 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (2 : ℤ) ∣ psiNum psiKTB2 p L := by
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
    simp (config := {decide := true}) only [KTB2, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTB2_00, psiKTB2_01, psiKTB2_02, psiKTB2_03, psiKTB2_10, psiKTB2_11, psiKTB2_12, psiKTB2_13, psiKTB2_20, psiKTB2_21, psiKTB2_22, psiKTB2_23, psiKTB2_30, psiKTB2_31, psiKTB2_32, psiKTB2_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValB; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTB2 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTB2 u →
    CountsInside cM3 k u → ∃ w, LatEq KTB2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB2; decide)
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
  refine ⟨canon_KTB2 u, ?_⟩
  intro i j
  rw [KTB2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTB2 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTB2 cM3 k :=
  even3Inside_of_scalar_five KTB2 cM3 k fiveStep_KTB2 KTB2_card (scalar_inside_KTB2 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTB2 : ∀ u c0, ScalarHyp KTB2 u → LatEq KTB2 u c0 →
    ∃ c, LatEq KTB2 u c ∧ ∀ τ ∈ KTB2, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTB2, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTB2 u, ?_, ?_⟩
  · intro i j
    rw [KTB2]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTB2, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
    generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
    generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
    generalize (1 * u 1 2) / 2 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTB2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTB2, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTB2 : UniversalCert KTB2 := by
  have hB : WitnessBoundK KTB2 204 1872 := by
    rw [show (1872 : ℕ) = KTB2.card * (1 * 204 + 4) by rw [KTB2_card_eq]]
    exact witnessBound_of_latEq_lowerK KTB2 KTB2_card 1 scalar_witness_KTB2 204
  exact universalCert_of_torsion_components_T2 KTB2 cM3 compLabel_KTB2 typesInside_KTB2 KTB2_card
    kappaLinks_KTB2 localWalk4_KTB2 even3Inside_KTB2 psiKTB2 torsionInside_KTB2
    (fun p L hin hL => psiVal_of_isIntDiv_KTB2 p L hin hL) TrKTB2 tr3_KTB2 tr_value_KTB2 1872 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 002 011 022 111 112 122 222 333}`. -/
noncomputable def KTB3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KTB3_card : ∀ τ ∈ KTB3, Multiset.card τ = 3 := by unfold KTB3; decide

theorem KTB3_card_eq : KTB3.card = 10 := by unfold KTB3; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTB3 : FiveStepLinks KTB3 := by
  unfold FiveStepLinks Link KTB3; decide

def kappaKTB3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTB3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTB3 := by
  refine ⟨kappaKTB3, ?_, ?_⟩ <;> unfold Link KTB3 kappaKTB3 <;> decide

theorem familyFacts_KTB3 : FamilyFacts KTB3 :=
  ⟨KTB3_card, by unfold Link KTB3; decide,
    by intro i; fin_cases i <;> (unfold Link KTB3; decide)⟩

theorem compLabel_KTB3 : CompLabel KTB3 cM3 := by
  unfold CompLabel Link KTB3 cM3; decide

theorem typesInside_KTB3 : TypesInside KTB3 cM3 := by
  unfold TypesInside KTB3 cM3; decide

theorem localWalk4_KTB3 (k : Fin 4) : LocalWalk4 KTB3 cM3 k := by
  revert k; unfold LocalWalk4 Link KTB3 cM3; decide

theorem isolatedMono_KTB3 : IsolatedMono KTB3 3 := by unfold IsolatedMono KTB3; decide

theorem KTB3_three : ThreeStepLinks KTB3 := by unfold ThreeStepLinks Link KTB3; decide

def psiKTB3 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem psiKTB3_00 : psiKTB3 0 0 = 0 := rfl
theorem psiKTB3_01 : psiKTB3 0 1 = 0 := rfl
theorem psiKTB3_02 : psiKTB3 0 2 = 0 := rfl
theorem psiKTB3_03 : psiKTB3 0 3 = 0 := rfl
theorem psiKTB3_10 : psiKTB3 1 0 = 0 := rfl
theorem psiKTB3_11 : psiKTB3 1 1 = 0 := rfl
theorem psiKTB3_12 : psiKTB3 1 2 = 1 := rfl
theorem psiKTB3_13 : psiKTB3 1 3 = 0 := rfl
theorem psiKTB3_20 : psiKTB3 2 0 = 0 := rfl
theorem psiKTB3_21 : psiKTB3 2 1 = 0 := rfl
theorem psiKTB3_22 : psiKTB3 2 2 = 0 := rfl
theorem psiKTB3_23 : psiKTB3 2 3 = 0 := rfl
theorem psiKTB3_30 : psiKTB3 3 0 = 0 := rfl
theorem psiKTB3_31 : psiKTB3 3 1 = 0 := rfl
theorem psiKTB3_32 : psiKTB3 3 2 = 0 := rfl
theorem psiKTB3_33 : psiKTB3 3 3 = 0 := rfl

def TrKTB3 : Template KTB3 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 1, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTB3 : 3 ∣ TrKTB3.E.card := by unfold TrKTB3; decide
theorem tr_value_KTB3 : psiNum psiKTB3 TrKTB3.L TrKTB3.E % 2 = 1 := by decide

def canon_KTB3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2) / 2), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTB3 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTB3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (2 : ℤ) ∣ ∑ i, ∑ j, psiKTB3 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTB3 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTB3_00, psiKTB3_01, psiKTB3_02, psiKTB3_03, psiKTB3_10, psiKTB3_11, psiKTB3_12, psiKTB3_13, psiKTB3_20, psiKTB3_21, psiKTB3_22, psiKTB3_23, psiKTB3_30, psiKTB3_31, psiKTB3_32, psiKTB3_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTB3 u, ?_⟩
  intro i j
  rw [KTB3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB3, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem torsionInside_KTB3 : TorsionInsideB KTB3 cM3 (cM3 0) psiKTB3 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTB3 KTB3_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (2 : ℤ) ∣ psiNum psiKTB3 p E := by unfold psiValB at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTB3 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTB3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTB3 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTB3 L) :
    psiValB psiKTB3 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTB3 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (2 : ℤ) ∣ psiNum psiKTB3 p L := by
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
    simp (config := {decide := true}) only [KTB3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTB3_00, psiKTB3_01, psiKTB3_02, psiKTB3_03, psiKTB3_10, psiKTB3_11, psiKTB3_12, psiKTB3_13, psiKTB3_20, psiKTB3_21, psiKTB3_22, psiKTB3_23, psiKTB3_30, psiKTB3_31, psiKTB3_32, psiKTB3_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValB; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTB3 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTB3 u →
    CountsInside cM3 k u → ∃ w, LatEq KTB3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB3; decide)
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
  refine ⟨canon_KTB3 u, ?_⟩
  intro i j
  rw [KTB3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTB3, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 1 2) / 2 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTB3 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTB3 cM3 k :=
  even3Inside_of_scalar_five KTB3 cM3 k fiveStep_KTB3 KTB3_card (scalar_inside_KTB3 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTB3 : ∀ u c0, ScalarHyp KTB3 u → LatEq KTB3 u c0 →
    ∃ c, LatEq KTB3 u c ∧ ∀ τ ∈ KTB3, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTB3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTB3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTB3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTB3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTB3 u, ?_, ?_⟩
  · intro i j
    rw [KTB3]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTB3, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 * 6 = 2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 6 = qv0 at *
    generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv1 at *
    generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv3 at *
    generalize (1 * u 1 2) / 2 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTB3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTB3, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTB3 : UniversalCert KTB3 := by
  have hB : WitnessBoundK KTB3 204 2080 := by
    rw [show (2080 : ℕ) = KTB3.card * (1 * 204 + 4) by rw [KTB3_card_eq]]
    exact witnessBound_of_latEq_lowerK KTB3 KTB3_card 1 scalar_witness_KTB3 204
  exact universalCert_of_torsion_components_T2 KTB3 cM3 compLabel_KTB3 typesInside_KTB3 KTB3_card
    kappaLinks_KTB3 localWalk4_KTB3 even3Inside_KTB3 psiKTB3 torsionInside_KTB3
    (fun p L hin hL => psiVal_of_isIntDiv_KTB3 p L hin hL) TrKTB3 tr3_KTB3 tr_value_KTB3 2080 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 012 022 122 333}`. -/
noncomputable def KTH1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KTH1_card : ∀ τ ∈ KTH1, Multiset.card τ = 3 := by unfold KTH1; decide

theorem KTH1_card_eq : KTH1.card = 6 := by unfold KTH1; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTH1 : FiveStepLinks KTH1 := by
  unfold FiveStepLinks Link KTH1; decide

def kappaKTH1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTH1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTH1 := by
  refine ⟨kappaKTH1, ?_, ?_⟩ <;> unfold Link KTH1 kappaKTH1 <;> decide

theorem familyFacts_KTH1 : FamilyFacts KTH1 :=
  ⟨KTH1_card, by unfold Link KTH1; decide,
    by intro i; fin_cases i <;> (unfold Link KTH1; decide)⟩

theorem compLabel_KTH1 : CompLabel KTH1 cM3 := by
  unfold CompLabel Link KTH1 cM3; decide

theorem typesInside_KTH1 : TypesInside KTH1 cM3 := by
  unfold TypesInside KTH1 cM3; decide

theorem localWalk4_KTH1 (k : Fin 4) : LocalWalk4 KTH1 cM3 k := by
  revert k; unfold LocalWalk4 Link KTH1 cM3; decide

theorem isolatedMono_KTH1 : IsolatedMono KTH1 3 := by unfold IsolatedMono KTH1; decide

theorem KTH1_three : ThreeStepLinks KTH1 := by unfold ThreeStepLinks Link KTH1; decide

def psiKTH1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 3, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]
theorem psiKTH1_00 : psiKTH1 0 0 = 0 := rfl
theorem psiKTH1_01 : psiKTH1 0 1 = 0 := rfl
theorem psiKTH1_02 : psiKTH1 0 2 = 1 := rfl
theorem psiKTH1_03 : psiKTH1 0 3 = 0 := rfl
theorem psiKTH1_10 : psiKTH1 1 0 = 0 := rfl
theorem psiKTH1_11 : psiKTH1 1 1 = 0 := rfl
theorem psiKTH1_12 : psiKTH1 1 2 = 3 := rfl
theorem psiKTH1_13 : psiKTH1 1 3 = 0 := rfl
theorem psiKTH1_20 : psiKTH1 2 0 = 0 := rfl
theorem psiKTH1_21 : psiKTH1 2 1 = 0 := rfl
theorem psiKTH1_22 : psiKTH1 2 2 = 2 := rfl
theorem psiKTH1_23 : psiKTH1 2 3 = 0 := rfl
theorem psiKTH1_30 : psiKTH1 3 0 = 0 := rfl
theorem psiKTH1_31 : psiKTH1 3 1 = 0 := rfl
theorem psiKTH1_32 : psiKTH1 3 2 = 0 := rfl
theorem psiKTH1_33 : psiKTH1 3 3 = 0 := rfl

def TrKTH1 : Template KTH1 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTH1 : 3 ∣ TrKTH1.E.card := by unfold TrKTH1; decide
theorem tr_value_KTH1 : psiNum psiKTH1 TrKTH1.L TrKTH1.E / 2 % 2 = 1 := by decide

def canon_KTH1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12), ({0,0,1}, (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4), ({0,1,2}, (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4), ({1,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTH1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTH1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (4 : ℤ) ∣ ∑ i, ∑ j, psiKTH1 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTH1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KTH1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTH1_00, psiKTH1_01, psiKTH1_02, psiKTH1_03, psiKTH1_10, psiKTH1_11, psiKTH1_12, psiKTH1_13, psiKTH1_20, psiKTH1_21, psiKTH1_22, psiKTH1_23, psiKTH1_30, psiKTH1_31, psiKTH1_32, psiKTH1_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTH1 u, ?_⟩
  intro i j
  rw [KTH1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH1, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem psiEven_KTH1 : PsiEven KTH1 cM3 (cM3 0) psiKTH1 := by
  intro V _ _ p E hg
  unfold psiNum
  have hs := unorderedCount_swap p E
  have hf := counts_forbid (F := KTH1) hg.2.1
  have hp := counts_parity p E hg.1 hg.2.2.1
  have hin := countsInside_of_insideE hg.2.2.2.2
  generalize unorderedCount p E = u at hs hf hp hin ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KTH1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, psiKTH1_00, psiKTH1_01, psiKTH1_02, psiKTH1_03, psiKTH1_10, psiKTH1_11, psiKTH1_12, psiKTH1_13, psiKTH1_20, psiKTH1_21, psiKTH1_22, psiKTH1_23, psiKTH1_30, psiKTH1_31, psiKTH1_32, psiKTH1_33]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem torsionInside_KTH1 : TorsionInsideH KTH1 cM3 (cM3 0) psiKTH1 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTH1 KTH1_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have h2 := psiEven_KTH1 p E hg
  have hψ : (4 : ℤ) ∣ psiNum psiKTH1 p E := by unfold psiValH at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTH1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTH1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTH1 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTH1 L) :
    psiValH psiKTH1 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTH1 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (4 : ℤ) ∣ psiNum psiKTH1 p L := by
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
    simp (config := {decide := true}) only [KTH1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTH1_00, psiKTH1_01, psiKTH1_02, psiKTH1_03, psiKTH1_10, psiKTH1_11, psiKTH1_12, psiKTH1_13, psiKTH1_20, psiKTH1_21, psiKTH1_22, psiKTH1_23, psiKTH1_30, psiKTH1_31, psiKTH1_32, psiKTH1_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValH; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTH1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTH1 u →
    CountsInside cM3 k u → ∃ w, LatEq KTH1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KTH1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH1; decide)
  have hz : u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 2 = 0 ∧ u 2 2 = 0 := ⟨hin 0 0 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 2 2 (by left; simpa [cM3] using fun h => hk h.symm)⟩
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTH1 u, ?_⟩
  intro i j
  rw [KTH1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH1, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTH1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTH1 cM3 k :=
  even3Inside_of_scalar_five KTH1 cM3 k fiveStep_KTH1 KTH1_card (scalar_inside_KTH1 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTH1 : ∀ u c0, ScalarHyp KTH1 u → LatEq KTH1 u c0 →
    ∃ c, LatEq KTH1 u c ∧ ∀ τ ∈ KTH1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KTH1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTH1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTH1 u, ?_, ?_⟩
  · intro i j
    rw [KTH1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTH1, coeffList, ite_true, ite_false]
    have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
    generalize (2 * u 0 1 - 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
    generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
    generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTH1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTH1, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTH1 : UniversalCert KTH1 := by
  have hB : WitnessBoundK KTH1 204 1248 := by
    rw [show (1248 : ℕ) = KTH1.card * (1 * 204 + 4) by rw [KTH1_card_eq]]
    exact witnessBound_of_latEq_lowerK KTH1 KTH1_card 1 scalar_witness_KTH1 204
  exact universalCert_of_torsion_components_T2H KTH1 cM3 compLabel_KTH1 typesInside_KTH1 KTH1_card
    kappaLinks_KTH1 localWalk4_KTH1 even3Inside_KTH1 psiKTH1 torsionInside_KTH1
    (fun p L hin hL => psiVal_of_isIntDiv_KTH1 p L hin hL) psiEven_KTH1 TrKTH1 tr3_KTH1 tr_value_KTH1 1248 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 022 122 333}`. -/
noncomputable def KTH2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KTH2_card : ∀ τ ∈ KTH2, Multiset.card τ = 3 := by unfold KTH2; decide

theorem KTH2_card_eq : KTH2.card = 7 := by unfold KTH2; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTH2 : FiveStepLinks KTH2 := by
  unfold FiveStepLinks Link KTH2; decide

def kappaKTH2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTH2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTH2 := by
  refine ⟨kappaKTH2, ?_, ?_⟩ <;> unfold Link KTH2 kappaKTH2 <;> decide

theorem familyFacts_KTH2 : FamilyFacts KTH2 :=
  ⟨KTH2_card, by unfold Link KTH2; decide,
    by intro i; fin_cases i <;> (unfold Link KTH2; decide)⟩

theorem compLabel_KTH2 : CompLabel KTH2 cM3 := by
  unfold CompLabel Link KTH2 cM3; decide

theorem typesInside_KTH2 : TypesInside KTH2 cM3 := by
  unfold TypesInside KTH2 cM3; decide

theorem localWalk4_KTH2 (k : Fin 4) : LocalWalk4 KTH2 cM3 k := by
  revert k; unfold LocalWalk4 Link KTH2 cM3; decide

theorem isolatedMono_KTH2 : IsolatedMono KTH2 3 := by unfold IsolatedMono KTH2; decide

theorem KTH2_three : ThreeStepLinks KTH2 := by unfold ThreeStepLinks Link KTH2; decide

def psiKTH2 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 3, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]
theorem psiKTH2_00 : psiKTH2 0 0 = 0 := rfl
theorem psiKTH2_01 : psiKTH2 0 1 = 0 := rfl
theorem psiKTH2_02 : psiKTH2 0 2 = 1 := rfl
theorem psiKTH2_03 : psiKTH2 0 3 = 0 := rfl
theorem psiKTH2_10 : psiKTH2 1 0 = 0 := rfl
theorem psiKTH2_11 : psiKTH2 1 1 = 0 := rfl
theorem psiKTH2_12 : psiKTH2 1 2 = 3 := rfl
theorem psiKTH2_13 : psiKTH2 1 3 = 0 := rfl
theorem psiKTH2_20 : psiKTH2 2 0 = 0 := rfl
theorem psiKTH2_21 : psiKTH2 2 1 = 0 := rfl
theorem psiKTH2_22 : psiKTH2 2 2 = 2 := rfl
theorem psiKTH2_23 : psiKTH2 2 3 = 0 := rfl
theorem psiKTH2_30 : psiKTH2 3 0 = 0 := rfl
theorem psiKTH2_31 : psiKTH2 3 1 = 0 := rfl
theorem psiKTH2_32 : psiKTH2 3 2 = 0 := rfl
theorem psiKTH2_33 : psiKTH2 3 3 = 0 := rfl

def TrKTH2 : Template KTH2 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTH2 : 3 ∣ TrKTH2.E.card := by unfold TrKTH2; decide
theorem tr_value_KTH2 : psiNum psiKTH2 TrKTH2.L TrKTH2.E / 2 % 2 = 1 := by decide

def canon_KTH2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12), ({0,0,1}, (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4), ({1,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTH2 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTH2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (4 : ℤ) ∣ ∑ i, ∑ j, psiKTH2 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTH2 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTH2_00, psiKTH2_01, psiKTH2_02, psiKTH2_03, psiKTH2_10, psiKTH2_11, psiKTH2_12, psiKTH2_13, psiKTH2_20, psiKTH2_21, psiKTH2_22, psiKTH2_23, psiKTH2_30, psiKTH2_31, psiKTH2_32, psiKTH2_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTH2 u, ?_⟩
  intro i j
  rw [KTH2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH2, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem psiEven_KTH2 : PsiEven KTH2 cM3 (cM3 0) psiKTH2 := by
  intro V _ _ p E hg
  unfold psiNum
  have hs := unorderedCount_swap p E
  have hf := counts_forbid (F := KTH2) hg.2.1
  have hp := counts_parity p E hg.1 hg.2.2.1
  have hin := countsInside_of_insideE hg.2.2.2.2
  generalize unorderedCount p E = u at hs hf hp hin ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, psiKTH2_00, psiKTH2_01, psiKTH2_02, psiKTH2_03, psiKTH2_10, psiKTH2_11, psiKTH2_12, psiKTH2_13, psiKTH2_20, psiKTH2_21, psiKTH2_22, psiKTH2_23, psiKTH2_30, psiKTH2_31, psiKTH2_32, psiKTH2_33]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem torsionInside_KTH2 : TorsionInsideH KTH2 cM3 (cM3 0) psiKTH2 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTH2 KTH2_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have h2 := psiEven_KTH2 p E hg
  have hψ : (4 : ℤ) ∣ psiNum psiKTH2 p E := by unfold psiValH at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTH2 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTH2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTH2 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTH2 L) :
    psiValH psiKTH2 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTH2 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (4 : ℤ) ∣ psiNum psiKTH2 p L := by
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
    simp (config := {decide := true}) only [KTH2, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTH2_00, psiKTH2_01, psiKTH2_02, psiKTH2_03, psiKTH2_10, psiKTH2_11, psiKTH2_12, psiKTH2_13, psiKTH2_20, psiKTH2_21, psiKTH2_22, psiKTH2_23, psiKTH2_30, psiKTH2_31, psiKTH2_32, psiKTH2_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValH; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTH2 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTH2 u →
    CountsInside cM3 k u → ∃ w, LatEq KTH2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH2; decide)
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
  refine ⟨canon_KTH2 u, ?_⟩
  intro i j
  rw [KTH2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH2, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTH2 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTH2 cM3 k :=
  even3Inside_of_scalar_five KTH2 cM3 k fiveStep_KTH2 KTH2_card (scalar_inside_KTH2 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTH2 : ∀ u c0, ScalarHyp KTH2 u → LatEq KTH2 u c0 →
    ∃ c, LatEq KTH2 u c ∧ ∀ τ ∈ KTH2, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTH2, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTH2 u, ?_, ?_⟩
  · intro i j
    rw [KTH2]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTH2, coeffList, ite_true, ite_false]
    have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
    generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
    generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
    generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTH2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTH2, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTH2 : UniversalCert KTH2 := by
  have hB : WitnessBoundK KTH2 204 1456 := by
    rw [show (1456 : ℕ) = KTH2.card * (1 * 204 + 4) by rw [KTH2_card_eq]]
    exact witnessBound_of_latEq_lowerK KTH2 KTH2_card 1 scalar_witness_KTH2 204
  exact universalCert_of_torsion_components_T2H KTH2 cM3 compLabel_KTH2 typesInside_KTH2 KTH2_card
    kappaLinks_KTH2 localWalk4_KTH2 even3Inside_KTH2 psiKTH2 torsionInside_KTH2
    (fun p L hin hL => psiVal_of_isIntDiv_KTH2 p L hin hL) psiEven_KTH2 TrKTH2 tr3_KTH2 tr_value_KTH2 1456 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 012 022 112 122 333}`. -/
noncomputable def KTH3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KTH3_card : ∀ τ ∈ KTH3, Multiset.card τ = 3 := by unfold KTH3; decide

theorem KTH3_card_eq : KTH3.card = 7 := by unfold KTH3; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTH3 : FiveStepLinks KTH3 := by
  unfold FiveStepLinks Link KTH3; decide

def kappaKTH3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTH3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTH3 := by
  refine ⟨kappaKTH3, ?_, ?_⟩ <;> unfold Link KTH3 kappaKTH3 <;> decide

theorem familyFacts_KTH3 : FamilyFacts KTH3 :=
  ⟨KTH3_card, by unfold Link KTH3; decide,
    by intro i; fin_cases i <;> (unfold Link KTH3; decide)⟩

theorem compLabel_KTH3 : CompLabel KTH3 cM3 := by
  unfold CompLabel Link KTH3 cM3; decide

theorem typesInside_KTH3 : TypesInside KTH3 cM3 := by
  unfold TypesInside KTH3 cM3; decide

theorem localWalk4_KTH3 (k : Fin 4) : LocalWalk4 KTH3 cM3 k := by
  revert k; unfold LocalWalk4 Link KTH3 cM3; decide

theorem isolatedMono_KTH3 : IsolatedMono KTH3 3 := by unfold IsolatedMono KTH3; decide

theorem KTH3_three : ThreeStepLinks KTH3 := by unfold ThreeStepLinks Link KTH3; decide

def psiKTH3 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 2, 3, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]
theorem psiKTH3_00 : psiKTH3 0 0 = 0 := rfl
theorem psiKTH3_01 : psiKTH3 0 1 = 0 := rfl
theorem psiKTH3_02 : psiKTH3 0 2 = 1 := rfl
theorem psiKTH3_03 : psiKTH3 0 3 = 0 := rfl
theorem psiKTH3_10 : psiKTH3 1 0 = 0 := rfl
theorem psiKTH3_11 : psiKTH3 1 1 = 2 := rfl
theorem psiKTH3_12 : psiKTH3 1 2 = 3 := rfl
theorem psiKTH3_13 : psiKTH3 1 3 = 0 := rfl
theorem psiKTH3_20 : psiKTH3 2 0 = 0 := rfl
theorem psiKTH3_21 : psiKTH3 2 1 = 0 := rfl
theorem psiKTH3_22 : psiKTH3 2 2 = 2 := rfl
theorem psiKTH3_23 : psiKTH3 2 3 = 0 := rfl
theorem psiKTH3_30 : psiKTH3 3 0 = 0 := rfl
theorem psiKTH3_31 : psiKTH3 3 1 = 0 := rfl
theorem psiKTH3_32 : psiKTH3 3 2 = 0 := rfl
theorem psiKTH3_33 : psiKTH3 3 3 = 0 := rfl

def TrKTH3 : Template KTH3 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTH3 : 3 ∣ TrKTH3.E.card := by unfold TrKTH3; decide
theorem tr_value_KTH3 : psiNum psiKTH3 TrKTH3.L TrKTH3.E / 2 % 2 = 1 := by decide

def canon_KTH3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12), ({0,0,1}, (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4), ({0,1,2}, (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2), ({0,2,2}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4), ({1,1,2}, (1 * u 1 1) / 1), ({1,2,2}, (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTH3 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTH3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (4 : ℤ) ∣ ∑ i, ∑ j, psiKTH3 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTH3 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTH3_00, psiKTH3_01, psiKTH3_02, psiKTH3_03, psiKTH3_10, psiKTH3_11, psiKTH3_12, psiKTH3_13, psiKTH3_20, psiKTH3_21, psiKTH3_22, psiKTH3_23, psiKTH3_30, psiKTH3_31, psiKTH3_32, psiKTH3_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTH3 u, ?_⟩
  intro i j
  rw [KTH3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH3, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem psiEven_KTH3 : PsiEven KTH3 cM3 (cM3 0) psiKTH3 := by
  intro V _ _ p E hg
  unfold psiNum
  have hs := unorderedCount_swap p E
  have hf := counts_forbid (F := KTH3) hg.2.1
  have hp := counts_parity p E hg.1 hg.2.2.1
  have hin := countsInside_of_insideE hg.2.2.2.2
  generalize unorderedCount p E = u at hs hf hp hin ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, psiKTH3_00, psiKTH3_01, psiKTH3_02, psiKTH3_03, psiKTH3_10, psiKTH3_11, psiKTH3_12, psiKTH3_13, psiKTH3_20, psiKTH3_21, psiKTH3_22, psiKTH3_23, psiKTH3_30, psiKTH3_31, psiKTH3_32, psiKTH3_33]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem torsionInside_KTH3 : TorsionInsideH KTH3 cM3 (cM3 0) psiKTH3 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTH3 KTH3_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have h2 := psiEven_KTH3 p E hg
  have hψ : (4 : ℤ) ∣ psiNum psiKTH3 p E := by unfold psiValH at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTH3 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTH3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTH3 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTH3 L) :
    psiValH psiKTH3 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTH3 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (4 : ℤ) ∣ psiNum psiKTH3 p L := by
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
    simp (config := {decide := true}) only [KTH3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTH3_00, psiKTH3_01, psiKTH3_02, psiKTH3_03, psiKTH3_10, psiKTH3_11, psiKTH3_12, psiKTH3_13, psiKTH3_20, psiKTH3_21, psiKTH3_22, psiKTH3_23, psiKTH3_30, psiKTH3_31, psiKTH3_32, psiKTH3_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValH; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTH3 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTH3 u →
    CountsInside cM3 k u → ∃ w, LatEq KTH3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH3; decide)
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
  refine ⟨canon_KTH3 u, ?_⟩
  intro i j
  rw [KTH3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH3, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTH3 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTH3 cM3 k :=
  even3Inside_of_scalar_five KTH3 cM3 k fiveStep_KTH3 KTH3_card (scalar_inside_KTH3 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTH3 : ∀ u c0, ScalarHyp KTH3 u → LatEq KTH3 u c0 →
    ∃ c, LatEq KTH3 u c ∧ ∀ τ ∈ KTH3, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTH3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTH3 u, ?_, ?_⟩
  · intro i j
    rw [KTH3]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTH3, coeffList, ite_true, ite_false]
    have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
    generalize (2 * u 0 1 - 1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
    generalize (1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
    generalize (-1 * u 0 2 - 2 * u 1 1 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTH3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTH3, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTH3 : UniversalCert KTH3 := by
  have hB : WitnessBoundK KTH3 204 1456 := by
    rw [show (1456 : ℕ) = KTH3.card * (1 * 204 + 4) by rw [KTH3_card_eq]]
    exact witnessBound_of_latEq_lowerK KTH3 KTH3_card 1 scalar_witness_KTH3 204
  exact universalCert_of_torsion_components_T2H KTH3 cM3 compLabel_KTH3 typesInside_KTH3 KTH3_card
    kappaLinks_KTH3 localWalk4_KTH3 even3Inside_KTH3 psiKTH3 torsionInside_KTH3
    (fun p L hin hL => psiVal_of_isIntDiv_KTH3 p L hin hL) psiEven_KTH3 TrKTH3 tr3_KTH3 tr_value_KTH3 1456 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 022 111 122 333}`. -/
noncomputable def KTH4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 2, 2}, {3, 3, 3}}

theorem KTH4_card : ∀ τ ∈ KTH4, Multiset.card τ = 3 := by unfold KTH4; decide

theorem KTH4_card_eq : KTH4.card = 8 := by unfold KTH4; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KTH4 : FiveStepLinks KTH4 := by
  unfold FiveStepLinks Link KTH4; decide

def kappaKTH4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KTH4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KTH4 := by
  refine ⟨kappaKTH4, ?_, ?_⟩ <;> unfold Link KTH4 kappaKTH4 <;> decide

theorem familyFacts_KTH4 : FamilyFacts KTH4 :=
  ⟨KTH4_card, by unfold Link KTH4; decide,
    by intro i; fin_cases i <;> (unfold Link KTH4; decide)⟩

theorem compLabel_KTH4 : CompLabel KTH4 cM3 := by
  unfold CompLabel Link KTH4 cM3; decide

theorem typesInside_KTH4 : TypesInside KTH4 cM3 := by
  unfold TypesInside KTH4 cM3; decide

theorem localWalk4_KTH4 (k : Fin 4) : LocalWalk4 KTH4 cM3 k := by
  revert k; unfold LocalWalk4 Link KTH4 cM3; decide

theorem isolatedMono_KTH4 : IsolatedMono KTH4 3 := by unfold IsolatedMono KTH4; decide

theorem KTH4_three : ThreeStepLinks KTH4 := by unfold ThreeStepLinks Link KTH4; decide

def psiKTH4 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 3, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]
theorem psiKTH4_00 : psiKTH4 0 0 = 0 := rfl
theorem psiKTH4_01 : psiKTH4 0 1 = 0 := rfl
theorem psiKTH4_02 : psiKTH4 0 2 = 1 := rfl
theorem psiKTH4_03 : psiKTH4 0 3 = 0 := rfl
theorem psiKTH4_10 : psiKTH4 1 0 = 0 := rfl
theorem psiKTH4_11 : psiKTH4 1 1 = 0 := rfl
theorem psiKTH4_12 : psiKTH4 1 2 = 3 := rfl
theorem psiKTH4_13 : psiKTH4 1 3 = 0 := rfl
theorem psiKTH4_20 : psiKTH4 2 0 = 0 := rfl
theorem psiKTH4_21 : psiKTH4 2 1 = 0 := rfl
theorem psiKTH4_22 : psiKTH4 2 2 = 2 := rfl
theorem psiKTH4_23 : psiKTH4 2 3 = 0 := rfl
theorem psiKTH4_30 : psiKTH4 3 0 = 0 := rfl
theorem psiKTH4_31 : psiKTH4 3 1 = 0 := rfl
theorem psiKTH4_32 : psiKTH4 3 2 = 0 := rfl
theorem psiKTH4_33 : psiKTH4 3 3 = 0 := rfl

def TrKTH4 : Template KTH4 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide
theorem tr3_KTH4 : 3 ∣ TrKTH4.E.card := by unfold TrKTH4; decide
theorem tr_value_KTH4 : psiNum psiKTH4 TrKTH4.L TrKTH4.E / 2 % 2 = 1 := by decide

def canon_KTH4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12), ({0,0,1}, (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4), ({1,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KTH4 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KTH4 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (4 : ℤ) ∣ ∑ i, ∑ j, psiKTH4 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KTH4 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH4; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKTH4_00, psiKTH4_01, psiKTH4_02, psiKTH4_03, psiKTH4_10, psiKTH4_11, psiKTH4_12, psiKTH4_13, psiKTH4_20, psiKTH4_21, psiKTH4_22, psiKTH4_23, psiKTH4_30, psiKTH4_31, psiKTH4_32, psiKTH4_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KTH4 u, ?_⟩
  intro i j
  rw [KTH4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH4, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem psiEven_KTH4 : PsiEven KTH4 cM3 (cM3 0) psiKTH4 := by
  intro V _ _ p E hg
  unfold psiNum
  have hs := unorderedCount_swap p E
  have hf := counts_forbid (F := KTH4) hg.2.1
  have hp := counts_parity p E hg.1 hg.2.2.1
  have hin := countsInside_of_insideE hg.2.2.2.2
  generalize unorderedCount p E = u at hs hf hp hin ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH4; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, psiKTH4_00, psiKTH4_01, psiKTH4_02, psiKTH4_03, psiKTH4_10, psiKTH4_11, psiKTH4_12, psiKTH4_13, psiKTH4_20, psiKTH4_21, psiKTH4_22, psiKTH4_23, psiKTH4_30, psiKTH4_31, psiKTH4_32, psiKTH4_33]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem torsionInside_KTH4 : TorsionInsideH KTH4 cM3 (cM3 0) psiKTH4 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KTH4 KTH4_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have h2 := psiEven_KTH4 p E hg
  have hψ : (4 : ℤ) ∣ psiNum psiKTH4 p E := by unfold psiValH at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KTH4 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KTH4 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KTH4 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KTH4 L) :
    psiValH psiKTH4 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KTH4 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (4 : ℤ) ∣ psiNum psiKTH4 p L := by
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
    simp (config := {decide := true}) only [KTH4, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKTH4_00, psiKTH4_01, psiKTH4_02, psiKTH4_03, psiKTH4_10, psiKTH4_11, psiKTH4_12, psiKTH4_13, psiKTH4_20, psiKTH4_21, psiKTH4_22, psiKTH4_23, psiKTH4_30, psiKTH4_31, psiKTH4_32, psiKTH4_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiValH; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KTH4 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KTH4 u →
    CountsInside cM3 k u → ∃ w, LatEq KTH4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH4; decide)
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
  refine ⟨canon_KTH4 u, ?_⟩
  intro i j
  rw [KTH4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KTH4, coeffList, ite_true, ite_false]
  have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
  generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
  generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
  generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
  generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
  generalize (1 * u 3 3) / 3 = qv5 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KTH4 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KTH4 cM3 k :=
  even3Inside_of_scalar_five KTH4 cM3 k fiveStep_KTH4 KTH4_card (scalar_inside_KTH4 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KTH4 : ∀ u c0, ScalarHyp KTH4 u → LatEq KTH4 u c0 →
    ∃ c, LatEq KTH4 u c ∧ ∀ τ ∈ KTH4, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KTH4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KTH4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KTH4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KTH4, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KTH4 u, ?_, ?_⟩
  · intro i j
    rw [KTH4]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KTH4, coeffList, ite_true, ite_false]
    have hqv0 : (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 * 12 = 4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = 1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 * 4 = -1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv5 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (4 * u 0 0 - 2 * u 0 1 + 1 * u 0 2 + 4 * u 1 1 + 1 * u 1 2 - 2 * u 2 2) / 12 = qv0 at *
    generalize (2 * u 0 1 - 1 * u 0 2 - 4 * u 1 1 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv1 at *
    generalize (1 * u 0 2 + 1 * u 1 2 - 2 * u 2 2) / 2 = qv2 at *
    generalize (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 4 = qv3 at *
    generalize (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 4 = qv4 at *
    generalize (1 * u 3 3) / 3 = qv5 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KTH4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KTH4, coeffList, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem universalCert_KTH4 : UniversalCert KTH4 := by
  have hB : WitnessBoundK KTH4 204 1664 := by
    rw [show (1664 : ℕ) = KTH4.card * (1 * 204 + 4) by rw [KTH4_card_eq]]
    exact witnessBound_of_latEq_lowerK KTH4 KTH4_card 1 scalar_witness_KTH4 204
  exact universalCert_of_torsion_components_T2H KTH4 cM3 compLabel_KTH4 typesInside_KTH4 KTH4_card
    kappaLinks_KTH4 localWalk4_KTH4 even3Inside_KTH4 psiKTH4 torsionInside_KTH4
    (fun p L hin hL => psiVal_of_isIntDiv_KTH4 p L hin hL) psiEven_KTH4 TrKTH4 tr3_KTH4 tr_value_KTH4 1664 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KTA1
#print axioms PaddedComponents.universalCert_KTB1
#print axioms PaddedComponents.universalCert_KTB2
#print axioms PaddedComponents.universalCert_KTB3
#print axioms PaddedComponents.universalCert_KTH1
#print axioms PaddedComponents.universalCert_KTH2
#print axioms PaddedComponents.universalCert_KTH3
#print axioms PaddedComponents.universalCert_KTH4
