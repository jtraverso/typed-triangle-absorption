/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentChargeU12
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentChargeU6
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# The eleven disconnected `ThreeStepLinks` classes with charged components

`KQ1`–`KQ11` (census rows "Y | * | 2,3 | * | charges", relabelled so that a charged component
contains the class `0`). Each charged component: one charge of unit `12` (or `6` for `KQ10`),
`χ ≡ const ≢ 0 mod 3`, generic templates of charge `±U`. `KQ3` has two charged components.
Generator: `gen_g3.py`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon PaddedCharge

-- Census class `000 112 113 123`.
/-- `{001 002 012 333}`. -/
noncomputable def KQ1 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {3, 3, 3}}

theorem KQ1_card : ∀ τ ∈ KQ1, Multiset.card τ = 3 := by unfold KQ1; decide

theorem KQ1_card_eq : KQ1.card = 4 := by unfold KQ1; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ1 : FiveStepLinks KQ1 := by
  unfold FiveStepLinks Link KQ1; decide

def kappaKQ1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ1 := by
  refine ⟨kappaKQ1, ?_, ?_⟩ <;> unfold Link KQ1 kappaKQ1 <;> decide

theorem familyFacts_KQ1 : FamilyFacts KQ1 :=
  ⟨KQ1_card, by unfold Link KQ1; decide,
    by intro i; fin_cases i <;> (unfold Link KQ1; decide)⟩

def cKQ1 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ1 : CompLabel KQ1 cKQ1 := by
  unfold CompLabel Link KQ1 cKQ1; decide

theorem typesInside_KQ1 : TypesInside KQ1 cKQ1 := by
  unfold TypesInside KQ1 cKQ1; decide

theorem localWalk4_KQ1 (k : Fin 4) : LocalWalk4 KQ1 cKQ1 k := by
  revert k; unfold LocalWalk4 Link KQ1 cKQ1; decide


theorem KQ1_three : ThreeStepLinks KQ1 := by unfold ThreeStepLinks Link KQ1; decide

def canon_KQ1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 1 - 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({0,1,2}, (1 * u 1 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ1_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 0, 2, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ1_0_bound : ∀ i j, |chiKQ1_0 i j| ≤ 4 := by decide
theorem chiKQ1_0_00 : chiKQ1_0 0 0 = 2 := rfl
theorem chiKQ1_0_01 : chiKQ1_0 0 1 = -1 := rfl
theorem chiKQ1_0_02 : chiKQ1_0 0 2 = -1 := rfl
theorem chiKQ1_0_03 : chiKQ1_0 0 3 = 0 := rfl
theorem chiKQ1_0_10 : chiKQ1_0 1 0 = -1 := rfl
theorem chiKQ1_0_11 : chiKQ1_0 1 1 = 0 := rfl
theorem chiKQ1_0_12 : chiKQ1_0 1 2 = 2 := rfl
theorem chiKQ1_0_13 : chiKQ1_0 1 3 = 0 := rfl
theorem chiKQ1_0_20 : chiKQ1_0 2 0 = -1 := rfl
theorem chiKQ1_0_21 : chiKQ1_0 2 1 = 2 := rfl
theorem chiKQ1_0_22 : chiKQ1_0 2 2 = 0 := rfl
theorem chiKQ1_0_23 : chiKQ1_0 2 3 = 0 := rfl
theorem chiKQ1_0_30 : chiKQ1_0 3 0 = 0 := rfl
theorem chiKQ1_0_31 : chiKQ1_0 3 1 = 0 := rfl
theorem chiKQ1_0_32 : chiKQ1_0 3 2 = 0 := rfl
theorem chiKQ1_0_33 : chiKQ1_0 3 3 = 0 := rfl
theorem kills_KQ1_0 : Kills chiKQ1_0 KQ1 := by
  unfold Kills pair KQ1 chiKQ1_0; decide
def TpKQ1_0 : Template KQ1 cKQ1 (cKQ1 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ1_0 : charge chiKQ1_0 TpKQ1_0.L TpKQ1_0.E = 12 := by decide
def TmKQ1_0 : Template KQ1 cKQ1 (cKQ1 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ1_0 : charge chiKQ1_0 TmKQ1_0.L TmKQ1_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ1_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ1_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ1 (cKQ1 0) u) : ∃ c, LatEq KQ1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ1_0_00, chiKQ1_0_01, chiKQ1_0_02, chiKQ1_0_03, chiKQ1_0_10, chiKQ1_0_11, chiKQ1_0_12, chiKQ1_0_13, chiKQ1_0_20, chiKQ1_0_21, chiKQ1_0_22, chiKQ1_0_23, chiKQ1_0_30, chiKQ1_0_31, chiKQ1_0_32, chiKQ1_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ1 u, ?_⟩
  intro i j
  rw [KQ1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ1, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ1_0 : ChargeInside KQ1 cKQ1 (cKQ1 0) chiKQ1_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ1_three KQ1_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ1_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ1_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ1 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ1 (cKQ1 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ1_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ1) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ1_0_00, chiKQ1_0_01, chiKQ1_0_02, chiKQ1_0_03, chiKQ1_0_10, chiKQ1_0_11, chiKQ1_0_12, chiKQ1_0_13, chiKQ1_0_20, chiKQ1_0_21, chiKQ1_0_22, chiKQ1_0_23, chiKQ1_0_30, chiKQ1_0_31, chiKQ1_0_32, chiKQ1_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ1_1 : ∀ u, ScalarHyp KQ1 u → CountsInside cKQ1 1 u →
    ∃ w, LatEq KQ1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ1; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ1; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ1; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ1 u, ?_⟩
  intro i j
  rw [KQ1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ1, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ1_2 : ∀ u, ScalarHyp KQ1 u → CountsInside cKQ1 2 u →
    ∃ w, LatEq KQ1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ1; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ1; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ1; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ1; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ1 u, ?_⟩
  intro i j
  rw [KQ1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ1, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ1_3 : ∀ u, ScalarHyp KQ1 u → CountsInside cKQ1 3 u →
    ∃ w, LatEq KQ1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ1; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ1; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ1; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ1 u, ?_⟩
  intro i j
  rw [KQ1]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ1, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ1 (k : Fin 4) (hk0 : k ≠ cKQ1 0) : Even3Inside KQ1 cKQ1 k := by
  fin_cases k
  · exact absurd (by unfold cKQ1; decide) hk0
  · exact even3Inside_of_scalar KQ1 cKQ1 1 KQ1_three KQ1_card (scalar_inside_KQ1_1)
  · exact even3Inside_of_scalar KQ1 cKQ1 2 KQ1_three KQ1_card (scalar_inside_KQ1_2)
  · exact even3Inside_of_scalar KQ1 cKQ1 3 KQ1_three KQ1_card (scalar_inside_KQ1_3)

def aKQ1 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ1 : ∀ u c0, ScalarHyp KQ1 u → LatEq KQ1 u c0 →
    ∃ c, LatEq KQ1 u c ∧ ∀ τ ∈ KQ1, -((aKQ1 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KQ1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ1 u, ?_, ?_⟩
  · intro i j
    rw [KQ1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ1, coeffList, ite_true, ite_false]
    have hqv0 : (1 * u 0 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (1 * u 0 1 - 1 * u 1 2) / 2 = qv0 at *
    generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
    generalize (1 * u 3 3) / 3 = qv2 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ1, coeffList, aKQ1, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ1 : WitnessBoundK KQ1 840 1696 := by
  have h : WitnessBoundK KQ1 840 (∑ τ ∈ KQ1, (aKQ1 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ1 KQ1_card aKQ1 scalar_witness_KQ1 840
  have hv : ∑ τ ∈ KQ1, (aKQ1 τ * 840 + 4) = 1696 := by unfold KQ1 aKQ1; decide
  rwa [hv] at h

theorem kappaLinks3_KQ1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ1 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ1_three

/-- **`UniversalCert KQ1`**. -/
theorem universalCert_KQ1 : UniversalCert KQ1 :=
  universalCert_of_components KQ1 cKQ1 compLabel_KQ1 typesInside_KQ1 fun k => by
    by_cases h0 : k = cKQ1 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ1 cKQ1 (cKQ1 0) compLabel_KQ1 KQ1_card kappaLinks3_KQ1
        (localWalk4_KQ1 _) chiKQ1_0 chiKQ1_0_bound kills_KQ1_0 chargeInside_KQ1_0
        (fun p A hA hact hin h3 => dvd_KQ1_0 p A hA hact hin h3) TpKQ1_0 TmKQ1_0 Tp_charge_KQ1_0 Tm_charge_KQ1_0
        1696 wb_KQ1 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ1 cKQ1 k compLabel_KQ1 KQ1_card kappaLinks3_KQ1
        (localWalk4_KQ1 k) (even3Inside_KQ1 k h0) 1696
        (fun p P hK hdiv => wb_KQ1 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 001 223 233`.
/-- `{001 011 222 223}`. -/
noncomputable def KQ2 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {2, 2, 3}}

theorem KQ2_card : ∀ τ ∈ KQ2, Multiset.card τ = 3 := by unfold KQ2; decide

theorem KQ2_card_eq : KQ2.card = 4 := by unfold KQ2; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ2 : FiveStepLinks KQ2 := by
  unfold FiveStepLinks Link KQ2; decide

def kappaKQ2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 2], ![0, 0, 2, 0]]

theorem kappaLinks_KQ2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ2 := by
  refine ⟨kappaKQ2, ?_, ?_⟩ <;> unfold Link KQ2 kappaKQ2 <;> decide

theorem familyFacts_KQ2 : FamilyFacts KQ2 :=
  ⟨KQ2_card, by unfold Link KQ2; decide,
    by intro i; fin_cases i <;> (unfold Link KQ2; decide)⟩

def cKQ2 : Fin 4 → Fin 4 := ![0, 0, 2, 2]

theorem compLabel_KQ2 : CompLabel KQ2 cKQ2 := by
  unfold CompLabel Link KQ2 cKQ2; decide

theorem typesInside_KQ2 : TypesInside KQ2 cKQ2 := by
  unfold TypesInside KQ2 cKQ2; decide

theorem localWalk4_KQ2 (k : Fin 4) : LocalWalk4 KQ2 cKQ2 k := by
  revert k; unfold LocalWalk4 Link KQ2 cKQ2; decide


theorem KQ2_three : ThreeStepLinks KQ2 := by unfold ThreeStepLinks Link KQ2; decide

def canon_KQ2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (2 * u 2 2 - 1 * u 2 3) / 6), ({2,2,3}, (1 * u 2 3) / 2)]

def chiKQ2_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ2_0_bound : ∀ i j, |chiKQ2_0 i j| ≤ 4 := by decide
theorem chiKQ2_0_00 : chiKQ2_0 0 0 = 2 := rfl
theorem chiKQ2_0_01 : chiKQ2_0 0 1 = -1 := rfl
theorem chiKQ2_0_02 : chiKQ2_0 0 2 = 0 := rfl
theorem chiKQ2_0_03 : chiKQ2_0 0 3 = 0 := rfl
theorem chiKQ2_0_10 : chiKQ2_0 1 0 = -1 := rfl
theorem chiKQ2_0_11 : chiKQ2_0 1 1 = 2 := rfl
theorem chiKQ2_0_12 : chiKQ2_0 1 2 = 0 := rfl
theorem chiKQ2_0_13 : chiKQ2_0 1 3 = 0 := rfl
theorem chiKQ2_0_20 : chiKQ2_0 2 0 = 0 := rfl
theorem chiKQ2_0_21 : chiKQ2_0 2 1 = 0 := rfl
theorem chiKQ2_0_22 : chiKQ2_0 2 2 = 0 := rfl
theorem chiKQ2_0_23 : chiKQ2_0 2 3 = 0 := rfl
theorem chiKQ2_0_30 : chiKQ2_0 3 0 = 0 := rfl
theorem chiKQ2_0_31 : chiKQ2_0 3 1 = 0 := rfl
theorem chiKQ2_0_32 : chiKQ2_0 3 2 = 0 := rfl
theorem chiKQ2_0_33 : chiKQ2_0 3 3 = 0 := rfl
theorem kills_KQ2_0 : Kills chiKQ2_0 KQ2 := by
  unfold Kills pair KQ2 chiKQ2_0; decide
def TpKQ2_0 : Template KQ2 cKQ2 (cKQ2 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ2_0 : charge chiKQ2_0 TpKQ2_0.L TpKQ2_0.E = 12 := by decide
def TmKQ2_0 : Template KQ2 cKQ2 (cKQ2 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ2_0 : charge chiKQ2_0 TmKQ2_0.L TmKQ2_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ2_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ2_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ2 (cKQ2 0) u) : ∃ c, LatEq KQ2 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ2; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ2_0_00, chiKQ2_0_01, chiKQ2_0_02, chiKQ2_0_03, chiKQ2_0_10, chiKQ2_0_11, chiKQ2_0_12, chiKQ2_0_13, chiKQ2_0_20, chiKQ2_0_21, chiKQ2_0_22, chiKQ2_0_23, chiKQ2_0_30, chiKQ2_0_31, chiKQ2_0_32, chiKQ2_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ2 u, ?_⟩
  intro i j
  rw [KQ2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3) / 2 * 2 = 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3) / 6 = qv0 at *
  generalize (1 * u 2 3) / 2 = qv1 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ2_0 : ChargeInside KQ2 cKQ2 (cKQ2 0) chiKQ2_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ2_three KQ2_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ2_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ2_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ2 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ2 (cKQ2 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ2_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ2) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have o22 : u 2 2 = 0 := hin' 2 2 (by unfold cKQ2; decide)
  have o23 : u 2 3 = 0 := hin' 2 3 (by unfold cKQ2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ2_0_00, chiKQ2_0_01, chiKQ2_0_02, chiKQ2_0_03, chiKQ2_0_10, chiKQ2_0_11, chiKQ2_0_12, chiKQ2_0_13, chiKQ2_0_20, chiKQ2_0_21, chiKQ2_0_22, chiKQ2_0_23, chiKQ2_0_30, chiKQ2_0_31, chiKQ2_0_32, chiKQ2_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ2_1 : ∀ u, ScalarHyp KQ2 u → CountsInside cKQ2 1 u →
    ∃ w, LatEq KQ2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ2; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ2; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ2 u, ?_⟩
  intro i j
  rw [KQ2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3) / 2 * 2 = 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3) / 6 = qv0 at *
  generalize (1 * u 2 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ2_2 : ∀ u, ScalarHyp KQ2 u → CountsInside cKQ2 2 u →
    ∃ w, LatEq KQ2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ2; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ2 u, ?_⟩
  intro i j
  rw [KQ2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3) / 2 * 2 = 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3) / 6 = qv0 at *
  generalize (1 * u 2 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ2_3 : ∀ u, ScalarHyp KQ2 u → CountsInside cKQ2 3 u →
    ∃ w, LatEq KQ2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ2; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ2; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ2; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ2; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ2 u, ?_⟩
  intro i j
  rw [KQ2]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ2, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3) / 2 * 2 = 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3) / 6 = qv0 at *
  generalize (1 * u 2 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ2 (k : Fin 4) (hk0 : k ≠ cKQ2 0) : Even3Inside KQ2 cKQ2 k := by
  fin_cases k
  · exact absurd (by unfold cKQ2; decide) hk0
  · exact even3Inside_of_scalar KQ2 cKQ2 1 KQ2_three KQ2_card (scalar_inside_KQ2_1)
  · exact even3Inside_of_scalar KQ2 cKQ2 2 KQ2_three KQ2_card (scalar_inside_KQ2_2)
  · exact even3Inside_of_scalar KQ2 cKQ2 3 KQ2_three KQ2_card (scalar_inside_KQ2_3)

def aKQ2 : Multiset (Fin 4) → ℕ := fun τ => if τ = {2,2,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ2 : ∀ u c0, ScalarHyp KQ2 u → LatEq KQ2 u c0 →
    ∃ c, LatEq KQ2 u c ∧ ∀ τ ∈ KQ2, -((aKQ2 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ2; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ2; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ2; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KQ2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  simp (config := {decide := true}) only [KQ2, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e11 e22 e23
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ2 u, ?_, ?_⟩
  · intro i j
    rw [KQ2]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ2, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 2 2 - 1 * u 2 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 2 3) / 2 * 2 = 1 * u 2 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 2 2 - 1 * u 2 3) / 6 = qv0 at *
    generalize (1 * u 2 3) / 2 = qv1 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ2, coeffList, aKQ2, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ2 : WitnessBoundK KQ2 840 856 := by
  have h : WitnessBoundK KQ2 840 (∑ τ ∈ KQ2, (aKQ2 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ2 KQ2_card aKQ2 scalar_witness_KQ2 840
  have hv : ∑ τ ∈ KQ2, (aKQ2 τ * 840 + 4) = 856 := by unfold KQ2 aKQ2; decide
  rwa [hv] at h

theorem kappaLinks3_KQ2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ2 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ2_three

/-- **`UniversalCert KQ2`**. -/
theorem universalCert_KQ2 : UniversalCert KQ2 :=
  universalCert_of_components KQ2 cKQ2 compLabel_KQ2 typesInside_KQ2 fun k => by
    by_cases h0 : k = cKQ2 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ2 cKQ2 (cKQ2 0) compLabel_KQ2 KQ2_card kappaLinks3_KQ2
        (localWalk4_KQ2 _) chiKQ2_0 chiKQ2_0_bound kills_KQ2_0 chargeInside_KQ2_0
        (fun p A hA hact hin h3 => dvd_KQ2_0 p A hA hact hin h3) TpKQ2_0 TmKQ2_0 Tp_charge_KQ2_0 Tm_charge_KQ2_0
        856 wb_KQ2 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ2 cKQ2 k compLabel_KQ2 KQ2_card kappaLinks3_KQ2
        (localWalk4_KQ2 k) (even3Inside_KQ2 k h0) 856
        (fun p P hK hdiv => wb_KQ2 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `001 011 223 233`.
/-- `{001 011 223 233}`. -/
noncomputable def KQ3 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 1}, {2, 2, 3}, {2, 3, 3}}

theorem KQ3_card : ∀ τ ∈ KQ3, Multiset.card τ = 3 := by unfold KQ3; decide

theorem KQ3_card_eq : KQ3.card = 4 := by unfold KQ3; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ3 : FiveStepLinks KQ3 := by
  unfold FiveStepLinks Link KQ3; decide

def kappaKQ3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 2], ![0, 0, 2, 2]]

theorem kappaLinks_KQ3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ3 := by
  refine ⟨kappaKQ3, ?_, ?_⟩ <;> unfold Link KQ3 kappaKQ3 <;> decide

theorem familyFacts_KQ3 : FamilyFacts KQ3 :=
  ⟨KQ3_card, by unfold Link KQ3; decide,
    by intro i; fin_cases i <;> (unfold Link KQ3; decide)⟩

def cKQ3 : Fin 4 → Fin 4 := ![0, 0, 2, 2]

theorem compLabel_KQ3 : CompLabel KQ3 cKQ3 := by
  unfold CompLabel Link KQ3 cKQ3; decide

theorem typesInside_KQ3 : TypesInside KQ3 cKQ3 := by
  unfold TypesInside KQ3 cKQ3; decide

theorem localWalk4_KQ3 (k : Fin 4) : LocalWalk4 KQ3 cKQ3 k := by
  revert k; unfold LocalWalk4 Link KQ3 cKQ3; decide


theorem KQ3_three : ThreeStepLinks KQ3 := by unfold ThreeStepLinks Link KQ3; decide

def canon_KQ3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,3}, (1 * u 2 2) / 1), ({2,3,3}, (1 * u 3 3) / 1)]

def chiKQ3_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ3_0_bound : ∀ i j, |chiKQ3_0 i j| ≤ 4 := by decide
theorem chiKQ3_0_00 : chiKQ3_0 0 0 = 2 := rfl
theorem chiKQ3_0_01 : chiKQ3_0 0 1 = -1 := rfl
theorem chiKQ3_0_02 : chiKQ3_0 0 2 = 0 := rfl
theorem chiKQ3_0_03 : chiKQ3_0 0 3 = 0 := rfl
theorem chiKQ3_0_10 : chiKQ3_0 1 0 = -1 := rfl
theorem chiKQ3_0_11 : chiKQ3_0 1 1 = 2 := rfl
theorem chiKQ3_0_12 : chiKQ3_0 1 2 = 0 := rfl
theorem chiKQ3_0_13 : chiKQ3_0 1 3 = 0 := rfl
theorem chiKQ3_0_20 : chiKQ3_0 2 0 = 0 := rfl
theorem chiKQ3_0_21 : chiKQ3_0 2 1 = 0 := rfl
theorem chiKQ3_0_22 : chiKQ3_0 2 2 = 0 := rfl
theorem chiKQ3_0_23 : chiKQ3_0 2 3 = 0 := rfl
theorem chiKQ3_0_30 : chiKQ3_0 3 0 = 0 := rfl
theorem chiKQ3_0_31 : chiKQ3_0 3 1 = 0 := rfl
theorem chiKQ3_0_32 : chiKQ3_0 3 2 = 0 := rfl
theorem chiKQ3_0_33 : chiKQ3_0 3 3 = 0 := rfl
theorem kills_KQ3_0 : Kills chiKQ3_0 KQ3 := by
  unfold Kills pair KQ3 chiKQ3_0; decide
def TpKQ3_0 : Template KQ3 cKQ3 (cKQ3 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ3_0 : charge chiKQ3_0 TpKQ3_0.L TpKQ3_0.E = 12 := by decide
def TmKQ3_0 : Template KQ3 cKQ3 (cKQ3 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ3_0 : charge chiKQ3_0 TmKQ3_0.L TmKQ3_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ3_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ3_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ3 (cKQ3 0) u) : ∃ c, LatEq KQ3 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ3; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ3_0_00, chiKQ3_0_01, chiKQ3_0_02, chiKQ3_0_03, chiKQ3_0_10, chiKQ3_0_11, chiKQ3_0_12, chiKQ3_0_13, chiKQ3_0_20, chiKQ3_0_21, chiKQ3_0_22, chiKQ3_0_23, chiKQ3_0_30, chiKQ3_0_31, chiKQ3_0_32, chiKQ3_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ3 u, ?_⟩
  intro i j
  rw [KQ3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ3, coeffList, ite_true, ite_false]
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ3_0 : ChargeInside KQ3 cKQ3 (cKQ3 0) chiKQ3_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ3_three KQ3_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ3_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ3_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ3 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ3 (cKQ3 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ3_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ3) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o22 : u 2 2 = 0 := hin' 2 2 (by unfold cKQ3; decide)
  have o23 : u 2 3 = 0 := hin' 2 3 (by unfold cKQ3; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ3_0_00, chiKQ3_0_01, chiKQ3_0_02, chiKQ3_0_03, chiKQ3_0_10, chiKQ3_0_11, chiKQ3_0_12, chiKQ3_0_13, chiKQ3_0_20, chiKQ3_0_21, chiKQ3_0_22, chiKQ3_0_23, chiKQ3_0_30, chiKQ3_0_31, chiKQ3_0_32, chiKQ3_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

def chiKQ3_1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, -1], ![0, 0, -1, 2]]
theorem chiKQ3_1_bound : ∀ i j, |chiKQ3_1 i j| ≤ 4 := by decide
theorem chiKQ3_1_00 : chiKQ3_1 0 0 = 0 := rfl
theorem chiKQ3_1_01 : chiKQ3_1 0 1 = 0 := rfl
theorem chiKQ3_1_02 : chiKQ3_1 0 2 = 0 := rfl
theorem chiKQ3_1_03 : chiKQ3_1 0 3 = 0 := rfl
theorem chiKQ3_1_10 : chiKQ3_1 1 0 = 0 := rfl
theorem chiKQ3_1_11 : chiKQ3_1 1 1 = 0 := rfl
theorem chiKQ3_1_12 : chiKQ3_1 1 2 = 0 := rfl
theorem chiKQ3_1_13 : chiKQ3_1 1 3 = 0 := rfl
theorem chiKQ3_1_20 : chiKQ3_1 2 0 = 0 := rfl
theorem chiKQ3_1_21 : chiKQ3_1 2 1 = 0 := rfl
theorem chiKQ3_1_22 : chiKQ3_1 2 2 = 2 := rfl
theorem chiKQ3_1_23 : chiKQ3_1 2 3 = -1 := rfl
theorem chiKQ3_1_30 : chiKQ3_1 3 0 = 0 := rfl
theorem chiKQ3_1_31 : chiKQ3_1 3 1 = 0 := rfl
theorem chiKQ3_1_32 : chiKQ3_1 3 2 = -1 := rfl
theorem chiKQ3_1_33 : chiKQ3_1 3 3 = 2 := rfl
theorem kills_KQ3_1 : Kills chiKQ3_1 KQ3 := by
  unfold Kills pair KQ3 chiKQ3_1; decide
def TpKQ3_1 : Template KQ3 cKQ3 (cKQ3 2) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![2, 2, 2, 2, 2, 2]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ3_1 : charge chiKQ3_1 TpKQ3_1.L TpKQ3_1.E = 12 := by decide
def TmKQ3_1 : Template KQ3 cKQ3 (cKQ3 2) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![2, 3, 3, 2, 2, 3]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ3_1 : charge chiKQ3_1 TmKQ3_1.L TmKQ3_1.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ3_1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ3_1 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ3 (cKQ3 2) u) : ∃ c, LatEq KQ3 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ3_1_00, chiKQ3_1_01, chiKQ3_1_02, chiKQ3_1_03, chiKQ3_1_10, chiKQ3_1_11, chiKQ3_1_12, chiKQ3_1_13, chiKQ3_1_20, chiKQ3_1_21, chiKQ3_1_22, chiKQ3_1_23, chiKQ3_1_30, chiKQ3_1_31, chiKQ3_1_32, chiKQ3_1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ3 u, ?_⟩
  intro i j
  rw [KQ3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ3, coeffList, ite_true, ite_false]
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ3_1 : ChargeInside KQ3 cKQ3 (cKQ3 2) chiKQ3_1 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ3_three KQ3_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ3_1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ3_1 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ3 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ3 (cKQ3 2) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ3_1 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ3) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o00 : u 0 0 = 0 := hin' 0 0 (by unfold cKQ3; decide)
  have o01 : u 0 1 = 0 := hin' 0 1 (by unfold cKQ3; decide)
  have o11 : u 1 1 = 0 := hin' 1 1 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ3_1_00, chiKQ3_1_01, chiKQ3_1_02, chiKQ3_1_03, chiKQ3_1_10, chiKQ3_1_11, chiKQ3_1_12, chiKQ3_1_13, chiKQ3_1_20, chiKQ3_1_21, chiKQ3_1_22, chiKQ3_1_23, chiKQ3_1_30, chiKQ3_1_31, chiKQ3_1_32, chiKQ3_1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ3_1 : ∀ u, ScalarHyp KQ3 u → CountsInside cKQ3 1 u →
    ∃ w, LatEq KQ3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ3; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ3 u, ?_⟩
  intro i j
  rw [KQ3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ3, coeffList, ite_true, ite_false]
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ3_3 : ∀ u, ScalarHyp KQ3 u → CountsInside cKQ3 3 u →
    ∃ w, LatEq KQ3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ3; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ3; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ3; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ3; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ3; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ3; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ3 u, ?_⟩
  intro i j
  rw [KQ3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ3, coeffList, ite_true, ite_false]
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ3 (k : Fin 4) (hk0 : k ≠ cKQ3 0) (hk2 : k ≠ cKQ3 2) : Even3Inside KQ3 cKQ3 k := by
  fin_cases k
  · exact absurd (by unfold cKQ3; decide) hk0
  · exact even3Inside_of_scalar KQ3 cKQ3 1 KQ3_three KQ3_card (scalar_inside_KQ3_1)
  · exact absurd (by unfold cKQ3; decide) hk2
  · exact even3Inside_of_scalar KQ3 cKQ3 3 KQ3_three KQ3_card (scalar_inside_KQ3_3)

def aKQ3 : Multiset (Fin 4) → ℕ := fun τ => 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ3 : ∀ u c0, ScalarHyp KQ3 u → LatEq KQ3 u c0 →
    ∃ c, LatEq KQ3 u c ∧ ∀ τ ∈ KQ3, -((aKQ3 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ3; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ3; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ3, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ3 u, ?_, ?_⟩
  · intro i j
    rw [KQ3]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ3, coeffList, ite_true, ite_false]
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ3, coeffList, aKQ3, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ3 : WitnessBoundK KQ3 840 16 := by
  have h : WitnessBoundK KQ3 840 (∑ τ ∈ KQ3, (aKQ3 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ3 KQ3_card aKQ3 scalar_witness_KQ3 840
  have hv : ∑ τ ∈ KQ3, (aKQ3 τ * 840 + 4) = 16 := by unfold KQ3 aKQ3; decide
  rwa [hv] at h

theorem kappaLinks3_KQ3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ3 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ3_three

/-- **`UniversalCert KQ3`**. -/
theorem universalCert_KQ3 : UniversalCert KQ3 :=
  universalCert_of_components KQ3 cKQ3 compLabel_KQ3 typesInside_KQ3 fun k => by
    by_cases h0 : k = cKQ3 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ3 cKQ3 (cKQ3 0) compLabel_KQ3 KQ3_card kappaLinks3_KQ3
        (localWalk4_KQ3 _) chiKQ3_0 chiKQ3_0_bound kills_KQ3_0 chargeInside_KQ3_0
        (fun p A hA hact hin h3 => dvd_KQ3_0 p A hA hact hin h3) TpKQ3_0 TmKQ3_0 Tp_charge_KQ3_0 Tm_charge_KQ3_0
        16 wb_KQ3 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · 
      by_cases h2 : k = cKQ3 2
      · subst h2
        exact componentUniversalCert_of_charge_walk_U12 KQ3 cKQ3 (cKQ3 2) compLabel_KQ3 KQ3_card kappaLinks3_KQ3
          (localWalk4_KQ3 _) chiKQ3_1 chiKQ3_1_bound kills_KQ3_1 chargeInside_KQ3_1
          (fun p A hA hact hin h3 => dvd_KQ3_1 p A hA hact hin h3) TpKQ3_1 TmKQ3_1 Tp_charge_KQ3_1 Tm_charge_KQ3_1
          16 wb_KQ3 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
      · exact componentUniversalCert_of_even3_walk_kappa KQ3 cKQ3 k compLabel_KQ3 KQ3_card kappaLinks3_KQ3
          (localWalk4_KQ3 k) (even3Inside_KQ3 k h0 h2) 16
          (fun p P hK hdiv => wb_KQ3 p P (hK.trans (by norm_num)) hdiv)
          (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 112 113 122 123`.
/-- `{001 002 011 012 333}`. -/
noncomputable def KQ4 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {3, 3, 3}}

theorem KQ4_card : ∀ τ ∈ KQ4, Multiset.card τ = 3 := by unfold KQ4; decide

theorem KQ4_card_eq : KQ4.card = 5 := by unfold KQ4; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ4 : FiveStepLinks KQ4 := by
  unfold FiveStepLinks Link KQ4; decide

def kappaKQ4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ4 := by
  refine ⟨kappaKQ4, ?_, ?_⟩ <;> unfold Link KQ4 kappaKQ4 <;> decide

theorem familyFacts_KQ4 : FamilyFacts KQ4 :=
  ⟨KQ4_card, by unfold Link KQ4; decide,
    by intro i; fin_cases i <;> (unfold Link KQ4; decide)⟩

def cKQ4 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ4 : CompLabel KQ4 cKQ4 := by
  unfold CompLabel Link KQ4 cKQ4; decide

theorem typesInside_KQ4 : TypesInside KQ4 cKQ4 := by
  unfold TypesInside KQ4 cKQ4; decide

theorem localWalk4_KQ4 (k : Fin 4) : LocalWalk4 KQ4 cKQ4 k := by
  revert k; unfold LocalWalk4 Link KQ4 cKQ4; decide


theorem KQ4_three : ThreeStepLinks KQ4 := by unfold ThreeStepLinks Link KQ4; decide

def canon_KQ4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ4_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, 2, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ4_0_bound : ∀ i j, |chiKQ4_0 i j| ≤ 4 := by decide
theorem chiKQ4_0_00 : chiKQ4_0 0 0 = 2 := rfl
theorem chiKQ4_0_01 : chiKQ4_0 0 1 = -1 := rfl
theorem chiKQ4_0_02 : chiKQ4_0 0 2 = -1 := rfl
theorem chiKQ4_0_03 : chiKQ4_0 0 3 = 0 := rfl
theorem chiKQ4_0_10 : chiKQ4_0 1 0 = -1 := rfl
theorem chiKQ4_0_11 : chiKQ4_0 1 1 = 2 := rfl
theorem chiKQ4_0_12 : chiKQ4_0 1 2 = 2 := rfl
theorem chiKQ4_0_13 : chiKQ4_0 1 3 = 0 := rfl
theorem chiKQ4_0_20 : chiKQ4_0 2 0 = -1 := rfl
theorem chiKQ4_0_21 : chiKQ4_0 2 1 = 2 := rfl
theorem chiKQ4_0_22 : chiKQ4_0 2 2 = 0 := rfl
theorem chiKQ4_0_23 : chiKQ4_0 2 3 = 0 := rfl
theorem chiKQ4_0_30 : chiKQ4_0 3 0 = 0 := rfl
theorem chiKQ4_0_31 : chiKQ4_0 3 1 = 0 := rfl
theorem chiKQ4_0_32 : chiKQ4_0 3 2 = 0 := rfl
theorem chiKQ4_0_33 : chiKQ4_0 3 3 = 0 := rfl
theorem kills_KQ4_0 : Kills chiKQ4_0 KQ4 := by
  unfold Kills pair KQ4 chiKQ4_0; decide
def TpKQ4_0 : Template KQ4 cKQ4 (cKQ4 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ4_0 : charge chiKQ4_0 TpKQ4_0.L TpKQ4_0.E = 12 := by decide
def TmKQ4_0 : Template KQ4 cKQ4 (cKQ4 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ4_0 : charge chiKQ4_0 TmKQ4_0.L TmKQ4_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ4_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ4 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ4_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ4 (cKQ4 0) u) : ∃ c, LatEq KQ4 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ4_0_00, chiKQ4_0_01, chiKQ4_0_02, chiKQ4_0_03, chiKQ4_0_10, chiKQ4_0_11, chiKQ4_0_12, chiKQ4_0_13, chiKQ4_0_20, chiKQ4_0_21, chiKQ4_0_22, chiKQ4_0_23, chiKQ4_0_30, chiKQ4_0_31, chiKQ4_0_32, chiKQ4_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ4 u, ?_⟩
  intro i j
  rw [KQ4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ4, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 * 2 = 2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ4_0 : ChargeInside KQ4 cKQ4 (cKQ4 0) chiKQ4_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ4_three KQ4_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ4_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ4 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ4_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ4 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ4 (cKQ4 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ4_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ4) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ4_0_00, chiKQ4_0_01, chiKQ4_0_02, chiKQ4_0_03, chiKQ4_0_10, chiKQ4_0_11, chiKQ4_0_12, chiKQ4_0_13, chiKQ4_0_20, chiKQ4_0_21, chiKQ4_0_22, chiKQ4_0_23, chiKQ4_0_30, chiKQ4_0_31, chiKQ4_0_32, chiKQ4_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ4_1 : ∀ u, ScalarHyp KQ4 u → CountsInside cKQ4 1 u →
    ∃ w, LatEq KQ4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ4; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ4; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ4 u, ?_⟩
  intro i j
  rw [KQ4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ4, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 * 2 = 2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ4_2 : ∀ u, ScalarHyp KQ4 u → CountsInside cKQ4 2 u →
    ∃ w, LatEq KQ4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ4; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ4; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ4; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ4 u, ?_⟩
  intro i j
  rw [KQ4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ4, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 * 2 = 2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ4_3 : ∀ u, ScalarHyp KQ4 u → CountsInside cKQ4 3 u →
    ∃ w, LatEq KQ4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ4; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ4; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ4; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ4; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ4 u, ?_⟩
  intro i j
  rw [KQ4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ4, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 * 2 = 2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ4 (k : Fin 4) (hk0 : k ≠ cKQ4 0) : Even3Inside KQ4 cKQ4 k := by
  fin_cases k
  · exact absurd (by unfold cKQ4; decide) hk0
  · exact even3Inside_of_scalar KQ4 cKQ4 1 KQ4_three KQ4_card (scalar_inside_KQ4_1)
  · exact even3Inside_of_scalar KQ4 cKQ4 2 KQ4_three KQ4_card (scalar_inside_KQ4_2)
  · exact even3Inside_of_scalar KQ4 cKQ4 3 KQ4_three KQ4_card (scalar_inside_KQ4_3)

def aKQ4 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ4 : ∀ u c0, ScalarHyp KQ4 u → LatEq KQ4 u c0 →
    ∃ c, LatEq KQ4 u c ∧ ∀ τ ∈ KQ4, -((aKQ4 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KQ4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ4, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ4 u, ?_, ?_⟩
  · intro i j
    rw [KQ4]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ4, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 * 2 = 2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 2 - 1 * u 1 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 - 1 * u 0 2 + 1 * u 1 2) / 2 = qv0 at *
    generalize (1 * u 0 2 - 1 * u 1 2) / 2 = qv1 at *
    generalize (1 * u 3 3) / 3 = qv2 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ4, coeffList, aKQ4, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ4 : WitnessBoundK KQ4 840 1700 := by
  have h : WitnessBoundK KQ4 840 (∑ τ ∈ KQ4, (aKQ4 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ4 KQ4_card aKQ4 scalar_witness_KQ4 840
  have hv : ∑ τ ∈ KQ4, (aKQ4 τ * 840 + 4) = 1700 := by unfold KQ4 aKQ4; decide
  rwa [hv] at h

theorem kappaLinks3_KQ4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ4 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ4_three

/-- **`UniversalCert KQ4`**. -/
theorem universalCert_KQ4 : UniversalCert KQ4 :=
  universalCert_of_components KQ4 cKQ4 compLabel_KQ4 typesInside_KQ4 fun k => by
    by_cases h0 : k = cKQ4 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ4 cKQ4 (cKQ4 0) compLabel_KQ4 KQ4_card kappaLinks3_KQ4
        (localWalk4_KQ4 _) chiKQ4_0 chiKQ4_0_bound kills_KQ4_0 chargeInside_KQ4_0
        (fun p A hA hact hin h3 => dvd_KQ4_0 p A hA hact hin h3) TpKQ4_0 TmKQ4_0 Tp_charge_KQ4_0 Tm_charge_KQ4_0
        1700 wb_KQ4 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ4 cKQ4 k compLabel_KQ4 KQ4_card kappaLinks3_KQ4
        (localWalk4_KQ4 k) (even3Inside_KQ4 k h0) 1700
        (fun p P hK hdiv => wb_KQ4 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 112 113 122 133`.
/-- `{001 002 011 022 333}`. -/
noncomputable def KQ5 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {3, 3, 3}}

theorem KQ5_card : ∀ τ ∈ KQ5, Multiset.card τ = 3 := by unfold KQ5; decide

theorem KQ5_card_eq : KQ5.card = 5 := by unfold KQ5; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ5 : FiveStepLinks KQ5 := by
  unfold FiveStepLinks Link KQ5; decide

def kappaKQ5 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ5 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ5 := by
  refine ⟨kappaKQ5, ?_, ?_⟩ <;> unfold Link KQ5 kappaKQ5 <;> decide

theorem familyFacts_KQ5 : FamilyFacts KQ5 :=
  ⟨KQ5_card, by unfold Link KQ5; decide,
    by intro i; fin_cases i <;> (unfold Link KQ5; decide)⟩

def cKQ5 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ5 : CompLabel KQ5 cKQ5 := by
  unfold CompLabel Link KQ5 cKQ5; decide

theorem typesInside_KQ5 : TypesInside KQ5 cKQ5 := by
  unfold TypesInside KQ5 cKQ5; decide

theorem localWalk4_KQ5 (k : Fin 4) : LocalWalk4 KQ5 cKQ5 k := by
  revert k; unfold LocalWalk4 Link KQ5 cKQ5; decide


theorem KQ5_three : ThreeStepLinks KQ5 := by unfold ThreeStepLinks Link KQ5; decide

def canon_KQ5 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 1 - 2 * u 1 1) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ5_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, 0, 0], ![-1, 0, 2, 0], ![0, 0, 0, 0]]
theorem chiKQ5_0_bound : ∀ i j, |chiKQ5_0 i j| ≤ 4 := by decide
theorem chiKQ5_0_00 : chiKQ5_0 0 0 = 2 := rfl
theorem chiKQ5_0_01 : chiKQ5_0 0 1 = -1 := rfl
theorem chiKQ5_0_02 : chiKQ5_0 0 2 = -1 := rfl
theorem chiKQ5_0_03 : chiKQ5_0 0 3 = 0 := rfl
theorem chiKQ5_0_10 : chiKQ5_0 1 0 = -1 := rfl
theorem chiKQ5_0_11 : chiKQ5_0 1 1 = 2 := rfl
theorem chiKQ5_0_12 : chiKQ5_0 1 2 = 0 := rfl
theorem chiKQ5_0_13 : chiKQ5_0 1 3 = 0 := rfl
theorem chiKQ5_0_20 : chiKQ5_0 2 0 = -1 := rfl
theorem chiKQ5_0_21 : chiKQ5_0 2 1 = 0 := rfl
theorem chiKQ5_0_22 : chiKQ5_0 2 2 = 2 := rfl
theorem chiKQ5_0_23 : chiKQ5_0 2 3 = 0 := rfl
theorem chiKQ5_0_30 : chiKQ5_0 3 0 = 0 := rfl
theorem chiKQ5_0_31 : chiKQ5_0 3 1 = 0 := rfl
theorem chiKQ5_0_32 : chiKQ5_0 3 2 = 0 := rfl
theorem chiKQ5_0_33 : chiKQ5_0 3 3 = 0 := rfl
theorem kills_KQ5_0 : Kills chiKQ5_0 KQ5 := by
  unfold Kills pair KQ5 chiKQ5_0; decide
def TpKQ5_0 : Template KQ5 cKQ5 (cKQ5 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ5_0 : charge chiKQ5_0 TpKQ5_0.L TpKQ5_0.E = 12 := by decide
def TmKQ5_0 : Template KQ5 cKQ5 (cKQ5 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ5_0 : charge chiKQ5_0 TmKQ5_0.L TmKQ5_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ5_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ5 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ5_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ5 (cKQ5 0) u) : ∃ c, LatEq KQ5 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ5; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ5_0_00, chiKQ5_0_01, chiKQ5_0_02, chiKQ5_0_03, chiKQ5_0_10, chiKQ5_0_11, chiKQ5_0_12, chiKQ5_0_13, chiKQ5_0_20, chiKQ5_0_21, chiKQ5_0_22, chiKQ5_0_23, chiKQ5_0_30, chiKQ5_0_31, chiKQ5_0_32, chiKQ5_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ5 u, ?_⟩
  intro i j
  rw [KQ5]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ5, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ5_0 : ChargeInside KQ5 cKQ5 (cKQ5 0) chiKQ5_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ5_three KQ5_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ5_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ5 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ5_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ5 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ5 (cKQ5 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ5_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ5) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ5; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ5_0_00, chiKQ5_0_01, chiKQ5_0_02, chiKQ5_0_03, chiKQ5_0_10, chiKQ5_0_11, chiKQ5_0_12, chiKQ5_0_13, chiKQ5_0_20, chiKQ5_0_21, chiKQ5_0_22, chiKQ5_0_23, chiKQ5_0_30, chiKQ5_0_31, chiKQ5_0_32, chiKQ5_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ5_1 : ∀ u, ScalarHyp KQ5 u → CountsInside cKQ5 1 u →
    ∃ w, LatEq KQ5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ5; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ5; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ5; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ5; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ5; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ5; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ5 u, ?_⟩
  intro i j
  rw [KQ5]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ5, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ5_2 : ∀ u, ScalarHyp KQ5 u → CountsInside cKQ5 2 u →
    ∃ w, LatEq KQ5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ5; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ5; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ5; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ5; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ5; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ5; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ5 u, ?_⟩
  intro i j
  rw [KQ5]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ5, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ5_3 : ∀ u, ScalarHyp KQ5 u → CountsInside cKQ5 3 u →
    ∃ w, LatEq KQ5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ5; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ5; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ5; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ5; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ5; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ5 u, ?_⟩
  intro i j
  rw [KQ5]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ5, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ5 (k : Fin 4) (hk0 : k ≠ cKQ5 0) : Even3Inside KQ5 cKQ5 k := by
  fin_cases k
  · exact absurd (by unfold cKQ5; decide) hk0
  · exact even3Inside_of_scalar KQ5 cKQ5 1 KQ5_three KQ5_card (scalar_inside_KQ5_1)
  · exact even3Inside_of_scalar KQ5 cKQ5 2 KQ5_three KQ5_card (scalar_inside_KQ5_2)
  · exact even3Inside_of_scalar KQ5 cKQ5 3 KQ5_three KQ5_card (scalar_inside_KQ5_3)

def aKQ5 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ5 : ∀ u c0, ScalarHyp KQ5 u → LatEq KQ5 u c0 →
    ∃ c, LatEq KQ5 u c ∧ ∀ τ ∈ KQ5, -((aKQ5 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ5; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ5; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ5, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ5 u, ?_, ?_⟩
  · intro i j
    rw [KQ5]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ5, coeffList, ite_true, ite_false]
    have hqv0 : (1 * u 0 1 - 2 * u 1 1) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (1 * u 0 1 - 2 * u 1 1) / 2 = qv0 at *
    generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
    generalize (1 * u 3 3) / 3 = qv2 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ5, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ5, coeffList, aKQ5, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ5 : WitnessBoundK KQ5 840 1700 := by
  have h : WitnessBoundK KQ5 840 (∑ τ ∈ KQ5, (aKQ5 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ5 KQ5_card aKQ5 scalar_witness_KQ5 840
  have hv : ∑ τ ∈ KQ5, (aKQ5 τ * 840 + 4) = 1700 := by unfold KQ5 aKQ5; decide
  rwa [hv] at h

theorem kappaLinks3_KQ5 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ5 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ5_three

/-- **`UniversalCert KQ5`**. -/
theorem universalCert_KQ5 : UniversalCert KQ5 :=
  universalCert_of_components KQ5 cKQ5 compLabel_KQ5 typesInside_KQ5 fun k => by
    by_cases h0 : k = cKQ5 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ5 cKQ5 (cKQ5 0) compLabel_KQ5 KQ5_card kappaLinks3_KQ5
        (localWalk4_KQ5 _) chiKQ5_0 chiKQ5_0_bound kills_KQ5_0 chargeInside_KQ5_0
        (fun p A hA hact hin h3 => dvd_KQ5_0 p A hA hact hin h3) TpKQ5_0 TmKQ5_0 Tp_charge_KQ5_0 Tm_charge_KQ5_0
        1700 wb_KQ5 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ5 cKQ5 k compLabel_KQ5 KQ5_card kappaLinks3_KQ5
        (localWalk4_KQ5 k) (even3Inside_KQ5 k h0) 1700
        (fun p P hK hdiv => wb_KQ5 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 001 011 223 233`.
/-- `{001 011 222 223 233}`. -/
noncomputable def KQ6 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {2, 2, 3}, {2, 3, 3}}

theorem KQ6_card : ∀ τ ∈ KQ6, Multiset.card τ = 3 := by unfold KQ6; decide

theorem KQ6_card_eq : KQ6.card = 5 := by unfold KQ6; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ6 : FiveStepLinks KQ6 := by
  unfold FiveStepLinks Link KQ6; decide

def kappaKQ6 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 2], ![0, 0, 2, 2]]

theorem kappaLinks_KQ6 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ6 := by
  refine ⟨kappaKQ6, ?_, ?_⟩ <;> unfold Link KQ6 kappaKQ6 <;> decide

theorem familyFacts_KQ6 : FamilyFacts KQ6 :=
  ⟨KQ6_card, by unfold Link KQ6; decide,
    by intro i; fin_cases i <;> (unfold Link KQ6; decide)⟩

def cKQ6 : Fin 4 → Fin 4 := ![0, 0, 2, 2]

theorem compLabel_KQ6 : CompLabel KQ6 cKQ6 := by
  unfold CompLabel Link KQ6 cKQ6; decide

theorem typesInside_KQ6 : TypesInside KQ6 cKQ6 := by
  unfold TypesInside KQ6 cKQ6; decide

theorem localWalk4_KQ6 (k : Fin 4) : LocalWalk4 KQ6 cKQ6 k := by
  revert k; unfold LocalWalk4 Link KQ6 cKQ6; decide


theorem KQ6_three : ThreeStepLinks KQ6 := by unfold ThreeStepLinks Link KQ6; decide

def canon_KQ6 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6), ({2,2,3}, (1 * u 2 3 - 2 * u 3 3) / 2), ({2,3,3}, (1 * u 3 3) / 1)]

def chiKQ6_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ6_0_bound : ∀ i j, |chiKQ6_0 i j| ≤ 4 := by decide
theorem chiKQ6_0_00 : chiKQ6_0 0 0 = 2 := rfl
theorem chiKQ6_0_01 : chiKQ6_0 0 1 = -1 := rfl
theorem chiKQ6_0_02 : chiKQ6_0 0 2 = 0 := rfl
theorem chiKQ6_0_03 : chiKQ6_0 0 3 = 0 := rfl
theorem chiKQ6_0_10 : chiKQ6_0 1 0 = -1 := rfl
theorem chiKQ6_0_11 : chiKQ6_0 1 1 = 2 := rfl
theorem chiKQ6_0_12 : chiKQ6_0 1 2 = 0 := rfl
theorem chiKQ6_0_13 : chiKQ6_0 1 3 = 0 := rfl
theorem chiKQ6_0_20 : chiKQ6_0 2 0 = 0 := rfl
theorem chiKQ6_0_21 : chiKQ6_0 2 1 = 0 := rfl
theorem chiKQ6_0_22 : chiKQ6_0 2 2 = 0 := rfl
theorem chiKQ6_0_23 : chiKQ6_0 2 3 = 0 := rfl
theorem chiKQ6_0_30 : chiKQ6_0 3 0 = 0 := rfl
theorem chiKQ6_0_31 : chiKQ6_0 3 1 = 0 := rfl
theorem chiKQ6_0_32 : chiKQ6_0 3 2 = 0 := rfl
theorem chiKQ6_0_33 : chiKQ6_0 3 3 = 0 := rfl
theorem kills_KQ6_0 : Kills chiKQ6_0 KQ6 := by
  unfold Kills pair KQ6 chiKQ6_0; decide
def TpKQ6_0 : Template KQ6 cKQ6 (cKQ6 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ6_0 : charge chiKQ6_0 TpKQ6_0.L TpKQ6_0.E = 12 := by decide
def TmKQ6_0 : Template KQ6 cKQ6 (cKQ6 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ6_0 : charge chiKQ6_0 TmKQ6_0.L TmKQ6_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ6_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ6 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ6_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ6 (cKQ6 0) u) : ∃ c, LatEq KQ6 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ6; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ6; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ6; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ6_0_00, chiKQ6_0_01, chiKQ6_0_02, chiKQ6_0_03, chiKQ6_0_10, chiKQ6_0_11, chiKQ6_0_12, chiKQ6_0_13, chiKQ6_0_20, chiKQ6_0_21, chiKQ6_0_22, chiKQ6_0_23, chiKQ6_0_30, chiKQ6_0_31, chiKQ6_0_32, chiKQ6_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ6 u, ?_⟩
  intro i j
  rw [KQ6]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ6, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ6_0 : ChargeInside KQ6 cKQ6 (cKQ6 0) chiKQ6_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ6_three KQ6_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ6_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ6 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ6_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ6 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ6 (cKQ6 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ6_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ6) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have o22 : u 2 2 = 0 := hin' 2 2 (by unfold cKQ6; decide)
  have o23 : u 2 3 = 0 := hin' 2 3 (by unfold cKQ6; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ6; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ6_0_00, chiKQ6_0_01, chiKQ6_0_02, chiKQ6_0_03, chiKQ6_0_10, chiKQ6_0_11, chiKQ6_0_12, chiKQ6_0_13, chiKQ6_0_20, chiKQ6_0_21, chiKQ6_0_22, chiKQ6_0_23, chiKQ6_0_30, chiKQ6_0_31, chiKQ6_0_32, chiKQ6_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ6_1 : ∀ u, ScalarHyp KQ6 u → CountsInside cKQ6 1 u →
    ∃ w, LatEq KQ6 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ6; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ6; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ6; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ6; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ6; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ6; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ6 u, ?_⟩
  intro i j
  rw [KQ6]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ6, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ6_2 : ∀ u, ScalarHyp KQ6 u → CountsInside cKQ6 2 u →
    ∃ w, LatEq KQ6 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ6; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ6; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ6; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ6 u, ?_⟩
  intro i j
  rw [KQ6]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ6, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ6_3 : ∀ u, ScalarHyp KQ6 u → CountsInside cKQ6 3 u →
    ∃ w, LatEq KQ6 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ6; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ6; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ6; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ6; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ6; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ6; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ6 u, ?_⟩
  intro i j
  rw [KQ6]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ6, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ6 (k : Fin 4) (hk0 : k ≠ cKQ6 0) : Even3Inside KQ6 cKQ6 k := by
  fin_cases k
  · exact absurd (by unfold cKQ6; decide) hk0
  · exact even3Inside_of_scalar KQ6 cKQ6 1 KQ6_three KQ6_card (scalar_inside_KQ6_1)
  · exact even3Inside_of_scalar KQ6 cKQ6 2 KQ6_three KQ6_card (scalar_inside_KQ6_2)
  · exact even3Inside_of_scalar KQ6 cKQ6 3 KQ6_three KQ6_card (scalar_inside_KQ6_3)

def aKQ6 : Multiset (Fin 4) → ℕ := fun τ => if τ = {2,2,2} then 1 else if τ = {2,2,3} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ6 : ∀ u c0, ScalarHyp KQ6 u → LatEq KQ6 u c0 →
    ∃ c, LatEq KQ6 u c ∧ ∀ τ ∈ KQ6, -((aKQ6 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ6; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ6; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ6; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ6, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ6 u, ?_, ?_⟩
  · intro i j
    rw [KQ6]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ6, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
    generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ6, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ6, coeffList, aKQ6, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ6 : WitnessBoundK KQ6 840 1700 := by
  have h : WitnessBoundK KQ6 840 (∑ τ ∈ KQ6, (aKQ6 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ6 KQ6_card aKQ6 scalar_witness_KQ6 840
  have hv : ∑ τ ∈ KQ6, (aKQ6 τ * 840 + 4) = 1700 := by unfold KQ6 aKQ6; decide
  rwa [hv] at h

theorem kappaLinks3_KQ6 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ6 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ6_three

/-- **`UniversalCert KQ6`**. -/
theorem universalCert_KQ6 : UniversalCert KQ6 :=
  universalCert_of_components KQ6 cKQ6 compLabel_KQ6 typesInside_KQ6 fun k => by
    by_cases h0 : k = cKQ6 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ6 cKQ6 (cKQ6 0) compLabel_KQ6 KQ6_card kappaLinks3_KQ6
        (localWalk4_KQ6 _) chiKQ6_0 chiKQ6_0_bound kills_KQ6_0 chargeInside_KQ6_0
        (fun p A hA hact hin h3 => dvd_KQ6_0 p A hA hact hin h3) TpKQ6_0 TmKQ6_0 Tp_charge_KQ6_0 Tm_charge_KQ6_0
        1700 wb_KQ6 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ6 cKQ6 k compLabel_KQ6 KQ6_card kappaLinks3_KQ6
        (localWalk4_KQ6 k) (even3Inside_KQ6 k h0) 1700
        (fun p P hK hdiv => wb_KQ6 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 112 113 122 123 133`.
/-- `{001 002 011 012 022 333}`. -/
noncomputable def KQ7 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {3, 3, 3}}

theorem KQ7_card : ∀ τ ∈ KQ7, Multiset.card τ = 3 := by unfold KQ7; decide

theorem KQ7_card_eq : KQ7.card = 6 := by unfold KQ7; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ7 : FiveStepLinks KQ7 := by
  unfold FiveStepLinks Link KQ7; decide

def kappaKQ7 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ7 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ7 := by
  refine ⟨kappaKQ7, ?_, ?_⟩ <;> unfold Link KQ7 kappaKQ7 <;> decide

theorem familyFacts_KQ7 : FamilyFacts KQ7 :=
  ⟨KQ7_card, by unfold Link KQ7; decide,
    by intro i; fin_cases i <;> (unfold Link KQ7; decide)⟩

def cKQ7 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ7 : CompLabel KQ7 cKQ7 := by
  unfold CompLabel Link KQ7 cKQ7; decide

theorem typesInside_KQ7 : TypesInside KQ7 cKQ7 := by
  unfold TypesInside KQ7 cKQ7; decide

theorem localWalk4_KQ7 (k : Fin 4) : LocalWalk4 KQ7 cKQ7 k := by
  revert k; unfold LocalWalk4 Link KQ7 cKQ7; decide


theorem KQ7_three : ThreeStepLinks KQ7 := by unfold ThreeStepLinks Link KQ7; decide

def canon_KQ7 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ7_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, 2, 0], ![-1, 2, 2, 0], ![0, 0, 0, 0]]
theorem chiKQ7_0_bound : ∀ i j, |chiKQ7_0 i j| ≤ 4 := by decide
theorem chiKQ7_0_00 : chiKQ7_0 0 0 = 2 := rfl
theorem chiKQ7_0_01 : chiKQ7_0 0 1 = -1 := rfl
theorem chiKQ7_0_02 : chiKQ7_0 0 2 = -1 := rfl
theorem chiKQ7_0_03 : chiKQ7_0 0 3 = 0 := rfl
theorem chiKQ7_0_10 : chiKQ7_0 1 0 = -1 := rfl
theorem chiKQ7_0_11 : chiKQ7_0 1 1 = 2 := rfl
theorem chiKQ7_0_12 : chiKQ7_0 1 2 = 2 := rfl
theorem chiKQ7_0_13 : chiKQ7_0 1 3 = 0 := rfl
theorem chiKQ7_0_20 : chiKQ7_0 2 0 = -1 := rfl
theorem chiKQ7_0_21 : chiKQ7_0 2 1 = 2 := rfl
theorem chiKQ7_0_22 : chiKQ7_0 2 2 = 2 := rfl
theorem chiKQ7_0_23 : chiKQ7_0 2 3 = 0 := rfl
theorem chiKQ7_0_30 : chiKQ7_0 3 0 = 0 := rfl
theorem chiKQ7_0_31 : chiKQ7_0 3 1 = 0 := rfl
theorem chiKQ7_0_32 : chiKQ7_0 3 2 = 0 := rfl
theorem chiKQ7_0_33 : chiKQ7_0 3 3 = 0 := rfl
theorem kills_KQ7_0 : Kills chiKQ7_0 KQ7 := by
  unfold Kills pair KQ7 chiKQ7_0; decide
def TpKQ7_0 : Template KQ7 cKQ7 (cKQ7 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ7_0 : charge chiKQ7_0 TpKQ7_0.L TpKQ7_0.E = 12 := by decide
def TmKQ7_0 : Template KQ7 cKQ7 (cKQ7 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ7_0 : charge chiKQ7_0 TmKQ7_0.L TmKQ7_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ7_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ7 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ7_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ7 (cKQ7 0) u) : ∃ c, LatEq KQ7 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ7; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ7_0_00, chiKQ7_0_01, chiKQ7_0_02, chiKQ7_0_03, chiKQ7_0_10, chiKQ7_0_11, chiKQ7_0_12, chiKQ7_0_13, chiKQ7_0_20, chiKQ7_0_21, chiKQ7_0_22, chiKQ7_0_23, chiKQ7_0_30, chiKQ7_0_31, chiKQ7_0_32, chiKQ7_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ7 u, ?_⟩
  intro i j
  rw [KQ7]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ7, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ7_0 : ChargeInside KQ7 cKQ7 (cKQ7 0) chiKQ7_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ7_three KQ7_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ7_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ7 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ7_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ7 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ7 (cKQ7 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ7_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ7) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ7; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ7_0_00, chiKQ7_0_01, chiKQ7_0_02, chiKQ7_0_03, chiKQ7_0_10, chiKQ7_0_11, chiKQ7_0_12, chiKQ7_0_13, chiKQ7_0_20, chiKQ7_0_21, chiKQ7_0_22, chiKQ7_0_23, chiKQ7_0_30, chiKQ7_0_31, chiKQ7_0_32, chiKQ7_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ7_1 : ∀ u, ScalarHyp KQ7 u → CountsInside cKQ7 1 u →
    ∃ w, LatEq KQ7 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ7; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ7; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ7; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ7; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ7; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ7; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ7; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ7 u, ?_⟩
  intro i j
  rw [KQ7]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ7, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ7_2 : ∀ u, ScalarHyp KQ7 u → CountsInside cKQ7 2 u →
    ∃ w, LatEq KQ7 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ7; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ7; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ7; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ7; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ7; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ7; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ7; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ7 u, ?_⟩
  intro i j
  rw [KQ7]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ7, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ7_3 : ∀ u, ScalarHyp KQ7 u → CountsInside cKQ7 3 u →
    ∃ w, LatEq KQ7 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ7; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ7; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ7; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ7; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ7; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ7; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ7 u, ?_⟩
  intro i j
  rw [KQ7]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ7, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (1 * u 3 3) / 3 = qv2 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ7 (k : Fin 4) (hk0 : k ≠ cKQ7 0) : Even3Inside KQ7 cKQ7 k := by
  fin_cases k
  · exact absurd (by unfold cKQ7; decide) hk0
  · exact even3Inside_of_scalar KQ7 cKQ7 1 KQ7_three KQ7_card (scalar_inside_KQ7_1)
  · exact even3Inside_of_scalar KQ7 cKQ7 2 KQ7_three KQ7_card (scalar_inside_KQ7_2)
  · exact even3Inside_of_scalar KQ7 cKQ7 3 KQ7_three KQ7_card (scalar_inside_KQ7_3)

def aKQ7 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ7 : ∀ u c0, ScalarHyp KQ7 u → LatEq KQ7 u c0 →
    ∃ c, LatEq KQ7 u c ∧ ∀ τ ∈ KQ7, -((aKQ7 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ7; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ7; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ7; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ7, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ7 u, ?_, ?_⟩
  · intro i j
    rw [KQ7]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ7, coeffList, ite_true, ite_false]
    have hqv0 : (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2 = qv0 at *
    generalize (1 * u 0 2 - 1 * u 1 2 - 2 * u 2 2) / 2 = qv1 at *
    generalize (1 * u 3 3) / 3 = qv2 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ7, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ7, coeffList, aKQ7, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ7 : WitnessBoundK KQ7 840 1704 := by
  have h : WitnessBoundK KQ7 840 (∑ τ ∈ KQ7, (aKQ7 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ7 KQ7_card aKQ7 scalar_witness_KQ7 840
  have hv : ∑ τ ∈ KQ7, (aKQ7 τ * 840 + 4) = 1704 := by unfold KQ7 aKQ7; decide
  rwa [hv] at h

theorem kappaLinks3_KQ7 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ7 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ7_three

/-- **`UniversalCert KQ7`**. -/
theorem universalCert_KQ7 : UniversalCert KQ7 :=
  universalCert_of_components KQ7 cKQ7 compLabel_KQ7 typesInside_KQ7 fun k => by
    by_cases h0 : k = cKQ7 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ7 cKQ7 (cKQ7 0) compLabel_KQ7 KQ7_card kappaLinks3_KQ7
        (localWalk4_KQ7 _) chiKQ7_0 chiKQ7_0_bound kills_KQ7_0 chargeInside_KQ7_0
        (fun p A hA hact hin h3 => dvd_KQ7_0 p A hA hact hin h3) TpKQ7_0 TmKQ7_0 Tp_charge_KQ7_0 Tm_charge_KQ7_0
        1704 wb_KQ7 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ7 cKQ7 k compLabel_KQ7 KQ7_card kappaLinks3_KQ7
        (localWalk4_KQ7 k) (even3Inside_KQ7 k h0) 1704
        (fun p P hK hdiv => wb_KQ7 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 112 113 123 223 233`.
/-- `{001 002 012 112 122 333}`. -/
noncomputable def KQ8 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KQ8_card : ∀ τ ∈ KQ8, Multiset.card τ = 3 := by unfold KQ8; decide

theorem KQ8_card_eq : KQ8.card = 6 := by unfold KQ8; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ8 : FiveStepLinks KQ8 := by
  unfold FiveStepLinks Link KQ8; decide

def kappaKQ8 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ8 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ8 := by
  refine ⟨kappaKQ8, ?_, ?_⟩ <;> unfold Link KQ8 kappaKQ8 <;> decide

theorem familyFacts_KQ8 : FamilyFacts KQ8 :=
  ⟨KQ8_card, by unfold Link KQ8; decide,
    by intro i; fin_cases i <;> (unfold Link KQ8; decide)⟩

def cKQ8 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ8 : CompLabel KQ8 cKQ8 := by
  unfold CompLabel Link KQ8 cKQ8; decide

theorem typesInside_KQ8 : TypesInside KQ8 cKQ8 := by
  unfold TypesInside KQ8 cKQ8; decide

theorem localWalk4_KQ8 (k : Fin 4) : LocalWalk4 KQ8 cKQ8 k := by
  revert k; unfold LocalWalk4 Link KQ8 cKQ8; decide


theorem KQ8_three : ThreeStepLinks KQ8 := by unfold ThreeStepLinks Link KQ8; decide

def canon_KQ8 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4), ({0,0,2}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4), ({0,1,2}, (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2), ({1,1,2}, (1 * u 1 1) / 1), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ8_0 : Fin 4 → Fin 4 → ℤ := ![![-2, 1, 1, 0], ![1, 4, -2, 0], ![1, -2, 4, 0], ![0, 0, 0, 0]]
theorem chiKQ8_0_bound : ∀ i j, |chiKQ8_0 i j| ≤ 4 := by decide
theorem chiKQ8_0_00 : chiKQ8_0 0 0 = -2 := rfl
theorem chiKQ8_0_01 : chiKQ8_0 0 1 = 1 := rfl
theorem chiKQ8_0_02 : chiKQ8_0 0 2 = 1 := rfl
theorem chiKQ8_0_03 : chiKQ8_0 0 3 = 0 := rfl
theorem chiKQ8_0_10 : chiKQ8_0 1 0 = 1 := rfl
theorem chiKQ8_0_11 : chiKQ8_0 1 1 = 4 := rfl
theorem chiKQ8_0_12 : chiKQ8_0 1 2 = -2 := rfl
theorem chiKQ8_0_13 : chiKQ8_0 1 3 = 0 := rfl
theorem chiKQ8_0_20 : chiKQ8_0 2 0 = 1 := rfl
theorem chiKQ8_0_21 : chiKQ8_0 2 1 = -2 := rfl
theorem chiKQ8_0_22 : chiKQ8_0 2 2 = 4 := rfl
theorem chiKQ8_0_23 : chiKQ8_0 2 3 = 0 := rfl
theorem chiKQ8_0_30 : chiKQ8_0 3 0 = 0 := rfl
theorem chiKQ8_0_31 : chiKQ8_0 3 1 = 0 := rfl
theorem chiKQ8_0_32 : chiKQ8_0 3 2 = 0 := rfl
theorem chiKQ8_0_33 : chiKQ8_0 3 3 = 0 := rfl
theorem kills_KQ8_0 : Kills chiKQ8_0 KQ8 := by
  unfold Kills pair KQ8 chiKQ8_0; decide
def TpKQ8_0 : Template KQ8 cKQ8 (cKQ8 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 1, 1, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ8_0 : charge chiKQ8_0 TpKQ8_0.L TpKQ8_0.E = 12 := by decide
def TmKQ8_0 : Template KQ8 cKQ8 (cKQ8 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ8_0 : charge chiKQ8_0 TmKQ8_0.L TmKQ8_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ8_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ8 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ8_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ8 (cKQ8 0) u) : ∃ c, LatEq KQ8 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ8; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ8_0_00, chiKQ8_0_01, chiKQ8_0_02, chiKQ8_0_03, chiKQ8_0_10, chiKQ8_0_11, chiKQ8_0_12, chiKQ8_0_13, chiKQ8_0_20, chiKQ8_0_21, chiKQ8_0_22, chiKQ8_0_23, chiKQ8_0_30, chiKQ8_0_31, chiKQ8_0_32, chiKQ8_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ8 u, ?_⟩
  intro i j
  rw [KQ8]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ8, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 * 4 = 2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 * 4 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 * 2 = -2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 = qv0 at *
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 = qv1 at *
  generalize (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 = qv2 at *
  generalize (1 * u 3 3) / 3 = qv3 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ8_0 : ChargeInside KQ8 cKQ8 (cKQ8 0) chiKQ8_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ8_three KQ8_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ8_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ8 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ8_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ8 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ8 (cKQ8 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ8_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ8) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ8; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ8_0_00, chiKQ8_0_01, chiKQ8_0_02, chiKQ8_0_03, chiKQ8_0_10, chiKQ8_0_11, chiKQ8_0_12, chiKQ8_0_13, chiKQ8_0_20, chiKQ8_0_21, chiKQ8_0_22, chiKQ8_0_23, chiKQ8_0_30, chiKQ8_0_31, chiKQ8_0_32, chiKQ8_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ8_1 : ∀ u, ScalarHyp KQ8 u → CountsInside cKQ8 1 u →
    ∃ w, LatEq KQ8 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ8; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ8; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ8; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ8; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ8; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ8; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ8; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ8 u, ?_⟩
  intro i j
  rw [KQ8]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ8, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 * 4 = 2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 * 4 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 * 2 = -2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 = qv0 at *
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 = qv1 at *
  generalize (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 = qv2 at *
  generalize (1 * u 3 3) / 3 = qv3 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ8_2 : ∀ u, ScalarHyp KQ8 u → CountsInside cKQ8 2 u →
    ∃ w, LatEq KQ8 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ8; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ8; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ8; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ8; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ8; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ8; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ8; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ8 u, ?_⟩
  intro i j
  rw [KQ8]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ8, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 * 4 = 2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 * 4 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 * 2 = -2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 = qv0 at *
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 = qv1 at *
  generalize (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 = qv2 at *
  generalize (1 * u 3 3) / 3 = qv3 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ8_3 : ∀ u, ScalarHyp KQ8 u → CountsInside cKQ8 3 u →
    ∃ w, LatEq KQ8 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ8; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ8; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ8; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ8; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ8; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ8; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ8 u, ?_⟩
  intro i j
  rw [KQ8]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ8, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 * 4 = 2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 * 4 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 * 2 = -2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 = qv0 at *
  generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 = qv1 at *
  generalize (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 = qv2 at *
  generalize (1 * u 3 3) / 3 = qv3 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ8 (k : Fin 4) (hk0 : k ≠ cKQ8 0) : Even3Inside KQ8 cKQ8 k := by
  fin_cases k
  · exact absurd (by unfold cKQ8; decide) hk0
  · exact even3Inside_of_scalar KQ8 cKQ8 1 KQ8_three KQ8_card (scalar_inside_KQ8_1)
  · exact even3Inside_of_scalar KQ8 cKQ8 2 KQ8_three KQ8_card (scalar_inside_KQ8_2)
  · exact even3Inside_of_scalar KQ8 cKQ8 3 KQ8_three KQ8_card (scalar_inside_KQ8_3)

def aKQ8 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else if τ = {0,1,2} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ8 : ∀ u c0, ScalarHyp KQ8 u → LatEq KQ8 u c0 →
    ∃ c, LatEq KQ8 u c ∧ ∀ τ ∈ KQ8, -((aKQ8 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ8; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ8; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ8; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ8, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ8 u, ?_, ?_⟩
  · intro i j
    rw [KQ8]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ8, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 * 4 = 2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 * 4 = 2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 * 2 = -2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4 = qv0 at *
    generalize (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4 = qv1 at *
    generalize (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2 = qv2 at *
    generalize (1 * u 3 3) / 3 = qv3 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ8, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ8, coeffList, aKQ8, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ8 : WitnessBoundK KQ8 840 2544 := by
  have h : WitnessBoundK KQ8 840 (∑ τ ∈ KQ8, (aKQ8 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ8 KQ8_card aKQ8 scalar_witness_KQ8 840
  have hv : ∑ τ ∈ KQ8, (aKQ8 τ * 840 + 4) = 2544 := by unfold KQ8 aKQ8; decide
  rwa [hv] at h

theorem kappaLinks3_KQ8 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ8 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ8_three

/-- **`UniversalCert KQ8`**. -/
theorem universalCert_KQ8 : UniversalCert KQ8 :=
  universalCert_of_components KQ8 cKQ8 compLabel_KQ8 typesInside_KQ8 fun k => by
    by_cases h0 : k = cKQ8 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ8 cKQ8 (cKQ8 0) compLabel_KQ8 KQ8_card kappaLinks3_KQ8
        (localWalk4_KQ8 _) chiKQ8_0 chiKQ8_0_bound kills_KQ8_0 chargeInside_KQ8_0
        (fun p A hA hact hin h3 => dvd_KQ8_0 p A hA hact hin h3) TpKQ8_0 TmKQ8_0 Tp_charge_KQ8_0 Tm_charge_KQ8_0
        2544 wb_KQ8 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ8 cKQ8 k compLabel_KQ8 KQ8_card kappaLinks3_KQ8
        (localWalk4_KQ8 k) (even3Inside_KQ8 k h0) 2544
        (fun p P hK hdiv => wb_KQ8 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 001 011 111 223 233`.
/-- `{001 011 222 223 233 333}`. -/
noncomputable def KQ9 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {2, 2, 3}, {2, 3, 3}, {3, 3, 3}}

theorem KQ9_card : ∀ τ ∈ KQ9, Multiset.card τ = 3 := by unfold KQ9; decide

theorem KQ9_card_eq : KQ9.card = 6 := by unfold KQ9; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ9 : FiveStepLinks KQ9 := by
  unfold FiveStepLinks Link KQ9; decide

def kappaKQ9 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 2], ![0, 0, 2, 2]]

theorem kappaLinks_KQ9 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ9 := by
  refine ⟨kappaKQ9, ?_, ?_⟩ <;> unfold Link KQ9 kappaKQ9 <;> decide

theorem familyFacts_KQ9 : FamilyFacts KQ9 :=
  ⟨KQ9_card, by unfold Link KQ9; decide,
    by intro i; fin_cases i <;> (unfold Link KQ9; decide)⟩

def cKQ9 : Fin 4 → Fin 4 := ![0, 0, 2, 2]

theorem compLabel_KQ9 : CompLabel KQ9 cKQ9 := by
  unfold CompLabel Link KQ9 cKQ9; decide

theorem typesInside_KQ9 : TypesInside KQ9 cKQ9 := by
  unfold TypesInside KQ9 cKQ9; decide

theorem localWalk4_KQ9 (k : Fin 4) : LocalWalk4 KQ9 cKQ9 k := by
  revert k; unfold LocalWalk4 Link KQ9 cKQ9; decide


theorem KQ9_three : ThreeStepLinks KQ9 := by unfold ThreeStepLinks Link KQ9; decide

def canon_KQ9 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6), ({2,2,3}, (1 * u 2 3 - 2 * u 3 3) / 2), ({2,3,3}, (1 * u 3 3) / 1)]

def chiKQ9_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ9_0_bound : ∀ i j, |chiKQ9_0 i j| ≤ 4 := by decide
theorem chiKQ9_0_00 : chiKQ9_0 0 0 = 2 := rfl
theorem chiKQ9_0_01 : chiKQ9_0 0 1 = -1 := rfl
theorem chiKQ9_0_02 : chiKQ9_0 0 2 = 0 := rfl
theorem chiKQ9_0_03 : chiKQ9_0 0 3 = 0 := rfl
theorem chiKQ9_0_10 : chiKQ9_0 1 0 = -1 := rfl
theorem chiKQ9_0_11 : chiKQ9_0 1 1 = 2 := rfl
theorem chiKQ9_0_12 : chiKQ9_0 1 2 = 0 := rfl
theorem chiKQ9_0_13 : chiKQ9_0 1 3 = 0 := rfl
theorem chiKQ9_0_20 : chiKQ9_0 2 0 = 0 := rfl
theorem chiKQ9_0_21 : chiKQ9_0 2 1 = 0 := rfl
theorem chiKQ9_0_22 : chiKQ9_0 2 2 = 0 := rfl
theorem chiKQ9_0_23 : chiKQ9_0 2 3 = 0 := rfl
theorem chiKQ9_0_30 : chiKQ9_0 3 0 = 0 := rfl
theorem chiKQ9_0_31 : chiKQ9_0 3 1 = 0 := rfl
theorem chiKQ9_0_32 : chiKQ9_0 3 2 = 0 := rfl
theorem chiKQ9_0_33 : chiKQ9_0 3 3 = 0 := rfl
theorem kills_KQ9_0 : Kills chiKQ9_0 KQ9 := by
  unfold Kills pair KQ9 chiKQ9_0; decide
def TpKQ9_0 : Template KQ9 cKQ9 (cKQ9 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ9_0 : charge chiKQ9_0 TpKQ9_0.L TpKQ9_0.E = 12 := by decide
def TmKQ9_0 : Template KQ9 cKQ9 (cKQ9 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ9_0 : charge chiKQ9_0 TmKQ9_0.L TmKQ9_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ9_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ9 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ9_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ9 (cKQ9 0) u) : ∃ c, LatEq KQ9 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ9; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ9; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ9; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ9_0_00, chiKQ9_0_01, chiKQ9_0_02, chiKQ9_0_03, chiKQ9_0_10, chiKQ9_0_11, chiKQ9_0_12, chiKQ9_0_13, chiKQ9_0_20, chiKQ9_0_21, chiKQ9_0_22, chiKQ9_0_23, chiKQ9_0_30, chiKQ9_0_31, chiKQ9_0_32, chiKQ9_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ9 u, ?_⟩
  intro i j
  rw [KQ9]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ9, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ9_0 : ChargeInside KQ9 cKQ9 (cKQ9 0) chiKQ9_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ9_three KQ9_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ9_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ9 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ9_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ9 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ9 (cKQ9 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ9_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ9) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have o22 : u 2 2 = 0 := hin' 2 2 (by unfold cKQ9; decide)
  have o23 : u 2 3 = 0 := hin' 2 3 (by unfold cKQ9; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ9; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ9_0_00, chiKQ9_0_01, chiKQ9_0_02, chiKQ9_0_03, chiKQ9_0_10, chiKQ9_0_11, chiKQ9_0_12, chiKQ9_0_13, chiKQ9_0_20, chiKQ9_0_21, chiKQ9_0_22, chiKQ9_0_23, chiKQ9_0_30, chiKQ9_0_31, chiKQ9_0_32, chiKQ9_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ9_1 : ∀ u, ScalarHyp KQ9 u → CountsInside cKQ9 1 u →
    ∃ w, LatEq KQ9 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ9; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ9; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ9; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ9; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ9; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ9; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ9 u, ?_⟩
  intro i j
  rw [KQ9]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ9, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ9_2 : ∀ u, ScalarHyp KQ9 u → CountsInside cKQ9 2 u →
    ∃ w, LatEq KQ9 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ9; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ9; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ9; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ9 u, ?_⟩
  intro i j
  rw [KQ9]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ9, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ9_3 : ∀ u, ScalarHyp KQ9 u → CountsInside cKQ9 3 u →
    ∃ w, LatEq KQ9 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ9; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ9; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ9; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ9; decide)
  have o23 : u 2 3 = 0 := hin 2 3 (by unfold cKQ9; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ9; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ9 u, ?_⟩
  intro i j
  rw [KQ9]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ9, coeffList, ite_true, ite_false]
  have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
  generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ9 (k : Fin 4) (hk0 : k ≠ cKQ9 0) : Even3Inside KQ9 cKQ9 k := by
  fin_cases k
  · exact absurd (by unfold cKQ9; decide) hk0
  · exact even3Inside_of_scalar KQ9 cKQ9 1 KQ9_three KQ9_card (scalar_inside_KQ9_1)
  · exact even3Inside_of_scalar KQ9 cKQ9 2 KQ9_three KQ9_card (scalar_inside_KQ9_2)
  · exact even3Inside_of_scalar KQ9 cKQ9 3 KQ9_three KQ9_card (scalar_inside_KQ9_3)

def aKQ9 : Multiset (Fin 4) → ℕ := fun τ => if τ = {2,2,2} then 1 else if τ = {2,2,3} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ9 : ∀ u c0, ScalarHyp KQ9 u → LatEq KQ9 u c0 →
    ∃ c, LatEq KQ9 u c ∧ ∀ τ ∈ KQ9, -((aKQ9 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ9; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ9; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ9; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ9; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ9, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e11 e22 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ9 u, ?_, ?_⟩
  · intro i j
    rw [KQ9]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ9, coeffList, ite_true, ite_false]
    have hqv0 : (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 * 6 = 2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 2 3 - 2 * u 3 3) / 2 * 2 = 1 * u 2 3 - 2 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (2 * u 2 2 - 1 * u 2 3 + 2 * u 3 3) / 6 = qv0 at *
    generalize (1 * u 2 3 - 2 * u 3 3) / 2 = qv1 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ9, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ9, coeffList, aKQ9, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ9 : WitnessBoundK KQ9 840 1704 := by
  have h : WitnessBoundK KQ9 840 (∑ τ ∈ KQ9, (aKQ9 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ9 KQ9_card aKQ9 scalar_witness_KQ9 840
  have hv : ∑ τ ∈ KQ9, (aKQ9 τ * 840 + 4) = 1704 := by unfold KQ9 aKQ9; decide
  rwa [hv] at h

theorem kappaLinks3_KQ9 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ9 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ9_three

/-- **`UniversalCert KQ9`**. -/
theorem universalCert_KQ9 : UniversalCert KQ9 :=
  universalCert_of_components KQ9 cKQ9 compLabel_KQ9 typesInside_KQ9 fun k => by
    by_cases h0 : k = cKQ9 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ9 cKQ9 (cKQ9 0) compLabel_KQ9 KQ9_card kappaLinks3_KQ9
        (localWalk4_KQ9 _) chiKQ9_0 chiKQ9_0_bound kills_KQ9_0 chargeInside_KQ9_0
        (fun p A hA hact hin h3 => dvd_KQ9_0 p A hA hact hin h3) TpKQ9_0 TmKQ9_0 Tp_charge_KQ9_0 Tm_charge_KQ9_0
        1704 wb_KQ9 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ9 cKQ9 k compLabel_KQ9 KQ9_card kappaLinks3_KQ9
        (localWalk4_KQ9 k) (even3Inside_KQ9 k h0) 1704
        (fun p P hK hdiv => wb_KQ9 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 112 113 122 133 223 233`.
/-- `{001 002 011 022 112 122 333}`. -/
noncomputable def KQ10 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KQ10_card : ∀ τ ∈ KQ10, Multiset.card τ = 3 := by unfold KQ10; decide

theorem KQ10_card_eq : KQ10.card = 7 := by unfold KQ10; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ10 : FiveStepLinks KQ10 := by
  unfold FiveStepLinks Link KQ10; decide

def kappaKQ10 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ10 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ10 := by
  refine ⟨kappaKQ10, ?_, ?_⟩ <;> unfold Link KQ10 kappaKQ10 <;> decide

theorem familyFacts_KQ10 : FamilyFacts KQ10 :=
  ⟨KQ10_card, by unfold Link KQ10; decide,
    by intro i; fin_cases i <;> (unfold Link KQ10; decide)⟩

def cKQ10 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

theorem compLabel_KQ10 : CompLabel KQ10 cKQ10 := by
  unfold CompLabel Link KQ10 cKQ10; decide

theorem typesInside_KQ10 : TypesInside KQ10 cKQ10 := by
  unfold TypesInside KQ10 cKQ10; decide

theorem localWalk4_KQ10 (k : Fin 4) : LocalWalk4 KQ10 cKQ10 k := by
  revert k; unfold LocalWalk4 Link KQ10 cKQ10; decide


theorem KQ10_three : ThreeStepLinks KQ10 := by unfold ThreeStepLinks Link KQ10; decide

def canon_KQ10 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2), ({0,0,2}, (1 * u 0 2 - 2 * u 2 2) / 2), ({0,1,1}, (2 * u 1 1 - 1 * u 1 2) / 2), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ10_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, -1, 0], ![-1, -1, 2, 0], ![0, 0, 0, 0]]
theorem chiKQ10_0_bound : ∀ i j, |chiKQ10_0 i j| ≤ 2 := by decide
theorem chiKQ10_0_00 : chiKQ10_0 0 0 = 2 := rfl
theorem chiKQ10_0_01 : chiKQ10_0 0 1 = -1 := rfl
theorem chiKQ10_0_02 : chiKQ10_0 0 2 = -1 := rfl
theorem chiKQ10_0_03 : chiKQ10_0 0 3 = 0 := rfl
theorem chiKQ10_0_10 : chiKQ10_0 1 0 = -1 := rfl
theorem chiKQ10_0_11 : chiKQ10_0 1 1 = 2 := rfl
theorem chiKQ10_0_12 : chiKQ10_0 1 2 = -1 := rfl
theorem chiKQ10_0_13 : chiKQ10_0 1 3 = 0 := rfl
theorem chiKQ10_0_20 : chiKQ10_0 2 0 = -1 := rfl
theorem chiKQ10_0_21 : chiKQ10_0 2 1 = -1 := rfl
theorem chiKQ10_0_22 : chiKQ10_0 2 2 = 2 := rfl
theorem chiKQ10_0_23 : chiKQ10_0 2 3 = 0 := rfl
theorem chiKQ10_0_30 : chiKQ10_0 3 0 = 0 := rfl
theorem chiKQ10_0_31 : chiKQ10_0 3 1 = 0 := rfl
theorem chiKQ10_0_32 : chiKQ10_0 3 2 = 0 := rfl
theorem chiKQ10_0_33 : chiKQ10_0 3 3 = 0 := rfl
theorem kills_KQ10_0 : Kills chiKQ10_0 KQ10 := by
  unfold Kills pair KQ10 chiKQ10_0; decide
def TpKQ10_0 : Template KQ10 cKQ10 (cKQ10 0) where
  E := {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(3, 4)}
  L := ![0, 0, 0, 1, 2, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ10_0 : charge chiKQ10_0 TpKQ10_0.L TpKQ10_0.E = 6 := by decide
def TmKQ10_0 : Template KQ10 cKQ10 (cKQ10 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 1, 2, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ10_0 : charge chiKQ10_0 TmKQ10_0.L TmKQ10_0.E = -6 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ10_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ10 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ10_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ10 (cKQ10 0) u) : ∃ c, LatEq KQ10 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ10; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ10_0_00, chiKQ10_0_01, chiKQ10_0_02, chiKQ10_0_03, chiKQ10_0_10, chiKQ10_0_11, chiKQ10_0_12, chiKQ10_0_13, chiKQ10_0_20, chiKQ10_0_21, chiKQ10_0_22, chiKQ10_0_23, chiKQ10_0_30, chiKQ10_0_31, chiKQ10_0_32, chiKQ10_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ10 u, ?_⟩
  intro i j
  rw [KQ10]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ10, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv2 at *
  generalize (1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ10_0 : ChargeInside KQ10 cKQ10 (cKQ10 0) chiKQ10_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ10_three KQ10_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ10_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ10 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ10_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ10 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ10 (cKQ10 0) e)
    (h3 : OnePart.Even3 A) : (6 : ℤ) ∣ charge chiKQ10_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ10) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ10; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ10_0_00, chiKQ10_0_01, chiKQ10_0_02, chiKQ10_0_03, chiKQ10_0_10, chiKQ10_0_11, chiKQ10_0_12, chiKQ10_0_13, chiKQ10_0_20, chiKQ10_0_21, chiKQ10_0_22, chiKQ10_0_23, chiKQ10_0_30, chiKQ10_0_31, chiKQ10_0_32, chiKQ10_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ10_1 : ∀ u, ScalarHyp KQ10 u → CountsInside cKQ10 1 u →
    ∃ w, LatEq KQ10 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ10; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ10; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ10; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ10; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ10; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ10; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ10; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ10 u, ?_⟩
  intro i j
  rw [KQ10]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ10, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv2 at *
  generalize (1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ10_2 : ∀ u, ScalarHyp KQ10 u → CountsInside cKQ10 2 u →
    ∃ w, LatEq KQ10 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ10; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ10; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ10; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ10; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ10; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ10; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ10; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ10 u, ?_⟩
  intro i j
  rw [KQ10]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ10, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv2 at *
  generalize (1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ10_3 : ∀ u, ScalarHyp KQ10 u → CountsInside cKQ10 3 u →
    ∃ w, LatEq KQ10 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ10; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ10; decide)
  have o02 : u 0 2 = 0 := hin 0 2 (by unfold cKQ10; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ10; decide)
  have o12 : u 1 2 = 0 := hin 1 2 (by unfold cKQ10; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ10; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ10 u, ?_⟩
  intro i j
  rw [KQ10]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ10, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv2 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv3 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
  have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv0 at *
  generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
  generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv2 at *
  generalize (1 * u 1 2) / 2 = qv3 at *
  generalize (1 * u 3 3) / 3 = qv4 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ10 (k : Fin 4) (hk0 : k ≠ cKQ10 0) : Even3Inside KQ10 cKQ10 k := by
  fin_cases k
  · exact absurd (by unfold cKQ10; decide) hk0
  · exact even3Inside_of_scalar KQ10 cKQ10 1 KQ10_three KQ10_card (scalar_inside_KQ10_1)
  · exact even3Inside_of_scalar KQ10 cKQ10 2 KQ10_three KQ10_card (scalar_inside_KQ10_2)
  · exact even3Inside_of_scalar KQ10 cKQ10 3 KQ10_three KQ10_card (scalar_inside_KQ10_3)

def aKQ10 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,1} then 1 else if τ = {0,0,2} then 1 else if τ = {0,1,1} then 1 else 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ10 : ∀ u c0, ScalarHyp KQ10 u → LatEq KQ10 u c0 →
    ∃ c, LatEq KQ10 u c ∧ ∀ τ ∈ KQ10, -((aKQ10 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ10; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ10; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ10; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ10, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ10 u, ?_, ?_⟩
  · intro i j
    rw [KQ10]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ10, coeffList, ite_true, ite_false]
    have hqv0 : (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 * 2 = 1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 0 2 - 2 * u 2 2) / 2 * 2 = 1 * u 0 2 - 2 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv2 : (2 * u 1 1 - 1 * u 1 2) / 2 * 2 = 2 * u 1 1 - 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv3 : (1 * u 1 2) / 2 * 2 = 1 * u 1 2 := Int.ediv_mul_cancel (by omega)
    have hqv4 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (1 * u 0 1 - 2 * u 1 1 + 1 * u 1 2) / 2 = qv0 at *
    generalize (1 * u 0 2 - 2 * u 2 2) / 2 = qv1 at *
    generalize (2 * u 1 1 - 1 * u 1 2) / 2 = qv2 at *
    generalize (1 * u 1 2) / 2 = qv3 at *
    generalize (1 * u 3 3) / 3 = qv4 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ10, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ10, coeffList, aKQ10, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ10 : WitnessBoundK KQ10 840 2548 := by
  have h : WitnessBoundK KQ10 840 (∑ τ ∈ KQ10, (aKQ10 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ10 KQ10_card aKQ10 scalar_witness_KQ10 840
  have hv : ∑ τ ∈ KQ10, (aKQ10 τ * 840 + 4) = 2548 := by unfold KQ10 aKQ10; decide
  rwa [hv] at h

theorem kappaLinks3_KQ10 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ10 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ10_three

/-- **`UniversalCert KQ10`**. -/
theorem universalCert_KQ10 : UniversalCert KQ10 :=
  universalCert_of_components KQ10 cKQ10 compLabel_KQ10 typesInside_KQ10 fun k => by
    by_cases h0 : k = cKQ10 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U6 KQ10 cKQ10 (cKQ10 0) compLabel_KQ10 KQ10_card kappaLinks3_KQ10
        (localWalk4_KQ10 _) chiKQ10_0 chiKQ10_0_bound kills_KQ10_0 chargeInside_KQ10_0
        (fun p A hA hact hin h3 => dvd_KQ10_0 p A hA hact hin h3) TpKQ10_0 TmKQ10_0 Tp_charge_KQ10_0 Tm_charge_KQ10_0
        2548 wb_KQ10 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ10 cKQ10 k compLabel_KQ10 KQ10_card kappaLinks3_KQ10
        (localWalk4_KQ10 k) (even3Inside_KQ10 k h0) 2548
        (fun p P hK hdiv => wb_KQ10 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

-- Census class `000 111 223 233`.
/-- `{001 011 222 333}`. -/
noncomputable def KQ11 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KQ11_card : ∀ τ ∈ KQ11, Multiset.card τ = 3 := by unfold KQ11; decide

theorem KQ11_card_eq : KQ11.card = 4 := by unfold KQ11; decide


set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KQ11 : FiveStepLinks KQ11 := by
  unfold FiveStepLinks Link KQ11; decide

def kappaKQ11 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KQ11 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ11 := by
  refine ⟨kappaKQ11, ?_, ?_⟩ <;> unfold Link KQ11 kappaKQ11 <;> decide

theorem familyFacts_KQ11 : FamilyFacts KQ11 :=
  ⟨KQ11_card, by unfold Link KQ11; decide,
    by intro i; fin_cases i <;> (unfold Link KQ11; decide)⟩

def cKQ11 : Fin 4 → Fin 4 := ![0, 0, 2, 3]

theorem compLabel_KQ11 : CompLabel KQ11 cKQ11 := by
  unfold CompLabel Link KQ11 cKQ11; decide

theorem typesInside_KQ11 : TypesInside KQ11 cKQ11 := by
  unfold TypesInside KQ11 cKQ11; decide

theorem localWalk4_KQ11 (k : Fin 4) : LocalWalk4 KQ11 cKQ11 k := by
  revert k; unfold LocalWalk4 Link KQ11 cKQ11; decide


theorem KQ11_three : ThreeStepLinks KQ11 := by unfold ThreeStepLinks Link KQ11; decide

def canon_KQ11 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,1}, (1 * u 1 1) / 1), ({2,2,2}, (1 * u 2 2) / 3), ({3,3,3}, (1 * u 3 3) / 3)]

def chiKQ11_0 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
theorem chiKQ11_0_bound : ∀ i j, |chiKQ11_0 i j| ≤ 4 := by decide
theorem chiKQ11_0_00 : chiKQ11_0 0 0 = 2 := rfl
theorem chiKQ11_0_01 : chiKQ11_0 0 1 = -1 := rfl
theorem chiKQ11_0_02 : chiKQ11_0 0 2 = 0 := rfl
theorem chiKQ11_0_03 : chiKQ11_0 0 3 = 0 := rfl
theorem chiKQ11_0_10 : chiKQ11_0 1 0 = -1 := rfl
theorem chiKQ11_0_11 : chiKQ11_0 1 1 = 2 := rfl
theorem chiKQ11_0_12 : chiKQ11_0 1 2 = 0 := rfl
theorem chiKQ11_0_13 : chiKQ11_0 1 3 = 0 := rfl
theorem chiKQ11_0_20 : chiKQ11_0 2 0 = 0 := rfl
theorem chiKQ11_0_21 : chiKQ11_0 2 1 = 0 := rfl
theorem chiKQ11_0_22 : chiKQ11_0 2 2 = 0 := rfl
theorem chiKQ11_0_23 : chiKQ11_0 2 3 = 0 := rfl
theorem chiKQ11_0_30 : chiKQ11_0 3 0 = 0 := rfl
theorem chiKQ11_0_31 : chiKQ11_0 3 1 = 0 := rfl
theorem chiKQ11_0_32 : chiKQ11_0 3 2 = 0 := rfl
theorem chiKQ11_0_33 : chiKQ11_0 3 3 = 0 := rfl
theorem kills_KQ11_0 : Kills chiKQ11_0 KQ11 := by
  unfold Kills pair KQ11 chiKQ11_0; decide
def TpKQ11_0 : Template KQ11 cKQ11 (cKQ11 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tp_charge_KQ11_0 : charge chiKQ11_0 TpKQ11_0.L TpKQ11_0.E = 12 := by decide
def TmKQ11_0 : Template KQ11 cKQ11 (cKQ11 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 1, 1, 0, 0, 1]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide
theorem Tm_charge_KQ11_0 : charge chiKQ11_0 TmKQ11_0.L TmKQ11_0.E = -12 := by decide

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KQ11_0 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KQ11 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKQ11_0 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cKQ11 (cKQ11 0) u) : ∃ c, LatEq KQ11 u c := by
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ11; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ11; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKQ11_0_00, chiKQ11_0_01, chiKQ11_0_02, chiKQ11_0_03, chiKQ11_0_10, chiKQ11_0_11, chiKQ11_0_12, chiKQ11_0_13, chiKQ11_0_20, chiKQ11_0_21, chiKQ11_0_22, chiKQ11_0_23, chiKQ11_0_30, chiKQ11_0_31, chiKQ11_0_32, chiKQ11_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ11 u, ?_⟩
  intro i j
  rw [KQ11]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ11, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 2 2) / 3 * 3 = 1 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 2 2) / 3 = qv0 at *
  generalize (1 * u 3 3) / 3 = qv1 at *
  clear p0 p1 p2 p3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem chargeInside_KQ11_0 : ChargeInside KQ11 cKQ11 (cKQ11 0) chiKQ11_0 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff KQ11_three KQ11_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KQ11_0 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KQ11 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem dvd_KQ11_0 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KQ11 p A)
    (hin : ∀ e ∈ A, InsideE p cKQ11 (cKQ11 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKQ11_0 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KQ11) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have o22 : u 2 2 = 0 := hin' 2 2 (by unfold cKQ11; decide)
  have o33 : u 3 3 = 0 := hin' 3 3 (by unfold cKQ11; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKQ11_0_00, chiKQ11_0_01, chiKQ11_0_02, chiKQ11_0_03, chiKQ11_0_10, chiKQ11_0_11, chiKQ11_0_12, chiKQ11_0_13, chiKQ11_0_20, chiKQ11_0_21, chiKQ11_0_22, chiKQ11_0_23, chiKQ11_0_30, chiKQ11_0_31, chiKQ11_0_32, chiKQ11_0_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ11_1 : ∀ u, ScalarHyp KQ11 u → CountsInside cKQ11 1 u →
    ∃ w, LatEq KQ11 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ11; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ11; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ11; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ11; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ11; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ11 u, ?_⟩
  intro i j
  rw [KQ11]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ11, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 2 2) / 3 * 3 = 1 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 2 2) / 3 = qv0 at *
  generalize (1 * u 3 3) / 3 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ11_2 : ∀ u, ScalarHyp KQ11 u → CountsInside cKQ11 2 u →
    ∃ w, LatEq KQ11 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ11; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ11; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ11; decide)
  have o33 : u 3 3 = 0 := hin 3 3 (by unfold cKQ11; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ11 u, ?_⟩
  intro i j
  rw [KQ11]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ11, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 2 2) / 3 * 3 = 1 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 2 2) / 3 = qv0 at *
  generalize (1 * u 3 3) / 3 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KQ11_3 : ∀ u, ScalarHyp KQ11 u → CountsInside cKQ11 3 u →
    ∃ w, LatEq KQ11 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have o00 : u 0 0 = 0 := hin 0 0 (by unfold cKQ11; decide)
  have o01 : u 0 1 = 0 := hin 0 1 (by unfold cKQ11; decide)
  have o11 : u 1 1 = 0 := hin 1 1 (by unfold cKQ11; decide)
  have o22 : u 2 2 = 0 := hin 2 2 (by unfold cKQ11; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KQ11 u, ?_⟩
  intro i j
  rw [KQ11]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon_KQ11, coeffList, ite_true, ite_false]
  have hqv0 : (1 * u 2 2) / 3 * 3 = 1 * u 2 2 := Int.ediv_mul_cancel (by omega)
  have hqv1 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
  generalize (1 * u 2 2) / 3 = qv0 at *
  generalize (1 * u 3 3) / 3 = qv1 at *
  clear p0 p1 p2 p3 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

theorem even3Inside_KQ11 (k : Fin 4) (hk0 : k ≠ cKQ11 0) : Even3Inside KQ11 cKQ11 k := by
  fin_cases k
  · exact absurd (by unfold cKQ11; decide) hk0
  · exact even3Inside_of_scalar KQ11 cKQ11 1 KQ11_three KQ11_card (scalar_inside_KQ11_1)
  · exact even3Inside_of_scalar KQ11 cKQ11 2 KQ11_three KQ11_card (scalar_inside_KQ11_2)
  · exact even3Inside_of_scalar KQ11 cKQ11 3 KQ11_three KQ11_card (scalar_inside_KQ11_3)

def aKQ11 : Multiset (Fin 4) → ℕ := fun τ => 0
set_option maxHeartbeats 16000000 in
theorem scalar_witness_KQ11 : ∀ u c0, ScalarHyp KQ11 u → LatEq KQ11 u c0 →
    ∃ c, LatEq KQ11 u c ∧ ∀ τ ∈ KQ11, -((aKQ11 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link KQ11; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KQ11; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KQ11; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KQ11; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KQ11; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e11 := hc0 1 1
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) only [KQ11, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e11 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KQ11 u, ?_, ?_⟩
  · intro i j
    rw [KQ11]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [canon_KQ11, coeffList, ite_true, ite_false]
    have hqv0 : (1 * u 2 2) / 3 * 3 = 1 * u 2 2 := Int.ediv_mul_cancel (by omega)
    have hqv1 : (1 * u 3 3) / 3 * 3 = 1 * u 3 3 := Int.ediv_mul_cancel (by omega)
    generalize (1 * u 2 2) / 3 = qv0 at *
    generalize (1 * u 3 3) / 3 = qv1 at *
    clear n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 h3
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KQ11, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [canon_KQ11, coeffList, aKQ11, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero] <;> omega

theorem wb_KQ11 : WitnessBoundK KQ11 840 16 := by
  have h : WitnessBoundK KQ11 840 (∑ τ ∈ KQ11, (aKQ11 τ * 840 + 4)) :=
    witnessBound_of_latEq_lowerA KQ11 KQ11_card aKQ11 scalar_witness_KQ11 840
  have hv : ∑ τ ∈ KQ11, (aKQ11 τ * 840 + 4) = 16 := by unfold KQ11 aKQ11; decide
  rwa [hv] at h

theorem kappaLinks3_KQ11 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KQ11 :=
  PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep KQ11_three

/-- **`UniversalCert KQ11`**. -/
theorem universalCert_KQ11 : UniversalCert KQ11 :=
  universalCert_of_components KQ11 cKQ11 compLabel_KQ11 typesInside_KQ11 fun k => by
    by_cases h0 : k = cKQ11 0
    · subst h0
      exact componentUniversalCert_of_charge_walk_U12 KQ11 cKQ11 (cKQ11 0) compLabel_KQ11 KQ11_card kappaLinks3_KQ11
        (localWalk4_KQ11 _) chiKQ11_0 chiKQ11_0_bound kills_KQ11_0 chargeInside_KQ11_0
        (fun p A hA hact hin h3 => dvd_KQ11_0 p A hA hact hin h3) TpKQ11_0 TmKQ11_0 Tp_charge_KQ11_0 Tm_charge_KQ11_0
        16 wb_KQ11 (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    · exact componentUniversalCert_of_even3_walk_kappa KQ11 cKQ11 k compLabel_KQ11 KQ11_card kappaLinks3_KQ11
        (localWalk4_KQ11 k) (even3Inside_KQ11 k h0) 16
        (fun p P hK hdiv => wb_KQ11 p P (hK.trans (by norm_num)) hdiv)
        (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KQ1
#print axioms PaddedComponents.universalCert_KQ2
#print axioms PaddedComponents.universalCert_KQ3
#print axioms PaddedComponents.universalCert_KQ4
#print axioms PaddedComponents.universalCert_KQ5
#print axioms PaddedComponents.universalCert_KQ6
#print axioms PaddedComponents.universalCert_KQ7
#print axioms PaddedComponents.universalCert_KQ8
#print axioms PaddedComponents.universalCert_KQ9
#print axioms PaddedComponents.universalCert_KQ10
#print axioms PaddedComponents.universalCert_KQ11
