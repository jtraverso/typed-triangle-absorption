/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.FnoC
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Collapse
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ChargeWalk

@[expose] public section

/-!
# Two one-charge families without `ThreeStepLinks`: `KCa = FnoC ∖ {022, 133}`, `KCb = FnoC ∖ {133}`

Both have the charge `chiNoC` of `FnoC` (2 on the diagonal, -1 off it), no torsion (`L_F` is primitive
in `Λ_ord`, Python `kab_data.py`), `KappaLinks` (explicit `κ`) and `FiveStepLinks`. Their lattices,
witnesses and the divisibility `12 ∣ charge` are the `FnoC` proofs with `u 3 3 = 0`
(and `u 2 2 = 0` for `KCa`), using the `FiveStepLinks` collapse `isIntDiv_iff_five`.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12 PaddedGeneral PaddedNoCommon
open PartitionedTriangleAbsorption.StructuralF3General

noncomputable def KCa : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}}

theorem KCa_card : ∀ τ ∈ KCa, Multiset.card τ = 3 := by unfold KCa; decide

theorem not_threeStep_KCa : ¬ ThreeStepLinks KCa := by
  unfold ThreeStepLinks Link KCa; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCa : FiveStepLinks KCa := by
  unfold FiveStepLinks Link KCa; decide

def kappaKCa : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 1, 0, 0]]

theorem kappaLinks_KCa : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCa := by
  refine ⟨kappaKCa, ?_, ?_⟩ <;> unfold Link KCa kappaKCa <;> decide

theorem walk4_KCa : Walk4 (fun i j : Fin 4 => ∃ k, Link KCa i j k) := by
  unfold Walk4; beta_reduce; unfold Link KCa; decide

theorem familyFacts_KCa : FamilyFacts KCa :=
  ⟨KCa_card, by unfold Link KCa; decide, by intro i; fin_cases i <;> (unfold Link KCa; decide)⟩

theorem kills_KCa : Kills chiNoC KCa := by
  unfold Kills pair KCa chiNoC; decide

theorem plus_active_KCa : ActiveEdges KCa plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_KCa : ActiveEdges KCa minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide

set_option maxHeartbeats 4000000 in
theorem scalar_KCa (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCa i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiNoC i j * ((if i = j then 2 else 1) * u i j) = 0) :
    ∃ c, LatEq KCa u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCa; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCa; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCa; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCa; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KCa; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨coeffList [({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 3 / 2),
    ({0,0,2}, u 0 2 / 2),
    ({0,1,1}, u 1 1 - u 1 3 / 2),
    ({1,1,3}, u 1 3 / 2)], ?_⟩
  intro i j
  rw [KCa]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [coeffList, ite_true, ite_false]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

set_option maxHeartbeats 4000000 in
theorem lower_KCa (u : Fin 4 → Fin 4 → ℤ) (c : Multiset (Fin 4) → ℤ)
    (hs : ∀ i j, u i j = u j i) (hn : ∀ i j, 0 ≤ u i j) (h : LatEq KCa u c) :
    ∀ τ ∈ KCa, -(totalU u) ≤ c τ := by
  have e00 := h 0 0; have e01 := h 0 1; have e02 := h 0 2; have e11 := h 1 1
  have e13 := h 1 3; have e22 := h 2 2; have e33 := h 3 3
  simp (config := {decide := true}) only [KCa, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e13 e22 e33
  unfold totalU
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3
  have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2
  have n23 := hn 2 3; have n33 := hn 3 3
  intro τ hτ
  simp only [KCa, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp only [Multiset.insert_eq_cons] at e00 e01 e02 e11 e13 e22 e33 ⊢ <;> omega

theorem chargeLattice_KCa : ChargeLattice KCa chiNoC := by
  intro V _ _ p E hloop
  constructor
  · intro h
    exact ⟨active_of_isIntDiv KCa_card h, even_of_isIntDiv KCa_card hloop h,
      charge_eq_zero_of_isIntDiv kills_KCa h⟩
  · rintro ⟨hact, hev, hch⟩
    rw [isIntDiv_iff_five fiveStep_KCa KCa_card hloop]
    refine ⟨hact, hev, ?_⟩
    rw [charge_counts] at hch
    obtain ⟨c, hc⟩ := scalar_KCa (unorderedCount p E) (unorderedCount_swap p E)
      (counts_forbid hact) (counts_parity p E hloop hev) hch
    exact ⟨c, (latEq_counts_iff KCa p E c).mp hc⟩

set_option maxHeartbeats 4000000 in
theorem twelve_dvd_KCa {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCa p A)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiNoC p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCa) hact
  have hp := counts_parity p A hloop h3.2
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCa; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCa; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCa; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCa; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KCa; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem card_KCa : KCa.card = 4 := by unfold KCa; decide

theorem witnessBound_KCa (K : ℕ) : WitnessBoundK KCa K (4 * K) := by
  have h : WitnessBoundK KCa K (KCa.card * K) := witnessBound_of_lower KCa K lower_KCa
  rwa [card_KCa] at h

theorem KCa_budgets :
    terminalOrder 504 (4 * 504) 4 ≤ 2 ^ 21 ∧ terminalSize 504 (4 * 504) ≤ 2 ^ 21 := by
  unfold terminalOrder
    terminalSize; decide

theorem universalCert_KCa : UniversalCert KCa :=
  universalCert_of_charge_walk_kappa KCa KCa_card kappaLinks_KCa walk4_KCa chiNoC chiNoC_bound
    chargeLattice_KCa (fun p A hA hact h3 => twelve_dvd_KCa p A hA hact h3) plus_active_KCa
    minus_active_KCa plus_charge_FnoC minus_charge_FnoC _ (witnessBound_KCa 504)
    KCa_budgets.1 KCa_budgets.2

noncomputable def KCb : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}}

theorem KCb_card : ∀ τ ∈ KCb, Multiset.card τ = 3 := by unfold KCb; decide

theorem not_threeStep_KCb : ¬ ThreeStepLinks KCb := by
  unfold ThreeStepLinks Link KCb; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCb : FiveStepLinks KCb := by
  unfold FiveStepLinks Link KCb; decide

def kappaKCb : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 1, 0, 0]]

theorem kappaLinks_KCb : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCb := by
  refine ⟨kappaKCb, ?_, ?_⟩ <;> unfold Link KCb kappaKCb <;> decide

theorem walk4_KCb : Walk4 (fun i j : Fin 4 => ∃ k, Link KCb i j k) := by
  unfold Walk4; beta_reduce; unfold Link KCb; decide

theorem familyFacts_KCb : FamilyFacts KCb :=
  ⟨KCb_card, by unfold Link KCb; decide, by intro i; fin_cases i <;> (unfold Link KCb; decide)⟩

theorem kills_KCb : Kills chiNoC KCb := by
  unfold Kills pair KCb chiNoC; decide

theorem plus_active_KCb : ActiveEdges KCb plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_KCb : ActiveEdges KCb minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide

set_option maxHeartbeats 4000000 in
theorem scalar_KCb (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCb i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiNoC i j * ((if i = j then 2 else 1) * u i j) = 0) :
    ∃ c, LatEq KCb u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCb; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCb; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCb; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KCb; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨coeffList [({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 3 / 2),
    ({0,0,2}, u 0 2 / 2 - u 2 2),
    ({0,1,1}, u 1 1 - u 1 3 / 2),
    ({0,2,2}, u 2 2),
    ({1,1,3}, u 1 3 / 2)], ?_⟩
  intro i j
  rw [KCb]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [coeffList, ite_true, ite_false]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

set_option maxHeartbeats 4000000 in
theorem lower_KCb (u : Fin 4 → Fin 4 → ℤ) (c : Multiset (Fin 4) → ℤ)
    (hs : ∀ i j, u i j = u j i) (hn : ∀ i j, 0 ≤ u i j) (h : LatEq KCb u c) :
    ∀ τ ∈ KCb, -(totalU u) ≤ c τ := by
  have e00 := h 0 0; have e01 := h 0 1; have e02 := h 0 2; have e11 := h 1 1
  have e13 := h 1 3; have e22 := h 2 2; have e33 := h 3 3
  simp (config := {decide := true}) only [KCb, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] at e00 e01 e02 e11 e13 e22 e33
  unfold totalU
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3
  have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2
  have n23 := hn 2 3; have n33 := hn 3 3
  intro τ hτ
  simp only [KCb, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Multiset.insert_eq_cons] at e00 e01 e02 e11 e13 e22 e33 ⊢ <;> omega

theorem chargeLattice_KCb : ChargeLattice KCb chiNoC := by
  intro V _ _ p E hloop
  constructor
  · intro h
    exact ⟨active_of_isIntDiv KCb_card h, even_of_isIntDiv KCb_card hloop h,
      charge_eq_zero_of_isIntDiv kills_KCb h⟩
  · rintro ⟨hact, hev, hch⟩
    rw [isIntDiv_iff_five fiveStep_KCb KCb_card hloop]
    refine ⟨hact, hev, ?_⟩
    rw [charge_counts] at hch
    obtain ⟨c, hc⟩ := scalar_KCb (unorderedCount p E) (unorderedCount_swap p E)
      (counts_forbid hact) (counts_parity p E hloop hev) hch
    exact ⟨c, (latEq_counts_iff KCb p E c).mp hc⟩

set_option maxHeartbeats 4000000 in
theorem twelve_dvd_KCb {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCb p A)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiNoC p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCb) hact
  have hp := counts_parity p A hloop h3.2
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCb; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCb; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCb; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link KCb; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

theorem card_KCb : KCb.card = 5 := by unfold KCb; decide

theorem witnessBound_KCb (K : ℕ) : WitnessBoundK KCb K (5 * K) := by
  have h : WitnessBoundK KCb K (KCb.card * K) := witnessBound_of_lower KCb K lower_KCb
  rwa [card_KCb] at h

theorem KCb_budgets :
    terminalOrder 504 (5 * 504) 4 ≤ 2 ^ 21 ∧ terminalSize 504 (5 * 504) ≤ 2 ^ 21 := by
  unfold terminalOrder
    terminalSize; decide

theorem universalCert_KCb : UniversalCert KCb :=
  universalCert_of_charge_walk_kappa KCb KCb_card kappaLinks_KCb walk4_KCb chiNoC chiNoC_bound
    chargeLattice_KCb (fun p A hA hact h3 => twelve_dvd_KCb p A hA hact h3) plus_active_KCb
    minus_active_KCb plus_charge_FnoC minus_charge_FnoC _ (witnessBound_KCb 504)
    KCb_budgets.1 KCb_budgets.2

end PaddedCharge

#print axioms PaddedCharge.chargeLattice_KCa
#print axioms PaddedCharge.universalCert_KCa
#print axioms PaddedCharge.chargeLattice_KCb
#print axioms PaddedCharge.universalCert_KCb
