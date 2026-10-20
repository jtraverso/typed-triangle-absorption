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

/-- `{000 001 012 123 133 233}`. -/
noncomputable def KCX4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {2, 3, 3}}

theorem KCX4_card : ∀ τ ∈ KCX4, Multiset.card τ = 3 := by unfold KCX4; decide

theorem KCX4_card_eq : KCX4.card = 6 := by unfold KCX4; decide

theorem not_threeStep_KCX4 : ¬ ThreeStepLinks KCX4 := by unfold ThreeStepLinks Link KCX4; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCX4 : FiveStepLinks KCX4 := by
  unfold FiveStepLinks Link KCX4; decide

def kappaKCX4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 2], ![1, 3, 0, 1], ![0, 2, 1, 1]]

theorem kappaLinks_KCX4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCX4 := by
  refine ⟨kappaKCX4, ?_, ?_⟩ <;> unfold Link KCX4 kappaKCX4 <;> decide

theorem familyFacts_KCX4 : FamilyFacts KCX4 :=
  ⟨KCX4_card, by unfold Link KCX4; decide,
    by intro i; fin_cases i <;> (unfold Link KCX4; decide)⟩

theorem compLabel_KCX4 : CompLabel KCX4 cAll := by
  unfold CompLabel Link KCX4 cAll; decide

theorem typesInside_KCX4 : TypesInside KCX4 cAll := by
  unfold TypesInside KCX4 cAll; decide

theorem localWalk4_KCX4 (k : Fin 4) : LocalWalk4 KCX4 cAll k := by
  revert k; unfold LocalWalk4 Link KCX4 cAll; decide


def chiKCX4 : Fin 4 → Fin 4 → ℤ := ![![0, 0, -2, 0], ![0, 0, 2, -1], ![-2, 2, 0, -1], ![0, -1, -1, 2]]

theorem chiKCX4_bound : ∀ i j, |chiKCX4 i j| ≤ 2 := by decide
theorem chiKCX4_00 : chiKCX4 0 0 = 0 := rfl
theorem chiKCX4_01 : chiKCX4 0 1 = 0 := rfl
theorem chiKCX4_02 : chiKCX4 0 2 = -2 := rfl
theorem chiKCX4_03 : chiKCX4 0 3 = 0 := rfl
theorem chiKCX4_10 : chiKCX4 1 0 = 0 := rfl
theorem chiKCX4_11 : chiKCX4 1 1 = 0 := rfl
theorem chiKCX4_12 : chiKCX4 1 2 = 2 := rfl
theorem chiKCX4_13 : chiKCX4 1 3 = -1 := rfl
theorem chiKCX4_20 : chiKCX4 2 0 = -2 := rfl
theorem chiKCX4_21 : chiKCX4 2 1 = 2 := rfl
theorem chiKCX4_22 : chiKCX4 2 2 = 0 := rfl
theorem chiKCX4_23 : chiKCX4 2 3 = -1 := rfl
theorem chiKCX4_30 : chiKCX4 3 0 = 0 := rfl
theorem chiKCX4_31 : chiKCX4 3 1 = -1 := rfl
theorem chiKCX4_32 : chiKCX4 3 2 = -1 := rfl
theorem chiKCX4_33 : chiKCX4 3 3 = 2 := rfl

theorem kills_KCX4 : Kills chiKCX4 KCX4 := by
  unfold Kills pair KCX4 chiKCX4; decide

def TpKCX4 : Template KCX4 cAll (cAll 0) where
  E := cycleSlots
  L := ![0, 1, 2, 1, 3, 1]
  loop := cycleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := cycleSlots_even
  card := cycleSlots_card.le
  inside := by decide

def TmKCX4 : Template KCX4 cAll (cAll 0) where
  E := cycleSlots
  L := ![0, 0, 0, 1, 3, 1]
  loop := cycleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := cycleSlots_even
  card := cycleSlots_card.le
  inside := by decide

def TqKCX4 : Template KCX4 cAll (cAll 0) where
  E := quadSlots
  L := ![0, 0, 0, 0, 0, 0]
  loop := by unfold quadSlots; decide
  act := by unfold ActiveEdges Link quadSlots; decide
  even := by unfold quadSlots; decide
  card := by unfold quadSlots; decide
  inside := by decide

theorem tp_charge_KCX4 : charge chiKCX4 TpKCX4.L TpKCX4.E = 4 := by decide
theorem tm_charge_KCX4 : charge chiKCX4 TmKCX4.L TmKCX4.E = -4 := by decide
theorem tq_charge_KCX4 : charge chiKCX4 TqKCX4.L TqKCX4.E = 0 := by decide
theorem tq_value_KCX4 : psiNum psiOne TqKCX4.L TqKCX4.E % 3 = 1 := by decide

def canon_KCX4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,2,3}, (1 * u 1 3 + 1 * u 2 3 - 2 * u 3 3) / 2), ({1,3,3}, (1 * u 1 3 - 1 * u 2 3 + 2 * u 3 3) / 4), ({2,3,3}, (-1 * u 1 3 + 1 * u 2 3 + 2 * u 3 3) / 4)]

set_option maxHeartbeats 16000000 in
theorem scalar_ct_KCX4 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCX4 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCX4 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiOne i j * u i j)
    (hin : CountsInside cAll 0 u) : ∃ c, LatEq KCX4 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX4; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCX4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX4; decide)
  have p0 := hp 0
  have p1 := hp 1
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1
  simp only [Fin.sum_univ_four, chiKCX4_00, chiKCX4_01, chiKCX4_02, chiKCX4_03, chiKCX4_10, chiKCX4_11, chiKCX4_12, chiKCX4_13, chiKCX4_20, chiKCX4_21, chiKCX4_22, chiKCX4_23, chiKCX4_30, chiKCX4_31, chiKCX4_32, chiKCX4_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  obtain ⟨p, hp0⟩ := p0
  obtain ⟨q, hp1⟩ := p1
  obtain ⟨t, ht⟩ := hψ
  refine ⟨coeffList [
    ({0,0,0}, t - u 1 2 - u 3 3 - (p - u 0 2)),
    ({0,0,1}, p - u 0 2),
    ({0,1,2}, u 0 2),
    ({1,2,3}, u 1 2 - u 0 2),
    ({1,3,3}, q - (p - u 0 2) - u 1 2),
    ({2,3,3}, u 3 3 - (q - (p - u 0 2) - u 1 2))], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCX4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeTorsionInside_KCX4 : ChargeTorsionInside KCX4 cAll (cAll 0) chiKCX4 psiOne := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCX4 KCX4_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hch := hg.2.2.2.1
  rw [charge_counts] at hch
  have hψ : (3 : ℤ) ∣ psiNum psiOne p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_ct_KCX4 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1) hch hψ
    (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCX4 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCX4 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cAll (cAll 0) e) (hL : IsIntDiv p KCX4 L) :
    psiVal psiOne p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCX4 p L c).mpr hc
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
    simp (config := {decide := true}) [KCX4, typeEdgeVec, sum_insert] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_KCX4 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCX4 p A)
    (hin : ∀ e ∈ A, InsideE p cAll (cAll 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKCX4 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCX4) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX4; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCX4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX4; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX4_00, chiKCX4_01, chiKCX4_02, chiKCX4_03, chiKCX4_10, chiKCX4_11, chiKCX4_12, chiKCX4_13, chiKCX4_20, chiKCX4_21, chiKCX4_22, chiKCX4_23, chiKCX4_30, chiKCX4_31, chiKCX4_32, chiKCX4_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCX4 (k : Fin 4) (hk : k ≠ cAll 0) : ∀ u, ScalarHyp KCX4 u →
    CountsInside cAll k u → ∃ w, LatEq KCX4 u w := by
  intro u _hu hin
  refine ⟨0, ?_⟩
  intro i j
  have hi : cAll i = cAll 0 := by fin_cases i <;> rfl
  have hz : u i j = 0 :=
    hin i j (Or.inl (by rw [hi]; exact Ne.symm hk))
  simp [hz]

theorem even3Inside_KCX4 (k : Fin 4) (hk : k ≠ cAll 0) : Even3Inside KCX4 cAll k :=
  even3Inside_of_scalar_five KCX4 cAll k fiveStep_KCX4 KCX4_card (scalar_inside_KCX4 k hk)

/-- Per-type lower bounds of the canonical witness. -/
def aKCX4 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,0} then 1 else if τ = {0,0,1} then 1 else if τ = {1,2,3} then 1 else if τ = {1,3,3} then 1 else if τ = {2,3,3} then 1 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCX4 : ∀ u c0, ScalarHyp KCX4 u → LatEq KCX4 u c0 →
    ∃ c, LatEq KCX4 u c ∧ ∀ τ ∈ KCX4, -((aKCX4 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX4; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCX4; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e13 := hc0 1 3
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCX4, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e13 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨c0, hc0, ?_⟩
  unfold totalU
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
  intro τ hτ
  simp only [KCX4, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [aKCX4] <;> omega

theorem wb_KCX4 : WitnessBoundK KCX4 1230 6174 := by
  have h : WitnessBoundK KCX4 1230 (∑ τ ∈ KCX4, (aKCX4 τ * 1230 + 4)) :=
    witnessBound_of_latEq_lowerA KCX4 KCX4_card aKCX4 scalar_witness_KCX4 1230
  have hv : ∑ τ ∈ KCX4, (aKCX4 τ * 1230 + 4) = 6174 := by unfold KCX4 aKCX4; decide
  rwa [hv] at h

/-- **`UniversalCert KCX4`**. -/
theorem universalCert_KCX4 : UniversalCert KCX4 :=
  universalCert_of_ct_components KCX4 cAll compLabel_KCX4 typesInside_KCX4 KCX4_card
    kappaLinks_KCX4 localWalk4_KCX4 even3Inside_KCX4 chiKCX4 psiOne chiKCX4_bound kills_KCX4
    chargeTorsionInside_KCX4 (fun p L hin hL => psiVal_of_isIntDiv_KCX4 p L hin hL)
    (fun p A hA hact hin h3 => four_dvd_KCX4 p A hA hact hin h3) TpKCX4 TmKCX4 TqKCX4
    tp_charge_KCX4 tm_charge_KCX4 tq_charge_KCX4 tq_value_KCX4 6174 wb_KCX4
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KCX4
