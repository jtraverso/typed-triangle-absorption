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

/-- `{000 001 012 112 122 333}`. -/
noncomputable def KCX2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KCX2_card : ∀ τ ∈ KCX2, Multiset.card τ = 3 := by unfold KCX2; decide

theorem KCX2_card_eq : KCX2.card = 6 := by unfold KCX2; decide

theorem not_threeStep_KCX2 : ¬ ThreeStepLinks KCX2 := by unfold ThreeStepLinks Link KCX2; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCX2 : FiveStepLinks KCX2 := by
  unfold FiveStepLinks Link KCX2; decide

def kappaKCX2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 2, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCX2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCX2 := by
  refine ⟨kappaKCX2, ?_, ?_⟩ <;> unfold Link KCX2 kappaKCX2 <;> decide

theorem familyFacts_KCX2 : FamilyFacts KCX2 :=
  ⟨KCX2_card, by unfold Link KCX2; decide,
    by intro i; fin_cases i <;> (unfold Link KCX2; decide)⟩

theorem compLabel_KCX2 : CompLabel KCX2 cM3 := by
  unfold CompLabel Link KCX2 cM3; decide

theorem typesInside_KCX2 : TypesInside KCX2 cM3 := by
  unfold TypesInside KCX2 cM3; decide

theorem localWalk4_KCX2 (k : Fin 4) : LocalWalk4 KCX2 cM3 k := by
  revert k; unfold LocalWalk4 Link KCX2 cM3; decide

theorem isolatedMono_KCX2 : IsolatedMono KCX2 3 := by unfold IsolatedMono KCX2; decide

def chiKCX2 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 2, -1, 0], ![1, -1, 2, 0], ![0, 0, 0, 0]]

theorem chiKCX2_bound : ∀ i j, |chiKCX2 i j| ≤ 2 := by decide
theorem chiKCX2_00 : chiKCX2 0 0 = 0 := rfl
theorem chiKCX2_01 : chiKCX2 0 1 = 0 := rfl
theorem chiKCX2_02 : chiKCX2 0 2 = 1 := rfl
theorem chiKCX2_03 : chiKCX2 0 3 = 0 := rfl
theorem chiKCX2_10 : chiKCX2 1 0 = 0 := rfl
theorem chiKCX2_11 : chiKCX2 1 1 = 2 := rfl
theorem chiKCX2_12 : chiKCX2 1 2 = -1 := rfl
theorem chiKCX2_13 : chiKCX2 1 3 = 0 := rfl
theorem chiKCX2_20 : chiKCX2 2 0 = 1 := rfl
theorem chiKCX2_21 : chiKCX2 2 1 = -1 := rfl
theorem chiKCX2_22 : chiKCX2 2 2 = 2 := rfl
theorem chiKCX2_23 : chiKCX2 2 3 = 0 := rfl
theorem chiKCX2_30 : chiKCX2 3 0 = 0 := rfl
theorem chiKCX2_31 : chiKCX2 3 1 = 0 := rfl
theorem chiKCX2_32 : chiKCX2 3 2 = 0 := rfl
theorem chiKCX2_33 : chiKCX2 3 3 = 0 := rfl

theorem kills_KCX2 : Kills chiKCX2 KCX2 := by
  unfold Kills pair KCX2 chiKCX2; decide

def TpKCX2 : Template KCX2 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide

def TmKCX2 : Template KCX2 cM3 (cM3 0) where
  E := cycleSlots
  L := ![0, 0, 0, 1, 2, 1]
  loop := cycleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := cycleSlots_even
  card := cycleSlots_card.le
  inside := by decide

def TqKCX2 : Template KCX2 cM3 (cM3 0) where
  E := quadSlots
  L := ![0, 0, 0, 0, 0, 0]
  loop := by unfold quadSlots; decide
  act := by unfold ActiveEdges Link quadSlots; decide
  even := by unfold quadSlots; decide
  card := by unfold quadSlots; decide
  inside := by decide

theorem tp_charge_KCX2 : charge chiKCX2 TpKCX2.L TpKCX2.E = 4 := by decide
theorem tm_charge_KCX2 : charge chiKCX2 TmKCX2.L TmKCX2.E = -4 := by decide
theorem tq_charge_KCX2 : charge chiKCX2 TqKCX2.L TqKCX2.E = 0 := by decide
theorem tq_value_KCX2 : psiNum psiOne TqKCX2.L TqKCX2.E % 3 = 1 := by decide

def canon_KCX2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,1,2}, (1 * u 1 1) / 1), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_ct_KCX2 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCX2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCX2 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiOne i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCX2 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX2_00, chiKCX2_01, chiKCX2_02, chiKCX2_03, chiKCX2_10, chiKCX2_11, chiKCX2_12, chiKCX2_13, chiKCX2_20, chiKCX2_21, chiKCX2_22, chiKCX2_23, chiKCX2_30, chiKCX2_31, chiKCX2_32, chiKCX2_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCX2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCX2, canon_KCX2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeTorsionInside_KCX2 : ChargeTorsionInside KCX2 cM3 (cM3 0) chiKCX2 psiOne := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCX2 KCX2_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hch := hg.2.2.2.1
  rw [charge_counts] at hch
  have hψ : (3 : ℤ) ∣ psiNum psiOne p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_ct_KCX2 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1) hch hψ
    (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCX2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCX2 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCX2 L) :
    psiVal psiOne p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCX2 p L c).mpr hc
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
    simp (config := {decide := true}) [KCX2, typeEdgeVec, sum_insert] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_KCX2 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCX2 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKCX2 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCX2) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX2; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX2_00, chiKCX2_01, chiKCX2_02, chiKCX2_03, chiKCX2_10, chiKCX2_11, chiKCX2_12, chiKCX2_13, chiKCX2_20, chiKCX2_21, chiKCX2_22, chiKCX2_23, chiKCX2_30, chiKCX2_31, chiKCX2_32, chiKCX2_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCX2 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCX2 u →
    CountsInside cM3 k u → ∃ w, LatEq KCX2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX2; decide)
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
  refine ⟨canon_KCX2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCX2, canon_KCX2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCX2 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCX2 cM3 k :=
  even3Inside_of_scalar_five KCX2 cM3 k fiveStep_KCX2 KCX2_card (scalar_inside_KCX2 k hk)

/-- Per-type lower bounds of the canonical witness. -/
def aKCX2 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,0} then 1 else if τ = {0,0,1} then 1 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCX2 : ∀ u c0, ScalarHyp KCX2 u → LatEq KCX2 u c0 →
    ∃ c, LatEq KCX2 u c ∧ ∀ τ ∈ KCX2, -((aKCX2 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCX2, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCX2 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCX2, canon_KCX2, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCX2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCX2, coeffList, aKCX2] <;> omega

theorem wb_KCX2 : WitnessBoundK KCX2 1230 2484 := by
  have h : WitnessBoundK KCX2 1230 (∑ τ ∈ KCX2, (aKCX2 τ * 1230 + 4)) :=
    witnessBound_of_latEq_lowerA KCX2 KCX2_card aKCX2 scalar_witness_KCX2 1230
  have hv : ∑ τ ∈ KCX2, (aKCX2 τ * 1230 + 4) = 2484 := by unfold KCX2 aKCX2; decide
  rwa [hv] at h

/-- **`UniversalCert KCX2`**. -/
theorem universalCert_KCX2 : UniversalCert KCX2 :=
  universalCert_of_ct_components KCX2 cM3 compLabel_KCX2 typesInside_KCX2 KCX2_card
    kappaLinks_KCX2 localWalk4_KCX2 even3Inside_KCX2 chiKCX2 psiOne chiKCX2_bound kills_KCX2
    chargeTorsionInside_KCX2 (fun p L hin hL => psiVal_of_isIntDiv_KCX2 p L hin hL)
    (fun p A hA hact hin h3 => four_dvd_KCX2 p A hA hact hin h3) TpKCX2 TmKCX2 TqKCX2
    tp_charge_KCX2 tm_charge_KCX2 tq_charge_KCX2 tq_value_KCX2 2484 wb_KCX2
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])


end PaddedComponents

#print axioms PaddedComponents.universalCert_KCX2
