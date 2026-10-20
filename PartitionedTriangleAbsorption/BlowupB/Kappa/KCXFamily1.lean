/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentChargeTorsion
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# Four families with one charge of unit `4` whose zero set does not force `3 ∣ e`

`KCX1`–`KCX3`: disconnected, a charged `KappaLinks` component on `0, 1, 2` and the isolated `333`;
`KCX4 = {000,001,012,123,133,233}` (the class "C1"): connected, one component. Inside the
component the lattice is "even, `χ = 0`, `e ≡ 0 mod 3`" (`ChargeTorsionInside` with `ψ` the edge
count). `UniversalCert` by `universalCert_of_ct_components` with templates of charge `±4` and a
4-cycle of charge `0`. Generator: `gen_kcx.py`.
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

/-- Component labels of a connected family: one component. -/
def cAll : Fin 4 → Fin 4 := ![0, 0, 0, 0]

/-- The four-cycle on the slots `0, 1, 2, 3`. -/
def quadSlots : Finset (Sym2 (Fin 6)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

/-- The edge count (upper triangular ones). -/
def psiOne : Fin 4 → Fin 4 → ℤ := fun i j => if i ≤ j then 1 else 0

theorem psiOne_00 : psiOne 0 0 = 1 := rfl
theorem psiOne_01 : psiOne 0 1 = 1 := rfl
theorem psiOne_02 : psiOne 0 2 = 1 := rfl
theorem psiOne_03 : psiOne 0 3 = 1 := rfl
theorem psiOne_10 : psiOne 1 0 = 0 := rfl
theorem psiOne_11 : psiOne 1 1 = 1 := rfl
theorem psiOne_12 : psiOne 1 2 = 1 := rfl
theorem psiOne_13 : psiOne 1 3 = 1 := rfl
theorem psiOne_20 : psiOne 2 0 = 0 := rfl
theorem psiOne_21 : psiOne 2 1 = 0 := rfl
theorem psiOne_22 : psiOne 2 2 = 1 := rfl
theorem psiOne_23 : psiOne 2 3 = 1 := rfl
theorem psiOne_30 : psiOne 3 0 = 0 := rfl
theorem psiOne_31 : psiOne 3 1 = 0 := rfl
theorem psiOne_32 : psiOne 3 2 = 0 := rfl
theorem psiOne_33 : psiOne 3 3 = 1 := rfl

/-- `{000 001 012 112 333}`. -/
noncomputable def KCX1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KCX1_card : ∀ τ ∈ KCX1, Multiset.card τ = 3 := by unfold KCX1; decide

theorem KCX1_card_eq : KCX1.card = 5 := by unfold KCX1; decide

theorem not_threeStep_KCX1 : ¬ ThreeStepLinks KCX1 := by unfold ThreeStepLinks Link KCX1; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCX1 : FiveStepLinks KCX1 := by
  unfold FiveStepLinks Link KCX1; decide

def kappaKCX1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCX1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCX1 := by
  refine ⟨kappaKCX1, ?_, ?_⟩ <;> unfold Link KCX1 kappaKCX1 <;> decide

theorem familyFacts_KCX1 : FamilyFacts KCX1 :=
  ⟨KCX1_card, by unfold Link KCX1; decide,
    by intro i; fin_cases i <;> (unfold Link KCX1; decide)⟩

theorem compLabel_KCX1 : CompLabel KCX1 cM3 := by
  unfold CompLabel Link KCX1 cM3; decide

theorem typesInside_KCX1 : TypesInside KCX1 cM3 := by
  unfold TypesInside KCX1 cM3; decide

theorem localWalk4_KCX1 (k : Fin 4) : LocalWalk4 KCX1 cM3 k := by
  revert k; unfold LocalWalk4 Link KCX1 cM3; decide

theorem isolatedMono_KCX1 : IsolatedMono KCX1 3 := by unfold IsolatedMono KCX1; decide

def chiKCX1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, -1, 0], ![0, -2, 1, 0], ![-1, 1, 0, 0], ![0, 0, 0, 0]]

theorem chiKCX1_bound : ∀ i j, |chiKCX1 i j| ≤ 2 := by decide
theorem chiKCX1_00 : chiKCX1 0 0 = 0 := rfl
theorem chiKCX1_01 : chiKCX1 0 1 = 0 := rfl
theorem chiKCX1_02 : chiKCX1 0 2 = -1 := rfl
theorem chiKCX1_03 : chiKCX1 0 3 = 0 := rfl
theorem chiKCX1_10 : chiKCX1 1 0 = 0 := rfl
theorem chiKCX1_11 : chiKCX1 1 1 = -2 := rfl
theorem chiKCX1_12 : chiKCX1 1 2 = 1 := rfl
theorem chiKCX1_13 : chiKCX1 1 3 = 0 := rfl
theorem chiKCX1_20 : chiKCX1 2 0 = -1 := rfl
theorem chiKCX1_21 : chiKCX1 2 1 = 1 := rfl
theorem chiKCX1_22 : chiKCX1 2 2 = 0 := rfl
theorem chiKCX1_23 : chiKCX1 2 3 = 0 := rfl
theorem chiKCX1_30 : chiKCX1 3 0 = 0 := rfl
theorem chiKCX1_31 : chiKCX1 3 1 = 0 := rfl
theorem chiKCX1_32 : chiKCX1 3 2 = 0 := rfl
theorem chiKCX1_33 : chiKCX1 3 3 = 0 := rfl

theorem kills_KCX1 : Kills chiKCX1 KCX1 := by
  unfold Kills pair KCX1 chiKCX1; decide

def TpKCX1 : Template KCX1 cM3 (cM3 0) where
  E := cycleSlots
  L := ![0, 0, 0, 1, 2, 1]
  loop := cycleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := cycleSlots_even
  card := cycleSlots_card.le
  inside := by decide

def TmKCX1 : Template KCX1 cM3 (cM3 0) where
  E := triangleSlots
  L := ![0, 0, 2, 0, 0, 0]
  loop := triangleSlots_loopless
  act := by unfold ActiveEdges Link; decide
  even := triangleSlots_even
  card := by rw [triangleSlots_card]; norm_num
  inside := by decide

def TqKCX1 : Template KCX1 cM3 (cM3 0) where
  E := quadSlots
  L := ![0, 0, 0, 0, 0, 0]
  loop := by unfold quadSlots; decide
  act := by unfold ActiveEdges Link quadSlots; decide
  even := by unfold quadSlots; decide
  card := by unfold quadSlots; decide
  inside := by decide

theorem tp_charge_KCX1 : charge chiKCX1 TpKCX1.L TpKCX1.E = 4 := by decide
theorem tm_charge_KCX1 : charge chiKCX1 TmKCX1.L TmKCX1.E = -4 := by decide
theorem tq_charge_KCX1 : charge chiKCX1 TqKCX1.L TqKCX1.E = 0 := by decide
theorem tq_value_KCX1 : psiNum psiOne TqKCX1.L TqKCX1.E % 3 = 1 := by decide

def canon_KCX1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,1,2}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_ct_KCX1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCX1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCX1 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiOne i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCX1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX1_00, chiKCX1_01, chiKCX1_02, chiKCX1_03, chiKCX1_10, chiKCX1_11, chiKCX1_12, chiKCX1_13, chiKCX1_20, chiKCX1_21, chiKCX1_22, chiKCX1_23, chiKCX1_30, chiKCX1_31, chiKCX1_32, chiKCX1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCX1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCX1, canon_KCX1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeTorsionInside_KCX1 : ChargeTorsionInside KCX1 cM3 (cM3 0) chiKCX1 psiOne := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCX1 KCX1_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hch := hg.2.2.2.1
  rw [charge_counts] at hch
  have hψ : (3 : ℤ) ∣ psiNum psiOne p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_ct_KCX1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1) hch hψ
    (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCX1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCX1 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCX1 L) :
    psiVal psiOne p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCX1 p L c).mpr hc
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
    simp (config := {decide := true}) [KCX1, typeEdgeVec, sum_insert] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_KCX1 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCX1 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKCX1 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCX1) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX1; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCX1_00, chiKCX1_01, chiKCX1_02, chiKCX1_03, chiKCX1_10, chiKCX1_11, chiKCX1_12, chiKCX1_13, chiKCX1_20, chiKCX1_21, chiKCX1_22, chiKCX1_23, chiKCX1_30, chiKCX1_31, chiKCX1_32, chiKCX1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCX1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCX1 u →
    CountsInside cM3 k u → ∃ w, LatEq KCX1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX1; decide)
  have hz : u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 ∧ u 1 2 = 0 := ⟨hin 0 0 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 2 (by left; simpa [cM3] using fun h => hk h.symm)⟩
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCX1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCX1, canon_KCX1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCX1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCX1 cM3 k :=
  even3Inside_of_scalar_five KCX1 cM3 k fiveStep_KCX1 KCX1_card (scalar_inside_KCX1 k hk)

/-- Per-type lower bounds of the canonical witness. -/
def aKCX1 : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,0} then 1 else if τ = {0,0,1} then 1 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCX1 : ∀ u c0, ScalarHyp KCX1 u → LatEq KCX1 u c0 →
    ∃ c, LatEq KCX1 u c ∧ ∀ τ ∈ KCX1, -((aKCX1 τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCX1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCX1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCX1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCX1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCX1, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCX1 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCX1, canon_KCX1, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCX1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCX1, coeffList, aKCX1] <;> omega

theorem wb_KCX1 : WitnessBoundK KCX1 1230 2480 := by
  have h : WitnessBoundK KCX1 1230 (∑ τ ∈ KCX1, (aKCX1 τ * 1230 + 4)) :=
    witnessBound_of_latEq_lowerA KCX1 KCX1_card aKCX1 scalar_witness_KCX1 1230
  have hv : ∑ τ ∈ KCX1, (aKCX1 τ * 1230 + 4) = 2480 := by unfold KCX1 aKCX1; decide
  rwa [hv] at h

/-- **`UniversalCert KCX1`**. -/
theorem universalCert_KCX1 : UniversalCert KCX1 :=
  universalCert_of_ct_components KCX1 cM3 compLabel_KCX1 typesInside_KCX1 KCX1_card
    kappaLinks_KCX1 localWalk4_KCX1 even3Inside_KCX1 chiKCX1 psiOne chiKCX1_bound kills_KCX1
    chargeTorsionInside_KCX1 (fun p L hin hL => psiVal_of_isIntDiv_KCX1 p L hin hL)
    (fun p A hA hact hin h3 => four_dvd_KCX1 p A hA hact hin h3) TpKCX1 TmKCX1 TqKCX1
    tp_charge_KCX1 tm_charge_KCX1 tq_charge_KCX1 tq_value_KCX1 2480 wb_KCX1
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])


end PaddedComponents

#print axioms PaddedComponents.universalCert_KCX1
