/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentTorsion
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# Six disconnected families with a `ℤ/3` component and an isolated `333` (census class `ℤ/9`)

`KCT1`–`KCT6`: a `KappaLinks` component on the classes `0, 1, 2` whose lattice inside the
component is "`Even3` and `ψ`-value `0` mod `3`" (`TorsionInside`), plus the isolated type `333`.
`UniversalCert` by `universalCert_of_torsion_components` (`Kappa/ComponentTorsion.lean`) with a
triangle token of value `1`. Generator: `gen_kct.py`.
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

/-- `{000 001 012 022 222 333}`. -/
noncomputable def KCT1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KCT1_card : ∀ τ ∈ KCT1, Multiset.card τ = 3 := by unfold KCT1; decide

theorem KCT1_card_eq : KCT1.card = 6 := by unfold KCT1; decide

theorem not_threeStep_KCT1 : ¬ ThreeStepLinks KCT1 := by unfold ThreeStepLinks Link KCT1; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT1 : FiveStepLinks KCT1 := by
  unfold FiveStepLinks Link KCT1; decide

def kappaKCT1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT1 := by
  refine ⟨kappaKCT1, ?_, ?_⟩ <;> unfold Link KCT1 kappaKCT1 <;> decide

theorem familyFacts_KCT1 : FamilyFacts KCT1 :=
  ⟨KCT1_card, by unfold Link KCT1; decide,
    by intro i; fin_cases i <;> (unfold Link KCT1; decide)⟩

theorem compLabel_KCT1 : CompLabel KCT1 cM3 := by
  unfold CompLabel Link KCT1 cM3; decide

theorem typesInside_KCT1 : TypesInside KCT1 cM3 := by
  unfold TypesInside KCT1 cM3; decide

theorem localWalk4_KCT1 (k : Fin 4) : LocalWalk4 KCT1 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT1 cM3; decide

theorem isolatedMono_KCT1 : IsolatedMono KCT1 3 := by unfold IsolatedMono KCT1; decide

/-- The `ℤ/3` functional of `KCT1` (upper triangular). -/
def psiKCT1 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 2, 0], ![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]

theorem psiKCT1_00 : psiKCT1 0 0 = 0 := rfl
theorem psiKCT1_01 : psiKCT1 0 1 = 0 := rfl
theorem psiKCT1_02 : psiKCT1 0 2 = 2 := rfl
theorem psiKCT1_03 : psiKCT1 0 3 = 0 := rfl
theorem psiKCT1_10 : psiKCT1 1 0 = 0 := rfl
theorem psiKCT1_11 : psiKCT1 1 1 = 0 := rfl
theorem psiKCT1_12 : psiKCT1 1 2 = 1 := rfl
theorem psiKCT1_13 : psiKCT1 1 3 = 0 := rfl
theorem psiKCT1_20 : psiKCT1 2 0 = 0 := rfl
theorem psiKCT1_21 : psiKCT1 2 1 = 0 := rfl
theorem psiKCT1_22 : psiKCT1 2 2 = 2 := rfl
theorem psiKCT1_23 : psiKCT1 2 3 = 0 := rfl
theorem psiKCT1_30 : psiKCT1 3 0 = 0 := rfl
theorem psiKCT1_31 : psiKCT1 3 1 = 0 := rfl
theorem psiKCT1_32 : psiKCT1 3 2 = 0 := rfl
theorem psiKCT1_33 : psiKCT1 3 3 = 0 := rfl

def labelKCT1 : Fin 6 → Fin 4 := ![0, 0, 2, 0, 0, 0]

theorem label_active_KCT1 : ActiveEdges KCT1 labelKCT1 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT1 : psiNum psiKCT1 labelKCT1 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT1`. -/
def canon_KCT1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 1 2) / 2), ({0,1,2}, (1 * u 1 2) / 1), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({2,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 6), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT1 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT1_00, psiKCT1_01, psiKCT1_02, psiKCT1_03, psiKCT1_10, psiKCT1_11, psiKCT1_12, psiKCT1_13, psiKCT1_20, psiKCT1_21, psiKCT1_22, psiKCT1_23, psiKCT1_30, psiKCT1_31, psiKCT1_32, psiKCT1_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT1, canon_KCT1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT1 : TorsionInside KCT1 cM3 (cM3 0) psiKCT1 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT1 KCT1_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT1 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT1 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT1 L) :
    psiVal psiKCT1 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT1 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT1 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT1, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT1_00, psiKCT1_01, psiKCT1_02, psiKCT1_03, psiKCT1_10, psiKCT1_11, psiKCT1_12, psiKCT1_13, psiKCT1_20, psiKCT1_21, psiKCT1_22, psiKCT1_23, psiKCT1_30, psiKCT1_31, psiKCT1_32, psiKCT1_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT1 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT1; decide)
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
  refine ⟨canon_KCT1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT1, canon_KCT1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT1 cM3 k :=
  even3Inside_of_scalar_five KCT1 cM3 k fiveStep_KCT1 KCT1_card (scalar_inside_KCT1 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT1 : ∀ u c0, ScalarHyp KCT1 u → LatEq KCT1 u c0 →
    ∃ c, LatEq KCT1 u c ∧ ∀ τ ∈ KCT1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT1, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT1 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT1, canon_KCT1, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT1, coeffList] <;> omega

/-- **`UniversalCert KCT1`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT1 : UniversalCert KCT1 := by
  have hB : WitnessBoundK KCT1 195 1194 := by
    rw [show (1194 : ℕ) = KCT1.card * (1 * 195 + 4) by rw [KCT1_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT1 KCT1_card 1 scalar_witness_KCT1 195
  exact universalCert_of_torsion_components KCT1 cM3 compLabel_KCT1 typesInside_KCT1 KCT1_card
    kappaLinks_KCT1 localWalk4_KCT1 even3Inside_KCT1 psiKCT1 torsionInside_KCT1
    (fun p L hin hL => psiVal_of_isIntDiv_KCT1 p L hin hL) labelKCT1 label_active_KCT1 (by decide)
    label_value_KCT1 1194 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 022 222 333}`. -/
noncomputable def KCT2 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KCT2_card : ∀ τ ∈ KCT2, Multiset.card τ = 3 := by unfold KCT2; decide

theorem KCT2_card_eq : KCT2.card = 7 := by unfold KCT2; decide

theorem not_threeStep_KCT2 : ¬ ThreeStepLinks KCT2 := by unfold ThreeStepLinks Link KCT2; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT2 : FiveStepLinks KCT2 := by
  unfold FiveStepLinks Link KCT2; decide

def kappaKCT2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT2 := by
  refine ⟨kappaKCT2, ?_, ?_⟩ <;> unfold Link KCT2 kappaKCT2 <;> decide

theorem familyFacts_KCT2 : FamilyFacts KCT2 :=
  ⟨KCT2_card, by unfold Link KCT2; decide,
    by intro i; fin_cases i <;> (unfold Link KCT2; decide)⟩

theorem compLabel_KCT2 : CompLabel KCT2 cM3 := by
  unfold CompLabel Link KCT2 cM3; decide

theorem typesInside_KCT2 : TypesInside KCT2 cM3 := by
  unfold TypesInside KCT2 cM3; decide

theorem localWalk4_KCT2 (k : Fin 4) : LocalWalk4 KCT2 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT2 cM3; decide

theorem isolatedMono_KCT2 : IsolatedMono KCT2 3 := by unfold IsolatedMono KCT2; decide

/-- The `ℤ/3` functional of `KCT2` (upper triangular). -/
def psiKCT2 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]]

theorem psiKCT2_00 : psiKCT2 0 0 = 0 := rfl
theorem psiKCT2_01 : psiKCT2 0 1 = 0 := rfl
theorem psiKCT2_02 : psiKCT2 0 2 = 1 := rfl
theorem psiKCT2_03 : psiKCT2 0 3 = 0 := rfl
theorem psiKCT2_10 : psiKCT2 1 0 = 0 := rfl
theorem psiKCT2_11 : psiKCT2 1 1 = 0 := rfl
theorem psiKCT2_12 : psiKCT2 1 2 = 2 := rfl
theorem psiKCT2_13 : psiKCT2 1 3 = 0 := rfl
theorem psiKCT2_20 : psiKCT2 2 0 = 0 := rfl
theorem psiKCT2_21 : psiKCT2 2 1 = 0 := rfl
theorem psiKCT2_22 : psiKCT2 2 2 = 1 := rfl
theorem psiKCT2_23 : psiKCT2 2 3 = 0 := rfl
theorem psiKCT2_30 : psiKCT2 3 0 = 0 := rfl
theorem psiKCT2_31 : psiKCT2 3 1 = 0 := rfl
theorem psiKCT2_32 : psiKCT2 3 2 = 0 := rfl
theorem psiKCT2_33 : psiKCT2 3 3 = 0 := rfl

def labelKCT2 : Fin 6 → Fin 4 := ![1, 1, 2, 0, 0, 0]

theorem label_active_KCT2 : ActiveEdges KCT2 labelKCT2 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT2 : psiNum psiKCT2 labelKCT2 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT2`. -/
def canon_KCT2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1 + 1 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2) / 1), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({2,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 6), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT2 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT2 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT2 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT2_00, psiKCT2_01, psiKCT2_02, psiKCT2_03, psiKCT2_10, psiKCT2_11, psiKCT2_12, psiKCT2_13, psiKCT2_20, psiKCT2_21, psiKCT2_22, psiKCT2_23, psiKCT2_30, psiKCT2_31, psiKCT2_32, psiKCT2_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT2, canon_KCT2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT2 : TorsionInside KCT2 cM3 (cM3 0) psiKCT2 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT2 KCT2_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT2 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT2 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT2 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT2 L) :
    psiVal psiKCT2 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT2 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT2 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e11 := h 1 1
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT2, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT2_00, psiKCT2_01, psiKCT2_02, psiKCT2_03, psiKCT2_10, psiKCT2_11, psiKCT2_12, psiKCT2_13, psiKCT2_20, psiKCT2_21, psiKCT2_22, psiKCT2_23, psiKCT2_30, psiKCT2_31, psiKCT2_32, psiKCT2_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT2 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT2 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT2; decide)
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
  refine ⟨canon_KCT2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT2, canon_KCT2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT2 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT2 cM3 k :=
  even3Inside_of_scalar_five KCT2 cM3 k fiveStep_KCT2 KCT2_card (scalar_inside_KCT2 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT2 : ∀ u c0, ScalarHyp KCT2 u → LatEq KCT2 u c0 →
    ∃ c, LatEq KCT2 u c ∧ ∀ τ ∈ KCT2, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT2, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT2 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT2, canon_KCT2, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT2, coeffList] <;> omega

/-- **`UniversalCert KCT2`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT2 : UniversalCert KCT2 := by
  have hB : WitnessBoundK KCT2 195 1393 := by
    rw [show (1393 : ℕ) = KCT2.card * (1 * 195 + 4) by rw [KCT2_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT2 KCT2_card 1 scalar_witness_KCT2 195
  exact universalCert_of_torsion_components KCT2 cM3 compLabel_KCT2 typesInside_KCT2 KCT2_card
    kappaLinks_KCT2 localWalk4_KCT2 even3Inside_KCT2 psiKCT2 torsionInside_KCT2
    (fun p L hin hL => psiVal_of_isIntDiv_KCT2 p L hin hL) labelKCT2 label_active_KCT2 (by decide)
    label_value_KCT2 1393 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 012 122 222 333}`. -/
noncomputable def KCT3 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KCT3_card : ∀ τ ∈ KCT3, Multiset.card τ = 3 := by unfold KCT3; decide

theorem KCT3_card_eq : KCT3.card = 6 := by unfold KCT3; decide

theorem not_threeStep_KCT3 : ¬ ThreeStepLinks KCT3 := by unfold ThreeStepLinks Link KCT3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT3 : FiveStepLinks KCT3 := by
  unfold FiveStepLinks Link KCT3; decide

def kappaKCT3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 2, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT3 := by
  refine ⟨kappaKCT3, ?_, ?_⟩ <;> unfold Link KCT3 kappaKCT3 <;> decide

theorem familyFacts_KCT3 : FamilyFacts KCT3 :=
  ⟨KCT3_card, by unfold Link KCT3; decide,
    by intro i; fin_cases i <;> (unfold Link KCT3; decide)⟩

theorem compLabel_KCT3 : CompLabel KCT3 cM3 := by
  unfold CompLabel Link KCT3 cM3; decide

theorem typesInside_KCT3 : TypesInside KCT3 cM3 := by
  unfold TypesInside KCT3 cM3; decide

theorem localWalk4_KCT3 (k : Fin 4) : LocalWalk4 KCT3 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT3 cM3; decide

theorem isolatedMono_KCT3 : IsolatedMono KCT3 3 := by unfold IsolatedMono KCT3; decide

/-- The `ℤ/3` functional of `KCT3` (upper triangular). -/
def psiKCT3 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]

theorem psiKCT3_00 : psiKCT3 0 0 = 0 := rfl
theorem psiKCT3_01 : psiKCT3 0 1 = 0 := rfl
theorem psiKCT3_02 : psiKCT3 0 2 = 1 := rfl
theorem psiKCT3_03 : psiKCT3 0 3 = 0 := rfl
theorem psiKCT3_10 : psiKCT3 1 0 = 0 := rfl
theorem psiKCT3_11 : psiKCT3 1 1 = 0 := rfl
theorem psiKCT3_12 : psiKCT3 1 2 = 2 := rfl
theorem psiKCT3_13 : psiKCT3 1 3 = 0 := rfl
theorem psiKCT3_20 : psiKCT3 2 0 = 0 := rfl
theorem psiKCT3_21 : psiKCT3 2 1 = 0 := rfl
theorem psiKCT3_22 : psiKCT3 2 2 = 2 := rfl
theorem psiKCT3_23 : psiKCT3 2 3 = 0 := rfl
theorem psiKCT3_30 : psiKCT3 3 0 = 0 := rfl
theorem psiKCT3_31 : psiKCT3 3 1 = 0 := rfl
theorem psiKCT3_32 : psiKCT3 3 2 = 0 := rfl
theorem psiKCT3_33 : psiKCT3 3 3 = 0 := rfl

def labelKCT3 : Fin 6 → Fin 4 := ![0, 2, 2, 0, 0, 0]

theorem label_active_KCT3 : ActiveEdges KCT3 labelKCT3 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT3 : psiNum psiKCT3 labelKCT3 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT3`. -/
def canon_KCT3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,2,2}, (-1 * u 0 2 + 1 * u 1 2) / 2), ({2,2,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 6), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT3 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT3 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT3 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT3; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT3_00, psiKCT3_01, psiKCT3_02, psiKCT3_03, psiKCT3_10, psiKCT3_11, psiKCT3_12, psiKCT3_13, psiKCT3_20, psiKCT3_21, psiKCT3_22, psiKCT3_23, psiKCT3_30, psiKCT3_31, psiKCT3_32, psiKCT3_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT3, canon_KCT3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT3 : TorsionInside KCT3 cM3 (cM3 0) psiKCT3 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT3 KCT3_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT3 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT3 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT3 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT3 L) :
    psiVal psiKCT3 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT3 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT3 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT3, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT3_00, psiKCT3_01, psiKCT3_02, psiKCT3_03, psiKCT3_10, psiKCT3_11, psiKCT3_12, psiKCT3_13, psiKCT3_20, psiKCT3_21, psiKCT3_22, psiKCT3_23, psiKCT3_30, psiKCT3_31, psiKCT3_32, psiKCT3_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT3 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT3 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT3; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT3; decide)
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
  refine ⟨canon_KCT3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT3, canon_KCT3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT3 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT3 cM3 k :=
  even3Inside_of_scalar_five KCT3 cM3 k fiveStep_KCT3 KCT3_card (scalar_inside_KCT3 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT3 : ∀ u c0, ScalarHyp KCT3 u → LatEq KCT3 u c0 →
    ∃ c, LatEq KCT3 u c ∧ ∀ τ ∈ KCT3, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT3; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KCT3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT3, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT3, canon_KCT3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT3, coeffList] <;> omega

/-- **`UniversalCert KCT3`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT3 : UniversalCert KCT3 := by
  have hB : WitnessBoundK KCT3 195 1194 := by
    rw [show (1194 : ℕ) = KCT3.card * (1 * 195 + 4) by rw [KCT3_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT3 KCT3_card 1 scalar_witness_KCT3 195
  exact universalCert_of_torsion_components KCT3 cM3 compLabel_KCT3 typesInside_KCT3 KCT3_card
    kappaLinks_KCT3 localWalk4_KCT3 even3Inside_KCT3 psiKCT3 torsionInside_KCT3
    (fun p L hin hL => psiVal_of_isIntDiv_KCT3 p L hin hL) labelKCT3 label_active_KCT3 (by decide)
    label_value_KCT3 1194 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 012 022 111 112 333}`. -/
noncomputable def KCT4 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {3, 3, 3}}

theorem KCT4_card : ∀ τ ∈ KCT4, Multiset.card τ = 3 := by unfold KCT4; decide

theorem KCT4_card_eq : KCT4.card = 7 := by unfold KCT4; decide

theorem not_threeStep_KCT4 : ¬ ThreeStepLinks KCT4 := by unfold ThreeStepLinks Link KCT4; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT4 : FiveStepLinks KCT4 := by
  unfold FiveStepLinks Link KCT4; decide

def kappaKCT4 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT4 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT4 := by
  refine ⟨kappaKCT4, ?_, ?_⟩ <;> unfold Link KCT4 kappaKCT4 <;> decide

theorem familyFacts_KCT4 : FamilyFacts KCT4 :=
  ⟨KCT4_card, by unfold Link KCT4; decide,
    by intro i; fin_cases i <;> (unfold Link KCT4; decide)⟩

theorem compLabel_KCT4 : CompLabel KCT4 cM3 := by
  unfold CompLabel Link KCT4 cM3; decide

theorem typesInside_KCT4 : TypesInside KCT4 cM3 := by
  unfold TypesInside KCT4 cM3; decide

theorem localWalk4_KCT4 (k : Fin 4) : LocalWalk4 KCT4 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT4 cM3; decide

theorem isolatedMono_KCT4 : IsolatedMono KCT4 3 := by unfold IsolatedMono KCT4; decide

/-- The `ℤ/3` functional of `KCT4` (upper triangular). -/
def psiKCT4 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 2, 0], ![0, 1, 1, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]

theorem psiKCT4_00 : psiKCT4 0 0 = 0 := rfl
theorem psiKCT4_01 : psiKCT4 0 1 = 0 := rfl
theorem psiKCT4_02 : psiKCT4 0 2 = 2 := rfl
theorem psiKCT4_03 : psiKCT4 0 3 = 0 := rfl
theorem psiKCT4_10 : psiKCT4 1 0 = 0 := rfl
theorem psiKCT4_11 : psiKCT4 1 1 = 1 := rfl
theorem psiKCT4_12 : psiKCT4 1 2 = 1 := rfl
theorem psiKCT4_13 : psiKCT4 1 3 = 0 := rfl
theorem psiKCT4_20 : psiKCT4 2 0 = 0 := rfl
theorem psiKCT4_21 : psiKCT4 2 1 = 0 := rfl
theorem psiKCT4_22 : psiKCT4 2 2 = 2 := rfl
theorem psiKCT4_23 : psiKCT4 2 3 = 0 := rfl
theorem psiKCT4_30 : psiKCT4 3 0 = 0 := rfl
theorem psiKCT4_31 : psiKCT4 3 1 = 0 := rfl
theorem psiKCT4_32 : psiKCT4 3 2 = 0 := rfl
theorem psiKCT4_33 : psiKCT4 3 3 = 0 := rfl

def labelKCT4 : Fin 6 → Fin 4 := ![0, 0, 2, 0, 0, 0]

theorem label_active_KCT4 : ActiveEdges KCT4 labelKCT4 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT4 : psiNum psiKCT4 labelKCT4 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT4`. -/
def canon_KCT4 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 - 2 * u 2 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2 + 2 * u 2 2) / 2), ({0,1,2}, (1 * u 0 2 - 2 * u 2 2) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,1}, (1 * u 0 2 + 2 * u 1 1 - 1 * u 1 2 - 2 * u 2 2) / 6), ({1,1,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 2), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT4 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT4 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT4 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT4 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT4; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT4_00, psiKCT4_01, psiKCT4_02, psiKCT4_03, psiKCT4_10, psiKCT4_11, psiKCT4_12, psiKCT4_13, psiKCT4_20, psiKCT4_21, psiKCT4_22, psiKCT4_23, psiKCT4_30, psiKCT4_31, psiKCT4_32, psiKCT4_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT4, canon_KCT4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT4 : TorsionInside KCT4 cM3 (cM3 0) psiKCT4 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT4 KCT4_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT4 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT4 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT4 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT4 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT4 L) :
    psiVal psiKCT4 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT4 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT4 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e11 := h 1 1
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT4, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT4_00, psiKCT4_01, psiKCT4_02, psiKCT4_03, psiKCT4_10, psiKCT4_11, psiKCT4_12, psiKCT4_13, psiKCT4_20, psiKCT4_21, psiKCT4_22, psiKCT4_23, psiKCT4_30, psiKCT4_31, psiKCT4_32, psiKCT4_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT4 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT4 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT4 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT4; decide)
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
  refine ⟨canon_KCT4 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT4, canon_KCT4, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT4 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT4 cM3 k :=
  even3Inside_of_scalar_five KCT4 cM3 k fiveStep_KCT4 KCT4_card (scalar_inside_KCT4 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT4 : ∀ u c0, ScalarHyp KCT4 u → LatEq KCT4 u c0 →
    ∃ c, LatEq KCT4 u c ∧ ∀ τ ∈ KCT4, -(((2 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT4; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT4; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT4; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT4, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT4 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT4, canon_KCT4, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT4, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT4, coeffList] <;> omega

/-- **`UniversalCert KCT4`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT4 : UniversalCert KCT4 := by
  have hB : WitnessBoundK KCT4 195 2758 := by
    rw [show (2758 : ℕ) = KCT4.card * (2 * 195 + 4) by rw [KCT4_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT4 KCT4_card 2 scalar_witness_KCT4 195
  exact universalCert_of_torsion_components KCT4 cM3 compLabel_KCT4 typesInside_KCT4 KCT4_card
    kappaLinks_KCT4 localWalk4_KCT4 even3Inside_KCT4 psiKCT4 torsionInside_KCT4
    (fun p L hin hL => psiVal_of_isIntDiv_KCT4 p L hin hL) labelKCT4 label_active_KCT4 (by decide)
    label_value_KCT4 2758 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 122 222 333}`. -/
noncomputable def KCT5 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem KCT5_card : ∀ τ ∈ KCT5, Multiset.card τ = 3 := by unfold KCT5; decide

theorem KCT5_card_eq : KCT5.card = 7 := by unfold KCT5; decide

theorem not_threeStep_KCT5 : ¬ ThreeStepLinks KCT5 := by unfold ThreeStepLinks Link KCT5; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT5 : FiveStepLinks KCT5 := by
  unfold FiveStepLinks Link KCT5; decide

def kappaKCT5 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![1, 2, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT5 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT5 := by
  refine ⟨kappaKCT5, ?_, ?_⟩ <;> unfold Link KCT5 kappaKCT5 <;> decide

theorem familyFacts_KCT5 : FamilyFacts KCT5 :=
  ⟨KCT5_card, by unfold Link KCT5; decide,
    by intro i; fin_cases i <;> (unfold Link KCT5; decide)⟩

theorem compLabel_KCT5 : CompLabel KCT5 cM3 := by
  unfold CompLabel Link KCT5 cM3; decide

theorem typesInside_KCT5 : TypesInside KCT5 cM3 := by
  unfold TypesInside KCT5 cM3; decide

theorem localWalk4_KCT5 (k : Fin 4) : LocalWalk4 KCT5 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT5 cM3; decide

theorem isolatedMono_KCT5 : IsolatedMono KCT5 3 := by unfold IsolatedMono KCT5; decide

/-- The `ℤ/3` functional of `KCT5` (upper triangular). -/
def psiKCT5 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]

theorem psiKCT5_00 : psiKCT5 0 0 = 0 := rfl
theorem psiKCT5_01 : psiKCT5 0 1 = 0 := rfl
theorem psiKCT5_02 : psiKCT5 0 2 = 1 := rfl
theorem psiKCT5_03 : psiKCT5 0 3 = 0 := rfl
theorem psiKCT5_10 : psiKCT5 1 0 = 0 := rfl
theorem psiKCT5_11 : psiKCT5 1 1 = 0 := rfl
theorem psiKCT5_12 : psiKCT5 1 2 = 2 := rfl
theorem psiKCT5_13 : psiKCT5 1 3 = 0 := rfl
theorem psiKCT5_20 : psiKCT5 2 0 = 0 := rfl
theorem psiKCT5_21 : psiKCT5 2 1 = 0 := rfl
theorem psiKCT5_22 : psiKCT5 2 2 = 2 := rfl
theorem psiKCT5_23 : psiKCT5 2 3 = 0 := rfl
theorem psiKCT5_30 : psiKCT5 3 0 = 0 := rfl
theorem psiKCT5_31 : psiKCT5 3 1 = 0 := rfl
theorem psiKCT5_32 : psiKCT5 3 2 = 0 := rfl
theorem psiKCT5_33 : psiKCT5 3 3 = 0 := rfl

def labelKCT5 : Fin 6 → Fin 4 := ![0, 2, 2, 0, 0, 0]

theorem label_active_KCT5 : ActiveEdges KCT5 labelKCT5 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT5 : psiNum psiKCT5 labelKCT5 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT5`. -/
def canon_KCT5 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 + 2 * u 1 1) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2 - 2 * u 1 1) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 0 2) / 1), ({1,2,2}, (-1 * u 0 2 + 1 * u 1 2) / 2), ({2,2,2}, (1 * u 0 2 - 1 * u 1 2 + 2 * u 2 2) / 6), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT5 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT5 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT5 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT5 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT5; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT5_00, psiKCT5_01, psiKCT5_02, psiKCT5_03, psiKCT5_10, psiKCT5_11, psiKCT5_12, psiKCT5_13, psiKCT5_20, psiKCT5_21, psiKCT5_22, psiKCT5_23, psiKCT5_30, psiKCT5_31, psiKCT5_32, psiKCT5_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT5 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT5, canon_KCT5, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT5 : TorsionInside KCT5 cM3 (cM3 0) psiKCT5 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT5 KCT5_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT5 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT5 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT5 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT5 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT5 L) :
    psiVal psiKCT5 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT5 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT5 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e11 := h 1 1
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT5, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT5_00, psiKCT5_01, psiKCT5_02, psiKCT5_03, psiKCT5_10, psiKCT5_11, psiKCT5_12, psiKCT5_13, psiKCT5_20, psiKCT5_21, psiKCT5_22, psiKCT5_23, psiKCT5_30, psiKCT5_31, psiKCT5_32, psiKCT5_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT5 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT5 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT5 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT5; decide)
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
  refine ⟨canon_KCT5 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT5, canon_KCT5, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT5 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT5 cM3 k :=
  even3Inside_of_scalar_five KCT5 cM3 k fiveStep_KCT5 KCT5_card (scalar_inside_KCT5 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT5 : ∀ u c0, ScalarHyp KCT5 u → LatEq KCT5 u c0 →
    ∃ c, LatEq KCT5 u c ∧ ∀ τ ∈ KCT5, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT5; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT5; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT5; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT5, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT5 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT5, canon_KCT5, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT5, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT5, coeffList] <;> omega

/-- **`UniversalCert KCT5`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT5 : UniversalCert KCT5 := by
  have hB : WitnessBoundK KCT5 195 1393 := by
    rw [show (1393 : ℕ) = KCT5.card * (1 * 195 + 4) by rw [KCT5_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT5 KCT5_card 1 scalar_witness_KCT5 195
  exact universalCert_of_torsion_components KCT5 cM3 compLabel_KCT5 typesInside_KCT5 KCT5_card
    kappaLinks_KCT5 localWalk4_KCT5 even3Inside_KCT5 psiKCT5 torsionInside_KCT5
    (fun p L hin hL => psiVal_of_isIntDiv_KCT5 p L hin hL) labelKCT5 label_active_KCT5 (by decide)
    label_value_KCT5 1393 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{000 001 011 012 022 111 222 333}`. -/
noncomputable def KCT6 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem KCT6_card : ∀ τ ∈ KCT6, Multiset.card τ = 3 := by unfold KCT6; decide

theorem KCT6_card_eq : KCT6.card = 8 := by unfold KCT6; decide

theorem not_threeStep_KCT6 : ¬ ThreeStepLinks KCT6 := by unfold ThreeStepLinks Link KCT6; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCT6 : FiveStepLinks KCT6 := by
  unfold FiveStepLinks Link KCT6; decide

def kappaKCT6 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCT6 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCT6 := by
  refine ⟨kappaKCT6, ?_, ?_⟩ <;> unfold Link KCT6 kappaKCT6 <;> decide

theorem familyFacts_KCT6 : FamilyFacts KCT6 :=
  ⟨KCT6_card, by unfold Link KCT6; decide,
    by intro i; fin_cases i <;> (unfold Link KCT6; decide)⟩

theorem compLabel_KCT6 : CompLabel KCT6 cM3 := by
  unfold CompLabel Link KCT6 cM3; decide

theorem typesInside_KCT6 : TypesInside KCT6 cM3 := by
  unfold TypesInside KCT6 cM3; decide

theorem localWalk4_KCT6 (k : Fin 4) : LocalWalk4 KCT6 cM3 k := by
  revert k; unfold LocalWalk4 Link KCT6 cM3; decide

theorem isolatedMono_KCT6 : IsolatedMono KCT6 3 := by unfold IsolatedMono KCT6; decide

/-- The `ℤ/3` functional of `KCT6` (upper triangular). -/
def psiKCT6 : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]]

theorem psiKCT6_00 : psiKCT6 0 0 = 0 := rfl
theorem psiKCT6_01 : psiKCT6 0 1 = 0 := rfl
theorem psiKCT6_02 : psiKCT6 0 2 = 1 := rfl
theorem psiKCT6_03 : psiKCT6 0 3 = 0 := rfl
theorem psiKCT6_10 : psiKCT6 1 0 = 0 := rfl
theorem psiKCT6_11 : psiKCT6 1 1 = 0 := rfl
theorem psiKCT6_12 : psiKCT6 1 2 = 2 := rfl
theorem psiKCT6_13 : psiKCT6 1 3 = 0 := rfl
theorem psiKCT6_20 : psiKCT6 2 0 = 0 := rfl
theorem psiKCT6_21 : psiKCT6 2 1 = 0 := rfl
theorem psiKCT6_22 : psiKCT6 2 2 = 1 := rfl
theorem psiKCT6_23 : psiKCT6 2 3 = 0 := rfl
theorem psiKCT6_30 : psiKCT6 3 0 = 0 := rfl
theorem psiKCT6_31 : psiKCT6 3 1 = 0 := rfl
theorem psiKCT6_32 : psiKCT6 3 2 = 0 := rfl
theorem psiKCT6_33 : psiKCT6 3 3 = 0 := rfl

def labelKCT6 : Fin 6 → Fin 4 := ![1, 1, 2, 0, 0, 0]

theorem label_active_KCT6 : ActiveEdges KCT6 labelKCT6 triangleSlots := by
  unfold ActiveEdges Link; decide
theorem label_value_KCT6 : psiNum psiKCT6 labelKCT6 triangleSlots % 3 = 1 := by decide

/-- The canonical integral witness for `KCT6`. -/
def canon_KCT6 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 2 * u 1 1 + 1 * u 1 2) / 6), ({0,0,1}, (1 * u 0 1 - 2 * u 1 1 - 1 * u 1 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (1 * u 1 2) / 1), ({0,2,2}, (1 * u 0 2 - 1 * u 1 2) / 2), ({2,2,2}, (-1 * u 0 2 + 1 * u 1 2 + 2 * u 2 2) / 6), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_torsion_KCT6 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCT6 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j) (h3 : (3 : ℤ) ∣ totalU u)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKCT6 i j * u i j)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCT6 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT6; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT6; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  simp only [Fin.sum_univ_four, psiKCT6_00, psiKCT6_01, psiKCT6_02, psiKCT6_03, psiKCT6_10, psiKCT6_11, psiKCT6_12, psiKCT6_13, psiKCT6_20, psiKCT6_21, psiKCT6_22, psiKCT6_23, psiKCT6_30, psiKCT6_31, psiKCT6_32, psiKCT6_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCT6 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT6, canon_KCT6, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem torsionInside_KCT6 : TorsionInside KCT6 cM3 (cM3 0) psiKCT6 := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KCT6 KCT6_card hg.1]
  refine ⟨hg.2.1, hg.2.2.1, ?_⟩
  have hψ : (3 : ℤ) ∣ psiNum psiKCT6 p E := by unfold psiVal at hv; omega
  unfold psiNum at hψ
  obtain ⟨c, hc⟩ := scalar_torsion_KCT6 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.2.1) (counts_parity p E hg.1 hg.2.2.1)
    (by rw [totalU_counts]; exact_mod_cast hg.2.2.2.1) hψ (countsInside_of_insideE hg.2.2.2.2)
  exact ⟨c, (latEq_counts_iff KCT6 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem psiVal_of_isIntDiv_KCT6 {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cM3 (cM3 0) e) (hL : IsIntDiv p KCT6 L) :
    psiVal psiKCT6 p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KCT6 p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKCT6 p L := by
    unfold psiNum
    generalize unorderedCount p L = u at h hs ⊢
    have e00 := h 0 0
    have e01 := h 0 1
    have e02 := h 0 2
    have e11 := h 1 1
    have e12 := h 1 2
    have e22 := h 2 2
    have e33 := h 3 3
    simp (config := {decide := true}) [KCT6, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
    simp only [Fin.sum_univ_four, psiKCT6_00, psiKCT6_01, psiKCT6_02, psiKCT6_03, psiKCT6_10, psiKCT6_11, psiKCT6_12, psiKCT6_13, psiKCT6_20, psiKCT6_21, psiKCT6_22, psiKCT6_23, psiKCT6_30, psiKCT6_31, psiKCT6_32, psiKCT6_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCT6 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCT6 u →
    CountsInside cM3 k u → ∃ w, LatEq KCT6 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT6; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT6; decide)
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
  refine ⟨canon_KCT6 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCT6, canon_KCT6, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCT6 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCT6 cM3 k :=
  even3Inside_of_scalar_five KCT6 cM3 k fiveStep_KCT6 KCT6_card (scalar_inside_KCT6 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCT6 : ∀ u c0, ScalarHyp KCT6 u → LatEq KCT6 u c0 →
    ∃ c, LatEq KCT6 u c ∧ ∀ τ ∈ KCT6, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCT6; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCT6; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCT6; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCT6, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCT6 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCT6, canon_KCT6, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCT6, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCT6, coeffList] <;> omega

/-- **`UniversalCert KCT6`** (`ℤ/3` component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCT6 : UniversalCert KCT6 := by
  have hB : WitnessBoundK KCT6 195 1592 := by
    rw [show (1592 : ℕ) = KCT6.card * (1 * 195 + 4) by rw [KCT6_card_eq]]
    exact witnessBound_of_latEq_lowerK KCT6 KCT6_card 1 scalar_witness_KCT6 195
  exact universalCert_of_torsion_components KCT6 cM3 compLabel_KCT6 typesInside_KCT6 KCT6_card
    kappaLinks_KCT6 localWalk4_KCT6 even3Inside_KCT6 psiKCT6 torsionInside_KCT6
    (fun p L hin hL => psiVal_of_isIntDiv_KCT6 p L hin hL) labelKCT6 label_active_KCT6 (by decide)
    label_value_KCT6 1592 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KCT1
#print axioms PaddedComponents.universalCert_KCT2
#print axioms PaddedComponents.universalCert_KCT3
#print axioms PaddedComponents.universalCert_KCT4
#print axioms PaddedComponents.universalCert_KCT5
#print axioms PaddedComponents.universalCert_KCT6
