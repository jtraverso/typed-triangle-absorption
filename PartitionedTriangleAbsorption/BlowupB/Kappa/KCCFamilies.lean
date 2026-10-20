/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentCharge
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# Three disconnected families with one charged component and an isolated `333`

`KCC1`–`KCC3`: a `KappaLinks` component on the classes `0, 1, 2` with one integral charge `χ`
(`|χ| ≤ 4`, `χ ≡ const ≢ 0 mod 3`, so charge zero forces `3 ∣ e`) and the isolated type `333`.
`UniversalCert` by `universalCert_of_charge_components` (`Kappa/ComponentCharge.lean`). Census
representatives (before relabelling): `000 112 113 122` ↦ `001 002 011 333`, `000 112 113 123 223` ↦ `001 002 012 112 333`, `000 112 113 122 123 233` ↦ `001 002 011 012 122 333`. Generator: `gen_kcc.py`.
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

/-- `{001 002 011 333}`. -/
noncomputable def KCC1 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {3, 3, 3}}

theorem KCC1_card : ∀ τ ∈ KCC1, Multiset.card τ = 3 := by unfold KCC1; decide

theorem KCC1_card_eq : KCC1.card = 4 := by unfold KCC1; decide

theorem not_threeStep_KCC1 : ¬ ThreeStepLinks KCC1 := by unfold ThreeStepLinks Link KCC1; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCC1 : FiveStepLinks KCC1 := by
  unfold FiveStepLinks Link KCC1; decide

def kappaKCC1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCC1 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCC1 := by
  refine ⟨kappaKCC1, ?_, ?_⟩ <;> unfold Link KCC1 kappaKCC1 <;> decide

theorem familyFacts_KCC1 : FamilyFacts KCC1 :=
  ⟨KCC1_card, by unfold Link KCC1; decide,
    by intro i; fin_cases i <;> (unfold Link KCC1; decide)⟩

theorem compLabel_KCC1 : CompLabel KCC1 cM3 := by
  unfold CompLabel Link KCC1 cM3; decide

theorem typesInside_KCC1 : TypesInside KCC1 cM3 := by
  unfold TypesInside KCC1 cM3; decide

theorem localWalk4_KCC1 (k : Fin 4) : LocalWalk4 KCC1 cM3 k := by
  revert k; unfold LocalWalk4 Link KCC1 cM3; decide

theorem isolatedMono_KCC1 : IsolatedMono KCC1 3 := by unfold IsolatedMono KCC1; decide

/-- The charge of `KCC1`. -/
def chiKCC1 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0]]

theorem chiKCC1_bound : ∀ i j, |chiKCC1 i j| ≤ 4 := by decide

theorem chiKCC1_00 : chiKCC1 0 0 = 2 := rfl
theorem chiKCC1_01 : chiKCC1 0 1 = -1 := rfl
theorem chiKCC1_02 : chiKCC1 0 2 = -1 := rfl
theorem chiKCC1_03 : chiKCC1 0 3 = 0 := rfl
theorem chiKCC1_10 : chiKCC1 1 0 = -1 := rfl
theorem chiKCC1_11 : chiKCC1 1 1 = 2 := rfl
theorem chiKCC1_12 : chiKCC1 1 2 = 0 := rfl
theorem chiKCC1_13 : chiKCC1 1 3 = 0 := rfl
theorem chiKCC1_20 : chiKCC1 2 0 = -1 := rfl
theorem chiKCC1_21 : chiKCC1 2 1 = 0 := rfl
theorem chiKCC1_22 : chiKCC1 2 2 = 0 := rfl
theorem chiKCC1_23 : chiKCC1 2 3 = 0 := rfl
theorem chiKCC1_30 : chiKCC1 3 0 = 0 := rfl
theorem chiKCC1_31 : chiKCC1 3 1 = 0 := rfl
theorem chiKCC1_32 : chiKCC1 3 2 = 0 := rfl
theorem chiKCC1_33 : chiKCC1 3 3 = 0 := rfl

theorem kills_KCC1 : Kills chiKCC1 KCC1 := by
  unfold Kills pair KCC1 chiKCC1; decide

theorem plus_active_KCC1 : ActiveEdges KCC1 plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_KCC1 : ActiveEdges KCC1 minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide
theorem plus_charge_KCC1 : charge chiKCC1 plusLabel triangleSlots = 12 := by decide
theorem minus_charge_KCC1 : charge chiKCC1 minusLabel cycleSlots = -12 := by decide

/-- The canonical integral witness for `KCC1`. -/
def canon_KCC1 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (2 * u 0 0 - 1 * u 0 2) / 2), ({0,0,2}, (1 * u 0 2) / 2), ({0,1,1}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KCC1 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCC1 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCC1 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCC1 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCC1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC1; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCC1_00, chiKCC1_01, chiKCC1_02, chiKCC1_03, chiKCC1_10, chiKCC1_11, chiKCC1_12, chiKCC1_13, chiKCC1_20, chiKCC1_21, chiKCC1_22, chiKCC1_23, chiKCC1_30, chiKCC1_31, chiKCC1_32, chiKCC1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCC1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC1, canon_KCC1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeInside_KCC1 : ChargeInside KCC1 cM3 (cM3 0) chiKCC1 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff_five fiveStep_KCC1 KCC1_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KCC1 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KCC1 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem twelve_dvd_KCC1 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCC1 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKCC1 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCC1) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCC1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC1; decide)
  have z33 : u 3 3 = 0 := hin' 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKCC1_00, chiKCC1_01, chiKCC1_02, chiKCC1_03, chiKCC1_10, chiKCC1_11, chiKCC1_12, chiKCC1_13, chiKCC1_20, chiKCC1_21, chiKCC1_22, chiKCC1_23, chiKCC1_30, chiKCC1_31, chiKCC1_32, chiKCC1_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCC1 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCC1 u →
    CountsInside cM3 k u → ∃ w, LatEq KCC1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCC1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC1; decide)
  have hz : u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 1 = 0 := ⟨hin 0 0 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 1 (by left; simpa [cM3] using fun h => hk h.symm), hin 0 2 (by left; simpa [cM3] using fun h => hk h.symm), hin 1 1 (by left; simpa [cM3] using fun h => hk h.symm)⟩
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCC1 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC1, canon_KCC1, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCC1 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCC1 cM3 k :=
  even3Inside_of_scalar_five KCC1 cM3 k fiveStep_KCC1 KCC1_card (scalar_inside_KCC1 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCC1 : ∀ u c0, ScalarHyp KCC1 u → LatEq KCC1 u c0 →
    ∃ c, LatEq KCC1 u c ∧ ∀ τ ∈ KCC1, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link KCC1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC1; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC1; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC1; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCC1, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCC1 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCC1, canon_KCC1, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCC1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCC1, coeffList] <;> omega

/-- **`UniversalCert KCC1`** (charged component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCC1 : UniversalCert KCC1 := by
  have hB : WitnessBoundK KCC1 840 3376 := by
    rw [show (3376 : ℕ) = KCC1.card * (1 * 840 + 4) by rw [KCC1_card_eq]]
    exact witnessBound_of_latEq_lowerK KCC1 KCC1_card 1 scalar_witness_KCC1 840
  exact universalCert_of_charge_components KCC1 cM3 compLabel_KCC1 typesInside_KCC1 KCC1_card
    kappaLinks_KCC1 localWalk4_KCC1 even3Inside_KCC1 chiKCC1 chiKCC1_bound kills_KCC1 chargeInside_KCC1
    (fun p A hA hact hin h3 => twelve_dvd_KCC1 p A hA hact hin h3) plus_active_KCC1 minus_active_KCC1
    plus_charge_KCC1 minus_charge_KCC1 (by decide) (by decide) 3376 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{001 002 012 112 333}`. -/
noncomputable def KCC2 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KCC2_card : ∀ τ ∈ KCC2, Multiset.card τ = 3 := by unfold KCC2; decide

theorem KCC2_card_eq : KCC2.card = 5 := by unfold KCC2; decide

theorem not_threeStep_KCC2 : ¬ ThreeStepLinks KCC2 := by unfold ThreeStepLinks Link KCC2; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCC2 : FiveStepLinks KCC2 := by
  unfold FiveStepLinks Link KCC2; decide

def kappaKCC2 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCC2 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCC2 := by
  refine ⟨kappaKCC2, ?_, ?_⟩ <;> unfold Link KCC2 kappaKCC2 <;> decide

theorem familyFacts_KCC2 : FamilyFacts KCC2 :=
  ⟨KCC2_card, by unfold Link KCC2; decide,
    by intro i; fin_cases i <;> (unfold Link KCC2; decide)⟩

theorem compLabel_KCC2 : CompLabel KCC2 cM3 := by
  unfold CompLabel Link KCC2 cM3; decide

theorem typesInside_KCC2 : TypesInside KCC2 cM3 := by
  unfold TypesInside KCC2 cM3; decide

theorem localWalk4_KCC2 (k : Fin 4) : LocalWalk4 KCC2 cM3 k := by
  revert k; unfold LocalWalk4 Link KCC2 cM3; decide

theorem isolatedMono_KCC2 : IsolatedMono KCC2 3 := by unfold IsolatedMono KCC2; decide

/-- The charge of `KCC2`. -/
def chiKCC2 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, -4, 2, 0], ![-1, 2, 0, 0], ![0, 0, 0, 0]]

theorem chiKCC2_bound : ∀ i j, |chiKCC2 i j| ≤ 4 := by decide

theorem chiKCC2_00 : chiKCC2 0 0 = 2 := rfl
theorem chiKCC2_01 : chiKCC2 0 1 = -1 := rfl
theorem chiKCC2_02 : chiKCC2 0 2 = -1 := rfl
theorem chiKCC2_03 : chiKCC2 0 3 = 0 := rfl
theorem chiKCC2_10 : chiKCC2 1 0 = -1 := rfl
theorem chiKCC2_11 : chiKCC2 1 1 = -4 := rfl
theorem chiKCC2_12 : chiKCC2 1 2 = 2 := rfl
theorem chiKCC2_13 : chiKCC2 1 3 = 0 := rfl
theorem chiKCC2_20 : chiKCC2 2 0 = -1 := rfl
theorem chiKCC2_21 : chiKCC2 2 1 = 2 := rfl
theorem chiKCC2_22 : chiKCC2 2 2 = 0 := rfl
theorem chiKCC2_23 : chiKCC2 2 3 = 0 := rfl
theorem chiKCC2_30 : chiKCC2 3 0 = 0 := rfl
theorem chiKCC2_31 : chiKCC2 3 1 = 0 := rfl
theorem chiKCC2_32 : chiKCC2 3 2 = 0 := rfl
theorem chiKCC2_33 : chiKCC2 3 3 = 0 := rfl

theorem kills_KCC2 : Kills chiKCC2 KCC2 := by
  unfold Kills pair KCC2 chiKCC2; decide

theorem plus_active_KCC2 : ActiveEdges KCC2 plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_KCC2 : ActiveEdges KCC2 minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide
theorem plus_charge_KCC2 : charge chiKCC2 plusLabel triangleSlots = 12 := by decide
theorem minus_charge_KCC2 : charge chiKCC2 minusLabel cycleSlots = -12 := by decide

/-- The canonical integral witness for `KCC2`. -/
def canon_KCC2 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2) / 4), ({0,0,2}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 4), ({0,1,2}, (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2) / 2), ({1,1,2}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KCC2 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCC2 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCC2 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCC2 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC2; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCC2_00, chiKCC2_01, chiKCC2_02, chiKCC2_03, chiKCC2_10, chiKCC2_11, chiKCC2_12, chiKCC2_13, chiKCC2_20, chiKCC2_21, chiKCC2_22, chiKCC2_23, chiKCC2_30, chiKCC2_31, chiKCC2_32, chiKCC2_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCC2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC2, canon_KCC2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeInside_KCC2 : ChargeInside KCC2 cM3 (cM3 0) chiKCC2 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff_five fiveStep_KCC2 KCC2_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KCC2 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KCC2 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem twelve_dvd_KCC2 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCC2 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKCC2 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCC2) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC2; decide)
  have z33 : u 3 3 = 0 := hin' 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKCC2_00, chiKCC2_01, chiKCC2_02, chiKCC2_03, chiKCC2_10, chiKCC2_11, chiKCC2_12, chiKCC2_13, chiKCC2_20, chiKCC2_21, chiKCC2_22, chiKCC2_23, chiKCC2_30, chiKCC2_31, chiKCC2_32, chiKCC2_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCC2 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCC2 u →
    CountsInside cM3 k u → ∃ w, LatEq KCC2 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC2; decide)
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
  refine ⟨canon_KCC2 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC2, canon_KCC2, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCC2 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCC2 cM3 k :=
  even3Inside_of_scalar_five KCC2 cM3 k fiveStep_KCC2 KCC2_card (scalar_inside_KCC2 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCC2 : ∀ u c0, ScalarHyp KCC2 u → LatEq KCC2 u c0 →
    ∃ c, LatEq KCC2 u c ∧ ∀ τ ∈ KCC2, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC2; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC2; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KCC2; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC2; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCC2, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCC2 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCC2, canon_KCC2, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCC2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCC2, coeffList] <;> omega

/-- **`UniversalCert KCC2`** (charged component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCC2 : UniversalCert KCC2 := by
  have hB : WitnessBoundK KCC2 840 4220 := by
    rw [show (4220 : ℕ) = KCC2.card * (1 * 840 + 4) by rw [KCC2_card_eq]]
    exact witnessBound_of_latEq_lowerK KCC2 KCC2_card 1 scalar_witness_KCC2 840
  exact universalCert_of_charge_components KCC2 cM3 compLabel_KCC2 typesInside_KCC2 KCC2_card
    kappaLinks_KCC2 localWalk4_KCC2 even3Inside_KCC2 chiKCC2 chiKCC2_bound kills_KCC2 chargeInside_KCC2
    (fun p A hA hact hin h3 => twelve_dvd_KCC2 p A hA hact hin h3) plus_active_KCC2 minus_active_KCC2
    plus_charge_KCC2 minus_charge_KCC2 (by decide) (by decide) 4220 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

/-- `{001 002 011 012 122 333}`. -/
noncomputable def KCC3 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem KCC3_card : ∀ τ ∈ KCC3, Multiset.card τ = 3 := by unfold KCC3; decide

theorem KCC3_card_eq : KCC3.card = 6 := by unfold KCC3; decide

theorem not_threeStep_KCC3 : ¬ ThreeStepLinks KCC3 := by unfold ThreeStepLinks Link KCC3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KCC3 : FiveStepLinks KCC3 := by
  unfold FiveStepLinks Link KCC3; decide

def kappaKCC3 : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KCC3 : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KCC3 := by
  refine ⟨kappaKCC3, ?_, ?_⟩ <;> unfold Link KCC3 kappaKCC3 <;> decide

theorem familyFacts_KCC3 : FamilyFacts KCC3 :=
  ⟨KCC3_card, by unfold Link KCC3; decide,
    by intro i; fin_cases i <;> (unfold Link KCC3; decide)⟩

theorem compLabel_KCC3 : CompLabel KCC3 cM3 := by
  unfold CompLabel Link KCC3 cM3; decide

theorem typesInside_KCC3 : TypesInside KCC3 cM3 := by
  unfold TypesInside KCC3 cM3; decide

theorem localWalk4_KCC3 (k : Fin 4) : LocalWalk4 KCC3 cM3 k := by
  revert k; unfold LocalWalk4 Link KCC3 cM3; decide

theorem isolatedMono_KCC3 : IsolatedMono KCC3 3 := by unfold IsolatedMono KCC3; decide

/-- The charge of `KCC3`. -/
def chiKCC3 : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 2, 2, 0], ![-1, 2, -4, 0], ![0, 0, 0, 0]]

theorem chiKCC3_bound : ∀ i j, |chiKCC3 i j| ≤ 4 := by decide

theorem chiKCC3_00 : chiKCC3 0 0 = 2 := rfl
theorem chiKCC3_01 : chiKCC3 0 1 = -1 := rfl
theorem chiKCC3_02 : chiKCC3 0 2 = -1 := rfl
theorem chiKCC3_03 : chiKCC3 0 3 = 0 := rfl
theorem chiKCC3_10 : chiKCC3 1 0 = -1 := rfl
theorem chiKCC3_11 : chiKCC3 1 1 = 2 := rfl
theorem chiKCC3_12 : chiKCC3 1 2 = 2 := rfl
theorem chiKCC3_13 : chiKCC3 1 3 = 0 := rfl
theorem chiKCC3_20 : chiKCC3 2 0 = -1 := rfl
theorem chiKCC3_21 : chiKCC3 2 1 = 2 := rfl
theorem chiKCC3_22 : chiKCC3 2 2 = -4 := rfl
theorem chiKCC3_23 : chiKCC3 2 3 = 0 := rfl
theorem chiKCC3_30 : chiKCC3 3 0 = 0 := rfl
theorem chiKCC3_31 : chiKCC3 3 1 = 0 := rfl
theorem chiKCC3_32 : chiKCC3 3 2 = 0 := rfl
theorem chiKCC3_33 : chiKCC3 3 3 = 0 := rfl

theorem kills_KCC3 : Kills chiKCC3 KCC3 := by
  unfold Kills pair KCC3 chiKCC3; decide

theorem plus_active_KCC3 : ActiveEdges KCC3 plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_KCC3 : ActiveEdges KCC3 minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide
theorem plus_charge_KCC3 : charge chiKCC3 plusLabel triangleSlots = 12 := by decide
theorem minus_charge_KCC3 : charge chiKCC3 minusLabel cycleSlots = -12 := by decide

/-- The canonical integral witness for `KCC3`. -/
def canon_KCC3 (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (2 * u 0 0 + 1 * u 0 1 - 1 * u 0 2 - 2 * u 1 1) / 4), ({0,0,2}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2 + 2 * u 1 1) / 4), ({0,1,1}, (1 * u 1 1) / 1), ({0,1,2}, (-2 * u 0 0 + 1 * u 0 1 + 1 * u 0 2 - 2 * u 1 1) / 2), ({1,2,2}, (1 * u 2 2) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_charge_KCC3 (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KCC3 i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKCC3 i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KCC3 u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC3; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKCC3_00, chiKCC3_01, chiKCC3_02, chiKCC3_03, chiKCC3_10, chiKCC3_11, chiKCC3_12, chiKCC3_13, chiKCC3_20, chiKCC3_21, chiKCC3_22, chiKCC3_23, chiKCC3_30, chiKCC3_31, chiKCC3_32, chiKCC3_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KCC3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC3, canon_KCC3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeInside_KCC3 : ChargeInside KCC3 cM3 (cM3 0) chiKCC3 := by
  intro V _ _ p E hloop hact hin hev hch
  rw [isIntDiv_iff_five fiveStep_KCC3 KCC3_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch
  obtain ⟨c, hc⟩ := scalar_charge_KCC3 (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KCC3 p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem twelve_dvd_KCC3 {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KCC3 p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiKCC3 p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KCC3) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC3; decide)
  have z33 : u 3 3 = 0 := hin' 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiKCC3_00, chiKCC3_01, chiKCC3_02, chiKCC3_03, chiKCC3_10, chiKCC3_11, chiKCC3_12, chiKCC3_13, chiKCC3_20, chiKCC3_21, chiKCC3_22, chiKCC3_23, chiKCC3_30, chiKCC3_31, chiKCC3_32, chiKCC3_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KCC3 (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KCC3 u →
    CountsInside cM3 k u → ∃ w, LatEq KCC3 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC3; decide)
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
  refine ⟨canon_KCC3 u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KCC3, canon_KCC3, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KCC3 (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KCC3 cM3 k :=
  even3Inside_of_scalar_five KCC3 cM3 k fiveStep_KCC3 KCC3_card (scalar_inside_KCC3 k hk)

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KCC3 : ∀ u c0, ScalarHyp KCC3 u → LatEq KCC3 u c0 →
    ∃ c, LatEq KCC3 u c ∧ ∀ τ ∈ KCC3, -(((1 : ℕ) : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KCC3; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KCC3; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KCC3; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KCC3, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KCC3 u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KCC3, canon_KCC3, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KCC3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KCC3, coeffList] <;> omega

/-- **`UniversalCert KCC3`** (charged component, `KappaLinks` terminal absorbers). -/
theorem universalCert_KCC3 : UniversalCert KCC3 := by
  have hB : WitnessBoundK KCC3 840 5064 := by
    rw [show (5064 : ℕ) = KCC3.card * (1 * 840 + 4) by rw [KCC3_card_eq]]
    exact witnessBound_of_latEq_lowerK KCC3 KCC3_card 1 scalar_witness_KCC3 840
  exact universalCert_of_charge_components KCC3 cM3 compLabel_KCC3 typesInside_KCC3 KCC3_card
    kappaLinks_KCC3 localWalk4_KCC3 even3Inside_KCC3 chiKCC3 chiKCC3_bound kills_KCC3 chargeInside_KCC3
    (fun p A hA hact hin h3 => twelve_dvd_KCC3 p A hA hact hin h3) plus_active_KCC3 minus_active_KCC3
    plus_charge_KCC3 minus_charge_KCC3 (by decide) (by decide) 5064 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])
    (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KCC1
#print axioms PaddedComponents.universalCert_KCC2
#print axioms PaddedComponents.universalCert_KCC3
