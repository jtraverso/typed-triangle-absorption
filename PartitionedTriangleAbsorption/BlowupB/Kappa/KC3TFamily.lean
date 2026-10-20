/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentChargeTorsion2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamilies

@[expose] public section

/-!
# `KC3T = {000,001,012,123,233,333}` (the class "C2"): a charge, `e mod 3` and a `ℤ/3` value

Connected (one component, `cAll`). The lattice is "even, `χ = 0`, `3 ∣ e`, `ψ ≡ 0 mod 3`"
(`ChargeTorsion2Inside` with `ψE = psiOne`). `UniversalCert` by `universalCert_of_ct3_components`.
Generator: `gen_c2.py`.
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

/-- `{000 001 012 123 233 333}`. -/
noncomputable def KC3T : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 2}, {1, 2, 3}, {2, 3, 3}, {3, 3, 3}}

theorem KC3T_card : ∀ τ ∈ KC3T, Multiset.card τ = 3 := by unfold KC3T; decide

theorem KC3T_card_eq : KC3T.card = 6 := by unfold KC3T; decide

theorem not_threeStep_KC3T : ¬ ThreeStepLinks KC3T := by unfold ThreeStepLinks Link KC3T; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KC3T : FiveStepLinks KC3T := by
  unfold FiveStepLinks Link KC3T; decide

def kappaKC3T : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 0, 2], ![1, 3, 0, 1], ![0, 2, 3, 2]]

theorem kappaLinks_KC3T : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KC3T := by
  refine ⟨kappaKC3T, ?_, ?_⟩ <;> unfold Link KC3T kappaKC3T <;> decide

theorem familyFacts_KC3T : FamilyFacts KC3T :=
  ⟨KC3T_card, by unfold Link KC3T; decide,
    by intro i; fin_cases i <;> (unfold Link KC3T; decide)⟩

theorem compLabel_KC3T : CompLabel KC3T cAll := by
  unfold CompLabel Link KC3T cAll; decide

theorem typesInside_KC3T : TypesInside KC3T cAll := by
  unfold TypesInside KC3T cAll; decide

theorem localWalk4_KC3T (k : Fin 4) : LocalWalk4 KC3T cAll k := by
  revert k; unfold LocalWalk4 Link KC3T cAll; decide


def chiKC3T : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 1, 0, 0]]
theorem chiKC3T_bound : ∀ i j, |chiKC3T i j| ≤ 2 := by decide
theorem chiKC3T_00 : chiKC3T 0 0 = 0 := rfl
theorem chiKC3T_01 : chiKC3T 0 1 = 0 := rfl
theorem chiKC3T_02 : chiKC3T 0 2 = 1 := rfl
theorem chiKC3T_03 : chiKC3T 0 3 = 0 := rfl
theorem chiKC3T_10 : chiKC3T 1 0 = 0 := rfl
theorem chiKC3T_11 : chiKC3T 1 1 = 0 := rfl
theorem chiKC3T_12 : chiKC3T 1 2 = -1 := rfl
theorem chiKC3T_13 : chiKC3T 1 3 = 1 := rfl
theorem chiKC3T_20 : chiKC3T 2 0 = 1 := rfl
theorem chiKC3T_21 : chiKC3T 2 1 = -1 := rfl
theorem chiKC3T_22 : chiKC3T 2 2 = 0 := rfl
theorem chiKC3T_23 : chiKC3T 2 3 = 0 := rfl
theorem chiKC3T_30 : chiKC3T 3 0 = 0 := rfl
theorem chiKC3T_31 : chiKC3T 3 1 = 1 := rfl
theorem chiKC3T_32 : chiKC3T 3 2 = 0 := rfl
theorem chiKC3T_33 : chiKC3T 3 3 = 0 := rfl
theorem kills_KC3T : Kills chiKC3T KC3T := by
  unfold Kills pair KC3T chiKC3T; decide

def psiKC3T : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2], ![0, 0, 0, 2]]
theorem psiKC3T_00 : psiKC3T 0 0 = 0 := rfl
theorem psiKC3T_01 : psiKC3T 0 1 = 0 := rfl
theorem psiKC3T_02 : psiKC3T 0 2 = 0 := rfl
theorem psiKC3T_03 : psiKC3T 0 3 = 0 := rfl
theorem psiKC3T_10 : psiKC3T 1 0 = 0 := rfl
theorem psiKC3T_11 : psiKC3T 1 1 = 0 := rfl
theorem psiKC3T_12 : psiKC3T 1 2 = 0 := rfl
theorem psiKC3T_13 : psiKC3T 1 3 = 1 := rfl
theorem psiKC3T_20 : psiKC3T 2 0 = 0 := rfl
theorem psiKC3T_21 : psiKC3T 2 1 = 0 := rfl
theorem psiKC3T_22 : psiKC3T 2 2 = 0 := rfl
theorem psiKC3T_23 : psiKC3T 2 3 = 2 := rfl
theorem psiKC3T_30 : psiKC3T 3 0 = 0 := rfl
theorem psiKC3T_31 : psiKC3T 3 1 = 0 := rfl
theorem psiKC3T_32 : psiKC3T 3 2 = 0 := rfl
theorem psiKC3T_33 : psiKC3T 3 3 = 2 := rfl

def TpKC3T : Template KC3T cAll (cAll 0) where
  E := {s(0, 1), s(0, 2), s(1, 2)}
  L := ![0, 0, 2, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def TmKC3T : Template KC3T cAll (cAll 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 3)}
  L := ![0, 1, 1, 2, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def TqKC3T : Template KC3T cAll (cAll 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 3)}
  L := ![0, 0, 0, 0, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def TrKC3T : Template KC3T cAll (cAll 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 5), s(4, 5)}
  L := ![0, 0, 1, 2, 2, 3]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

theorem tp_charge_KC3T : charge chiKC3T TpKC3T.L TpKC3T.E = 4 := by decide
theorem tm_charge_KC3T : charge chiKC3T TmKC3T.L TmKC3T.E = -4 := by decide
theorem tq_charge_KC3T : charge chiKC3T TqKC3T.L TqKC3T.E = 0 := by decide
theorem tq_value_KC3T : psiNum psiOne TqKC3T.L TqKC3T.E % 3 = 1 := by decide
theorem tr_charge_KC3T : charge chiKC3T TrKC3T.L TrKC3T.E = 0 := by decide
theorem tr_valueE_KC3T : psiNum psiOne TrKC3T.L TrKC3T.E % 3 = 0 := by decide
theorem tr_value_KC3T : psiNum psiKC3T TrKC3T.L TrKC3T.E % 3 = 1 := by decide

def canon_KC3T (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,0}, (2 * u 0 0 - 1 * u 0 1 + 1 * u 0 2) / 6), ({0,0,1}, (1 * u 0 1 - 1 * u 0 2) / 2), ({0,1,2}, (1 * u 0 2) / 1), ({1,2,3}, (1 * u 1 3) / 1), ({2,3,3}, (-1 * u 1 3 + 1 * u 2 3) / 2), ({3,3,3}, (1 * u 1 3 - 1 * u 2 3 + 2 * u 3 3) / 6)]

set_option maxHeartbeats 16000000 in
theorem scalar_ct3_KC3T (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KC3T i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKC3T i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hψE : (3 : ℤ) ∣ ∑ i, ∑ j, psiOne i j * u i j)
    (hψ : (3 : ℤ) ∣ ∑ i, ∑ j, psiKC3T i j * u i j) : ∃ c, LatEq KC3T u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC3T; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KC3T; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KC3T; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKC3T_00, chiKC3T_01, chiKC3T_02, chiKC3T_03, chiKC3T_10, chiKC3T_11, chiKC3T_12, chiKC3T_13, chiKC3T_20, chiKC3T_21, chiKC3T_22, chiKC3T_23, chiKC3T_30, chiKC3T_31, chiKC3T_32, chiKC3T_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33] at hψE
  simp only [Fin.sum_univ_four, psiKC3T_00, psiKC3T_01, psiKC3T_02, psiKC3T_03, psiKC3T_10, psiKC3T_11, psiKC3T_12, psiKC3T_13, psiKC3T_20, psiKC3T_21, psiKC3T_22, psiKC3T_23, psiKC3T_30, psiKC3T_31, psiKC3T_32, psiKC3T_33] at hψ
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KC3T u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KC3T, canon_KC3T, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem chargeTorsion2Inside_KC3T : ChargeTorsion2Inside KC3T cAll (cAll 0) chiKC3T psiOne psiKC3T := by
  intro V _ _ p E hg hv
  rw [isIntDiv_iff_five fiveStep_KC3T KC3T_card hg.1.1]
  refine ⟨hg.1.2.1, hg.1.2.2.1, ?_⟩
  have hch := hg.1.2.2.2.1
  rw [charge_counts] at hch
  have hψE : (3 : ℤ) ∣ psiNum psiOne p E := by have := hg.2; unfold psiVal at this; omega
  have hψ : (3 : ℤ) ∣ psiNum psiKC3T p E := by unfold psiVal at hv; omega
  unfold psiNum at hψE hψ
  obtain ⟨c, hc⟩ := scalar_ct3_KC3T (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hg.1.2.1) (counts_parity p E hg.1.1 hg.1.2.2.1) hch hψE hψ
  exact ⟨c, (latEq_counts_iff KC3T p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem val_psiOne_of_isIntDiv_KC3T {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cAll (cAll 0) e) (hL : IsIntDiv p KC3T L) :
    psiVal psiOne p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KC3T p L c).mpr hc
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
    simp (config := {decide := true}) [KC3T, typeEdgeVec, sum_insert] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiOne_00, psiOne_01, psiOne_02, psiOne_03, psiOne_10, psiOne_11, psiOne_12, psiOne_13, psiOne_20, psiOne_21, psiOne_22, psiOne_23, psiOne_30, psiOne_31, psiOne_32, psiOne_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem val_psiKC3T_of_isIntDiv_KC3T {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4)
    (L : Finset (Sym2 W)) (_hin : ∀ e ∈ L, InsideE p cAll (cAll 0) e) (hL : IsIntDiv p KC3T L) :
    psiVal psiKC3T p L = 0 := by
  obtain ⟨c, hc⟩ := hL.1
  have h := (latEq_counts_iff KC3T p L c).mpr hc
  have hs := unorderedCount_swap p L
  have hψ : (3 : ℤ) ∣ psiNum psiKC3T p L := by
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
    simp (config := {decide := true}) [KC3T, typeEdgeVec, sum_insert] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [Fin.sum_univ_four, psiKC3T_00, psiKC3T_01, psiKC3T_02, psiKC3T_03, psiKC3T_10, psiKC3T_11, psiKC3T_12, psiKC3T_13, psiKC3T_20, psiKC3T_21, psiKC3T_22, psiKC3T_23, psiKC3T_30, psiKC3T_31, psiKC3T_32, psiKC3T_33]
    have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
    have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
    omega
  unfold psiVal; omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_KC3T {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KC3T p A)
    (_hin : ∀ e ∈ A, InsideE p cAll (cAll 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKC3T p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KC3T) hact
  have hp := counts_parity p A hloop h3.2
  generalize unorderedCount p A = u at hs hf hp ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC3T; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KC3T; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KC3T; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKC3T_00, chiKC3T_01, chiKC3T_02, chiKC3T_03, chiKC3T_10, chiKC3T_11, chiKC3T_12, chiKC3T_13, chiKC3T_20, chiKC3T_21, chiKC3T_22, chiKC3T_23, chiKC3T_30, chiKC3T_31, chiKC3T_32, chiKC3T_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KC3T (k : Fin 4) (hk : k ≠ cAll 0) : ∀ u, ScalarHyp KC3T u →
    CountsInside cAll k u → ∃ w, LatEq KC3T u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC3T; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KC3T; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KC3T; decide)
  have hz : u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 ∧ u 1 2 = 0 ∧ u 1 3 = 0 ∧ u 2 3 = 0 ∧ u 3 3 = 0 := ⟨hin 0 0 (by left; simpa [cAll] using fun h => hk h.symm), hin 0 1 (by left; simpa [cAll] using fun h => hk h.symm), hin 0 2 (by left; simpa [cAll] using fun h => hk h.symm), hin 1 2 (by left; simpa [cAll] using fun h => hk h.symm), hin 1 3 (by left; simpa [cAll] using fun h => hk h.symm), hin 2 3 (by left; simpa [cAll] using fun h => hk h.symm), hin 3 3 (by left; simpa [cAll] using fun h => hk h.symm)⟩
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KC3T u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KC3T, canon_KC3T, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KC3T (k : Fin 4) (hk : k ≠ cAll 0) : Even3Inside KC3T cAll k :=
  even3Inside_of_scalar_five KC3T cAll k fiveStep_KC3T KC3T_card (scalar_inside_KC3T k hk)

def aKC3T : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,0,0} then 1 else if τ = {0,0,1} then 1 else if τ = {2,3,3} then 1 else if τ = {3,3,3} then 1 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KC3T : ∀ u c0, ScalarHyp KC3T u → LatEq KC3T u c0 →
    ∃ c, LatEq KC3T u c ∧ ∀ τ ∈ KC3T, -((aKC3T τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC3T; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link KC3T; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link KC3T; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e12 := hc0 1 2
  have e13 := hc0 1 3
  have e23 := hc0 2 3
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KC3T, typeEdgeVec, sum_insert] at e00 e01 e02 e12 e13 e23 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KC3T u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KC3T, canon_KC3T, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KC3T, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KC3T, coeffList, aKC3T] <;> omega

theorem wb_KC3T : WitnessBoundK KC3T 1284 5160 := by
  have h : WitnessBoundK KC3T 1284 (∑ τ ∈ KC3T, (aKC3T τ * 1284 + 4)) :=
    witnessBound_of_latEq_lowerA KC3T KC3T_card aKC3T scalar_witness_KC3T 1284
  have hv : ∑ τ ∈ KC3T, (aKC3T τ * 1284 + 4) = 5160 := by unfold KC3T aKC3T; decide
  rwa [hv] at h

/-- **`UniversalCert KC3T`**. -/
theorem universalCert_KC3T : UniversalCert KC3T :=
  universalCert_of_ct3_components KC3T cAll compLabel_KC3T typesInside_KC3T KC3T_card
    kappaLinks_KC3T localWalk4_KC3T even3Inside_KC3T chiKC3T psiOne psiKC3T chiKC3T_bound kills_KC3T
    chargeTorsion2Inside_KC3T (fun p L hin hL => val_psiOne_of_isIntDiv_KC3T p L hin hL)
    (fun p L hin hL => val_psiKC3T_of_isIntDiv_KC3T p L hin hL)
    (fun p A hA hact hin h3 => four_dvd_KC3T p A hA hact hin h3) TpKC3T TmKC3T TqKC3T TrKC3T
    tp_charge_KC3T tm_charge_KC3T tq_charge_KC3T tq_value_KC3T tr_charge_KC3T tr_valueE_KC3T tr_value_KC3T
    5160 wb_KC3T (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KC3T
