/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentTwoCharge
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links

@[expose] public section

/-!
# `KC2C = {001,012,022,112,333}`: a component with two charges of unit `4` and an isolated `333`

Census representative `000 112 123 133 223` (relabelled). Inside the component the lattice is
"even, `χ = 0`, `χ₂ = 0`" (then `3 ∣ e` follows). `UniversalCert` by
`universalCert_of_twoc_components` with four templates (4- and 5-cycles). Generator: `gen_kc2.py`.
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

/-- `{001 012 022 112 333}`. -/
noncomputable def KC2C : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {3, 3, 3}}

theorem KC2C_card : ∀ τ ∈ KC2C, Multiset.card τ = 3 := by unfold KC2C; decide

theorem KC2C_card_eq : KC2C.card = 5 := by unfold KC2C; decide

theorem not_threeStep_KC2C : ¬ ThreeStepLinks KC2C := by unfold ThreeStepLinks Link KC2C; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KC2C : FiveStepLinks KC2C := by
  unfold FiveStepLinks Link KC2C; decide

def kappaKC2C : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 0, 1, 0], ![2, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 3]]

theorem kappaLinks_KC2C : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks KC2C := by
  refine ⟨kappaKC2C, ?_, ?_⟩ <;> unfold Link KC2C kappaKC2C <;> decide

theorem familyFacts_KC2C : FamilyFacts KC2C :=
  ⟨KC2C_card, by unfold Link KC2C; decide,
    by intro i; fin_cases i <;> (unfold Link KC2C; decide)⟩

theorem compLabel_KC2C : CompLabel KC2C cM3 := by
  unfold CompLabel Link KC2C cM3; decide

theorem typesInside_KC2C : TypesInside KC2C cM3 := by
  unfold TypesInside KC2C cM3; decide

theorem localWalk4_KC2C (k : Fin 4) : LocalWalk4 KC2C cM3 k := by
  revert k; unfold LocalWalk4 Link KC2C cM3; decide

theorem isolatedMono_KC2C : IsolatedMono KC2C 3 := by unfold IsolatedMono KC2C; decide

def chiKC2C : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, -2, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]
theorem chiKC2C_bound : ∀ i j, |chiKC2C i j| ≤ 2 := by decide
theorem chiKC2C_00 : chiKC2C 0 0 = 2 := rfl
theorem chiKC2C_01 : chiKC2C 0 1 = -1 := rfl
theorem chiKC2C_02 : chiKC2C 0 2 = 0 := rfl
theorem chiKC2C_03 : chiKC2C 0 3 = 0 := rfl
theorem chiKC2C_10 : chiKC2C 1 0 = -1 := rfl
theorem chiKC2C_11 : chiKC2C 1 1 = -2 := rfl
theorem chiKC2C_12 : chiKC2C 1 2 = 1 := rfl
theorem chiKC2C_13 : chiKC2C 1 3 = 0 := rfl
theorem chiKC2C_20 : chiKC2C 2 0 = 0 := rfl
theorem chiKC2C_21 : chiKC2C 2 1 = 1 := rfl
theorem chiKC2C_22 : chiKC2C 2 2 = 0 := rfl
theorem chiKC2C_23 : chiKC2C 2 3 = 0 := rfl
theorem chiKC2C_30 : chiKC2C 3 0 = 0 := rfl
theorem chiKC2C_31 : chiKC2C 3 1 = 0 := rfl
theorem chiKC2C_32 : chiKC2C 3 2 = 0 := rfl
theorem chiKC2C_33 : chiKC2C 3 3 = 0 := rfl
theorem kills_chiKC2C : Kills chiKC2C KC2C := by
  unfold Kills pair KC2C chiKC2C; decide

def chiBKC2C : Fin 4 → Fin 4 → ℤ := ![![-2, 1, -1, 0], ![1, 0, 0, 0], ![-1, 0, 2, 0], ![0, 0, 0, 0]]
theorem chiBKC2C_bound : ∀ i j, |chiBKC2C i j| ≤ 2 := by decide
theorem chiBKC2C_00 : chiBKC2C 0 0 = -2 := rfl
theorem chiBKC2C_01 : chiBKC2C 0 1 = 1 := rfl
theorem chiBKC2C_02 : chiBKC2C 0 2 = -1 := rfl
theorem chiBKC2C_03 : chiBKC2C 0 3 = 0 := rfl
theorem chiBKC2C_10 : chiBKC2C 1 0 = 1 := rfl
theorem chiBKC2C_11 : chiBKC2C 1 1 = 0 := rfl
theorem chiBKC2C_12 : chiBKC2C 1 2 = 0 := rfl
theorem chiBKC2C_13 : chiBKC2C 1 3 = 0 := rfl
theorem chiBKC2C_20 : chiBKC2C 2 0 = -1 := rfl
theorem chiBKC2C_21 : chiBKC2C 2 1 = 0 := rfl
theorem chiBKC2C_22 : chiBKC2C 2 2 = 2 := rfl
theorem chiBKC2C_23 : chiBKC2C 2 3 = 0 := rfl
theorem chiBKC2C_30 : chiBKC2C 3 0 = 0 := rfl
theorem chiBKC2C_31 : chiBKC2C 3 1 = 0 := rfl
theorem chiBKC2C_32 : chiBKC2C 3 2 = 0 := rfl
theorem chiBKC2C_33 : chiBKC2C 3 3 = 0 := rfl
theorem kills_chiBKC2C : Kills chiBKC2C KC2C := by
  unfold Kills pair KC2C chiBKC2C; decide

def TmKC2C : Template KC2C cM3 (cM3 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 3)}
  L := ![0, 0, 1, 1, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def TpKC2C : Template KC2C cM3 (cM3 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 4)}
  L := ![0, 0, 1, 1, 2, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def UmKC2C : Template KC2C cM3 (cM3 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 4), s(3, 4)}
  L := ![0, 0, 0, 1, 1, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

def UpKC2C : Template KC2C cM3 (cM3 0) where
  E := {s(0, 1), s(0, 2), s(1, 3), s(2, 3)}
  L := ![0, 1, 1, 2, 0, 0]
  loop := by decide
  act := by unfold ActiveEdges Link; decide
  even := by decide
  card := by decide
  inside := by decide

theorem Tp_chi_KC2C : charge chiKC2C TpKC2C.L TpKC2C.E = 4 := by decide
theorem Tm_chi_KC2C : charge chiKC2C TmKC2C.L TmKC2C.E = -4 := by decide
theorem Tp_chiB_KC2C : charge chiBKC2C TpKC2C.L TpKC2C.E = 0 := by decide
theorem Tm_chiB_KC2C : charge chiBKC2C TmKC2C.L TmKC2C.E = 0 := by decide
theorem Up_chiB_KC2C : charge chiBKC2C UpKC2C.L UpKC2C.E = 4 := by decide
theorem Um_chiB_KC2C : charge chiBKC2C UmKC2C.L UmKC2C.E = -4 := by decide
theorem Up_chi_KC2C : charge chiKC2C UpKC2C.L UpKC2C.E = 0 := by decide
theorem Um_chi_KC2C : charge chiKC2C UmKC2C.L UmKC2C.E = 0 := by decide

def canon_KC2C (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  coeffList [({0,0,1}, (1 * u 0 0) / 1), ({0,1,2}, (-2 * u 0 0 + 1 * u 0 1) / 1), ({0,2,2}, (1 * u 2 2) / 1), ({1,1,2}, (1 * u 1 1) / 1), ({3,3,3}, (1 * u 3 3) / 3)]

set_option maxHeartbeats 16000000 in
theorem scalar_2c_KC2C (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link KC2C i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiKC2C i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hc2 : ∑ i, ∑ j, chiBKC2C i j * ((if i = j then 2 else 1) * u i j) = 0)
    (hin : CountsInside cM3 0 u) : ∃ c, LatEq KC2C u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC2C; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KC2C; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KC2C; decide)
  have z33 : u 3 3 = 0 := hin 3 3 (by left; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKC2C_00, chiKC2C_01, chiKC2C_02, chiKC2C_03, chiKC2C_10, chiKC2C_11, chiKC2C_12, chiKC2C_13, chiKC2C_20, chiKC2C_21, chiKC2C_22, chiKC2C_23, chiKC2C_30, chiKC2C_31, chiKC2C_32, chiKC2C_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  simp only [Fin.sum_univ_four, chiBKC2C_00, chiBKC2C_01, chiBKC2C_02, chiBKC2C_03, chiBKC2C_10, chiBKC2C_11, chiBKC2C_12, chiBKC2C_13, chiBKC2C_20, chiBKC2C_21, chiBKC2C_22, chiBKC2C_23, chiBKC2C_30, chiBKC2C_31, chiBKC2C_32, chiBKC2C_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc2
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨canon_KC2C u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KC2C, canon_KC2C, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem twoChargeInside_KC2C : TwoChargeInside KC2C cM3 (cM3 0) chiKC2C chiBKC2C := by
  intro V _ _ p E hloop hact hin hev hch hch2
  rw [isIntDiv_iff_five fiveStep_KC2C KC2C_card hloop]
  refine ⟨hact, hev, ?_⟩
  rw [charge_counts] at hch hch2
  obtain ⟨c, hc⟩ := scalar_2c_KC2C (unorderedCount p E) (unorderedCount_swap p E)
    (counts_forbid hact) (counts_parity p E hloop hev) hch hch2 (countsInside_of_insideE hin)
  exact ⟨c, (latEq_counts_iff KC2C p E c).mp hc⟩

set_option maxHeartbeats 16000000 in
theorem four_dvd_chi_KC2C {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KC2C p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiKC2C p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KC2C) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  generalize unorderedCount p A = u at hs hf hp hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC2C; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KC2C; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KC2C; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiKC2C_00, chiKC2C_01, chiKC2C_02, chiKC2C_03, chiKC2C_10, chiKC2C_11, chiKC2C_12, chiKC2C_13, chiKC2C_20, chiKC2C_21, chiKC2C_22, chiKC2C_23, chiKC2C_30, chiKC2C_31, chiKC2C_32, chiKC2C_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem four_dvd_chiB_KC2C {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges KC2C p A)
    (hin : ∀ e ∈ A, InsideE p cM3 (cM3 0) e)
    (h3 : OnePart.Even3 A) : (4 : ℤ) ∣ charge chiBKC2C p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := KC2C) hact
  have hp := counts_parity p A hloop h3.2
  have hin' := countsInside_of_insideE hin
  generalize unorderedCount p A = u at hs hf hp hin' ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC2C; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KC2C; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KC2C; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiBKC2C_00, chiBKC2C_01, chiBKC2C_02, chiBKC2C_03, chiBKC2C_10, chiBKC2C_11, chiBKC2C_12, chiBKC2C_13, chiBKC2C_20, chiBKC2C_21, chiBKC2C_22, chiBKC2C_23, chiBKC2C_30, chiBKC2C_31, chiBKC2C_32, chiBKC2C_33, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

set_option maxHeartbeats 16000000 in
theorem scalar_inside_KC2C (k : Fin 4) (hk : k ≠ cM3 0) : ∀ u, ScalarHyp KC2C u →
    CountsInside cM3 k u → ∃ w, LatEq KC2C u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC2C; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KC2C; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KC2C; decide)
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
  refine ⟨canon_KC2C u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [KC2C, canon_KC2C, coeffList, typeEdgeVec, sum_insert] <;>
    omega

theorem even3Inside_KC2C (k : Fin 4) (hk : k ≠ cM3 0) : Even3Inside KC2C cM3 k :=
  even3Inside_of_scalar_five KC2C cM3 k fiveStep_KC2C KC2C_card (scalar_inside_KC2C k hk)

def aKC2C : Multiset (Fin 4) → ℕ := fun τ => if τ = {0,1,2} then 2 else 0

set_option maxHeartbeats 16000000 in
theorem scalar_witness_KC2C : ∀ u c0, ScalarHyp KC2C u → LatEq KC2C u c0 →
    ∃ c, LatEq KC2C u c ∧ ∀ τ ∈ KC2C, -((aKC2C τ : ℤ) * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link KC2C; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link KC2C; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link KC2C; decide)
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e02 := hc0 0 2
  have e11 := hc0 1 1
  have e12 := hc0 1 2
  have e22 := hc0 2 2
  have e33 := hc0 3 3
  simp (config := {decide := true}) [KC2C, typeEdgeVec, sum_insert] at e00 e01 e02 e11 e12 e22 e33
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3; have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2; have n23 := hn 2 3; have n33 := hn 3 3
  refine ⟨canon_KC2C u, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [KC2C, canon_KC2C, coeffList, typeEdgeVec, sum_insert] <;>
      omega
  · unfold totalU
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
    intro τ hτ
    simp only [KC2C, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [canon_KC2C, coeffList, aKC2C] <;> omega

theorem wb_KC2C : WitnessBoundK KC2C 2184 4388 := by
  have h : WitnessBoundK KC2C 2184 (∑ τ ∈ KC2C, (aKC2C τ * 2184 + 4)) :=
    witnessBound_of_latEq_lowerA KC2C KC2C_card aKC2C scalar_witness_KC2C 2184
  have hv : ∑ τ ∈ KC2C, (aKC2C τ * 2184 + 4) = 4388 := by unfold KC2C aKC2C; decide
  rwa [hv] at h

/-- **`UniversalCert KC2C`**. -/
theorem universalCert_KC2C : UniversalCert KC2C :=
  universalCert_of_twoc_components KC2C cM3 compLabel_KC2C typesInside_KC2C KC2C_card
    kappaLinks_KC2C localWalk4_KC2C even3Inside_KC2C chiKC2C chiBKC2C chiKC2C_bound chiBKC2C_bound
    kills_chiKC2C kills_chiBKC2C twoChargeInside_KC2C
    (fun p A hA hact hin h3 => four_dvd_chi_KC2C p A hA hact hin h3)
    (fun p A hA hact hin h3 => four_dvd_chiB_KC2C p A hA hact hin h3)
    TpKC2C TmKC2C UpKC2C UmKC2C Tp_chi_KC2C Tm_chi_KC2C Tp_chiB_KC2C Tm_chiB_KC2C Up_chiB_KC2C Um_chiB_KC2C
    Up_chi_KC2C Um_chi_KC2C 4388 wb_KC2C (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_KC2C
