/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.FamiliesT234

@[expose] public section

/-!
# The bounded signed inverse for `KT4` (the `KT4` inverse without the `233` modes; `t33 = 0`)

Types: 000 001 002 011 022 111 223 233. Totals use monochromatic and repeated type modes; the type vectors span all
allowed class-pair coordinates, so no compatibility condition is needed. Vertex rows use repeated and
singleton vertex modes with inputs `lc d …` (coefficient mass `≤ 2`), zero rows use internal and
repeated pair modes. The bound `2^20 ε/(γ^6 n)` of the F* inverse is kept.
-/

noncomputable section

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedFstar

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

def realMatrixKT4 (t00 t01 t02 t11 t22 t23 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, 0, 0], ![t02, 0, t22, t23], ![0, 0, t23, t33]]

theorem classTotal_realMatrixKT4 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KT4 g) :
    classTotal p g = realMatrixKT4 (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 2 2) (classTotal p g 2 3) 0 := by
  have h03 := classTotal_zero_of_inactive p KT4 g hs 0 3 (by unfold Link KT4; decide)
  have h12 := classTotal_zero_of_inactive p KT4 g hs 1 2 (by unfold Link KT4; decide)
  have h13 := classTotal_zero_of_inactive p KT4 g hs 1 3 (by unfold Link KT4; decide)
  have h33 := classTotal_zero_of_inactive p KT4 g hs 3 3 (by unfold Link KT4; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKT4, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1, classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h12, h13, h33]

def typeWeightKT4 (p : V → Fin 4) (z000 z001 z002 z011 z022 z111 z223 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  repeatedTypeWeight p 2 0 z022 a b c +
  monoTypeWeight p 1 z111 a b c +
  repeatedTypeWeight p 2 3 z223 a b c

theorem typeWeightKT4_symmetric (p : V → Fin 4) (z000 z001 z002 z011 z022 z111 z223 : ℝ) :
    TernarySymmetric (typeWeightKT4 p z000 z001 z002 z011 z022 z111 z223) := by
  unfold typeWeightKT4
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem typeWeightKT4_supported (p : V → Fin 4) (z000 z001 z002 z011 z022 z111 z223 : ℝ) :
    TernarySupported p KT4 (typeWeightKT4 p z000 z001 z002 z011 z022 z111 z223) := by
  unfold typeWeightKT4
  repeat' first
    | exact monoTypeWeight_supported p KT4 _ (by unfold Link KT4; decide) _
    | exact aabLift_supported p KT4 _ _ (by decide) (by unfold Link KT4; decide) _
    | apply TernarySupported.add

theorem typeWeightKT4_totals (p : V → Fin 4) (z000 z001 z002 z011 z022 z111 z223 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKT4 p z000 z001 z002 z011 z022 z111 z223)) =
      realMatrixKT4 (6 * z000 + 2 * z001 + 2 * z002) (2 * z001 + 2 * z011) (2 * z002 + 2 * z022) (2 * z011 + 6 * z111) (2 * z022 + 2 * z223) (2 * z223) 0 := by
  funext i j
  unfold typeWeightKT4
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  simp only [hmo, ht]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKT4] <;> ring

theorem typeWeightKT4_bound (p : V → Fin 4) (z000 z001 z002 z011 z022 z111 z223 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz000 : |z000| ≤ 2 * E) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz022 : |z022| ≤ 8 * E) (hz111 : |z111| ≤ 2 * E) (hz223 : |z223| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKT4 p z000 z001 z002 z011 z022 z111 z223 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKT4_supported p z000 z001 z002 z011 z022 z111 z223
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KT4 a b c := by
      intro h
      rcases hdiag with hdiag | hdiag | hdiag
      · exact h.1 hdiag
      · exact h.2.1 hdiag
      · exact h.2.2.1 hdiag
    rw [hsup a b c hbad, abs_zero]
    exact hM
  have hab : a ≠ b := fun h => hdiag (Or.inl h)
  have hac : a ≠ c := fun h => hdiag (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hdiag (Or.inr (Or.inr h))
  have e0 := mono_normalizer_bound p 0 z000 E δ hE hδ hz000 hm
  have e1 := repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ hz001 hm
  have e2 := repeatedType_normalizer_bound p 0 2 z002 E δ hE hδ hz002 hm
  have e3 := repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ hz011 hm
  have e4 := repeatedType_normalizer_bound p 2 0 z022 E δ hE hδ hz022 hm
  have e5 := mono_normalizer_bound p 1 z111 E δ hE hδ hz111 hm
  have e6 := repeatedType_normalizer_bound p 2 3 z223 E δ hE hδ hz223 hm
  dsimp only [typeWeightKT4, monoTypeWeight, repeatedTypeWeight, aabLift, pairSymmetrize, aabBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact e0
    | exact e1
    | exact e2
    | exact e3
    | exact e4
    | exact e5
    | exact e6
    | exact e7
    | exact hM

theorem exists_type_correction_KT4 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KT4 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KT4 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b22 := abs_le.mp (hbound 2 2)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  let z000 : ℝ := (1 / 6 : ℝ) * classTotal p g 0 0 + (-1 / 6 : ℝ) * classTotal p g 0 1 + (-1 / 6 : ℝ) * classTotal p g 0 2 + (1 / 6 : ℝ) * classTotal p g 2 2 + (-1 / 6 : ℝ) * classTotal p g 2 3
  let z001 : ℝ := (1 / 2 : ℝ) * classTotal p g 0 1
  let z002 : ℝ := (1 / 2 : ℝ) * classTotal p g 0 2 + (-1 / 2 : ℝ) * classTotal p g 2 2 + (1 / 2 : ℝ) * classTotal p g 2 3
  let z011 : ℝ := 0
  let z022 : ℝ := (1 / 2 : ℝ) * classTotal p g 2 2 + (-1 / 2 : ℝ) * classTotal p g 2 3
  let z111 : ℝ := (1 / 6 : ℝ) * classTotal p g 1 1
  let z223 : ℝ := (1 / 2 : ℝ) * classTotal p g 2 3
  have hz000 : |z000| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z000] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz022 : |z022| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z022] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz111 : |z111| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z111] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz223 : |z223| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z223] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKT4 p z000 z001 z002 z011 z022 z111 z223, typeWeightKT4_symmetric p _ _ _ _ _ _ _,
    typeWeightKT4_supported p _ _ _ _ _ _ _, ?_,
    typeWeightKT4_bound p _ _ _ _ _ _ _ E δ hE hδ hz000 hz001 hz002 hz011 hz022 hz111 hz223 hm⟩
  rw [typeWeightKT4_totals p _ _ _ _ _ _ _ hn hn1 hn2, classTotal_realMatrixKT4 p g hsym hs]
  congr 1 <;> dsimp only [z000, z001, z002, z011, z022, z111, z223] <;> ring

def vertexWeightKT4 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 (-1) 0) a b c +
  repeatedVertexWeight p 0 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) (1 / 2) 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  repeatedVertexWeight p 2 0 (lc d 0 0 1 (-1)) a b c +
  repeatedVertexWeight p 2 3 (lc d 0 0 0 1) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) 0 (-1 / 2) (1 / 2)) a b c +
  singletonVertexWeight p 2 3 (lc d 0 0 (1 / 2) 0) a b c

theorem vertexWeightKT4_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKT4 p d) := by
  unfold vertexWeightKT4
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem vertexWeightKT4_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KT4 (vertexWeightKT4 p d) := by
  unfold vertexWeightKT4
  repeat' first
    | exact aabLift_supported p KT4 _ _ (by decide) (by unfold Link KT4; decide) _
    | apply TernarySupported.add

theorem vertexWeightKT4_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KT4 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKT4 p d)) a k = d a k := by
  unfold vertexWeightKT4
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 1 0 (-1) 0 0) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz 0 0 1 0 0) (hm2 0) (hm 2),
    singletonVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) (1 / 2) 0 0) (hm 1) (hm1 1),
    repeatedVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm 0),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) 0 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 2 0 _ (lc_sum_zero p d hz 0 0 1 (-1) 2) (hm2 2) (hm 0),
    repeatedVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 0 1 2) (hm2 2) (hm 3),
    singletonVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) 0 (-1 / 2) (1 / 2) 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 (1 / 2) 0 3) (hm 2) (hm1 2)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KT4; decide)).symm
    | ring

theorem vertexWeightKT4_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKT4 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have e0 := (hb (lc d 1 0 (-1) 0) (lc_bound_two d D hD hd 1 0 (-1) 0 (by norm_num))).1 0 1
  have e1 := (hb (lc d 0 0 1 0) (lc_bound_two d D hD hd 0 0 1 0 (by norm_num))).1 0 2
  have e2 := (hb (lc d (-1 / 2) (1 / 2) (1 / 2) 0) (lc_bound_two d D hD hd (-1 / 2) (1 / 2) (1 / 2) 0 (by norm_num))).2.1 1 0
  have e3 := (hb (lc d 0 1 0 0) (lc_bound_two d D hD hd 0 1 0 0 (by norm_num))).1 1 0
  have e4 := (hb (lc d (1 / 2) (-1 / 2) 0 0) (lc_bound_two d D hD hd (1 / 2) (-1 / 2) 0 0 (by norm_num))).2.1 0 1
  have e5 := (hb (lc d 0 0 1 (-1)) (lc_bound_two d D hD hd 0 0 1 (-1) (by norm_num))).1 2 0
  have e6 := (hb (lc d 0 0 0 1) (lc_bound_two d D hD hd 0 0 0 1 (by norm_num))).1 2 3
  have e7 := (hb (lc d (1 / 2) 0 (-1 / 2) (1 / 2)) (lc_bound_two d D hD hd (1 / 2) 0 (-1 / 2) (1 / 2) (by norm_num))).2.1 0 2
  have e8 := (hb (lc d 0 0 0 1) (lc_bound_two d D hD hd 0 0 0 1 (by norm_num))).1 3 2
  have e9 := (hb (lc d 0 0 (1 / 2) 0) (lc_bound_two d D hD hd 0 0 (1 / 2) 0 (by norm_num))).2.1 2 3
  have hMpos : 0 ≤ 12 * (2 * D) / δ ^ 2 := by positivity
  unfold vertexWeightKT4
  have hM288 : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * (2 * D) / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 hMpos ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2, e9.1, e9.2]

def zeroRowWeightKT4 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  internalPairWeight p 1 0 g a b c +
  internalPairWeight p 2 0 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  repeatedPairWeight p 2 3 g a b c

theorem zeroRowWeightKT4_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightKT4 p g) := by
  unfold zeroRowWeightKT4
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | apply TernarySymmetric.add

theorem zeroRowWeightKT4_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KT4 (zeroRowWeightKT4 p g) := by
  unfold zeroRowWeightKT4
  repeat' first
    | exact aabLift_supported p KT4 _ _ (by decide) (by unfold Link KT4; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightKT4_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KT4 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightKT4 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  unfold zeroRowWeightKT4
  simp only [ternaryLoad_add, hint, hrep]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KT4; decide)).symm

theorem zeroRowWeightKT4_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightKT4 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, -⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hi 1 0
  have h2 := hi 2 0
  have h3 := hi 3 2
  have h4 := hr 0 1
  have h5 := hr 0 2
  have h6 := hr 2 3
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 hpos ⊢
  unfold zeroRowWeightKT4
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

/-- **The ternary bounded signed inverse for `KT4`.** -/
theorem ternaryInverse_KT4 : TernaryInverse KT4 := by
  intro V _ _ p g ε γ hε hγ hγ1 hlarge hmin hsym hd hs hg
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    exact (mul_pos_iff_of_pos_left hγ).mp (lt_of_lt_of_le (by norm_num) hlarge)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hε1 : 0 ≤ 33 * ε / γ ^ 3 := by positivity
  have hε2 : 0 ≤ 9537 * ε / γ ^ 5 := by positivity
  have hm (i : Fin 4) : classSize p i ≠ 0 := by have := hmin i; linarith
  have hm1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hmin i; linarith
  have hm2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hmin i; linarith
  obtain ⟨hstep1, hstep2, hbudget⟩ := complete_inverse_budgets ε γ n hε hγ hγ1 hn
  have he0 : 32 * (ε * n ^ 2) / (γ * n) ^ 3 = 32 * ε / (γ ^ 3 * n) := by
    field_simp [hγ0, hn0]
  have he1 : 288 * (n * (33 * ε / γ ^ 3)) / (γ * n) ^ 2 =
      9504 * ε / (γ ^ 5 * n) := by
    field_simp [hγ0, hn0]
    ring
  have he2 : 96 * (9537 * ε / γ ^ 5) / (γ * n) = 915552 * ε / (γ ^ 6 * n) := by
    field_simp [hγ0, hn0]
    ring
  have hstage : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KT4 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KT4 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KT4 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKT4 p d, vertexWeightKT4_symmetric p d,
        vertexWeightKT4_supported p d, vertexWeightKT4_rows p d hz hds hm hm1 hm2, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightKT4_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKT4 p f, zeroRowWeightKT4_symmetric p f hf,
        zeroRowWeightKT4_supported p f, zeroRowWeightKT4_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightKT4_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

end PaddedNoCommon
