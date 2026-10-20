/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KMFamilies

@[expose] public section

/-!
# The bounded signed inverse for `KM3` (classes of size at least 8)

Same frame as Aristotle's `InverseFMxx` (generator `gen_km.py`): totals from the types
`000` `001` `002` `011` `012` `122` `333`; vertex rows from repeated, singleton, tripartite and monochromatic vertex
modes (per-mode budgets `12 m D/δ²`, `24 m D/δ²` for coefficient mass `m`); zero rows from
internal, repeated and tripartite pair modes and the monochromatic zero-row mode of class `3`.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedFstar PaddedNoCommon PaddedGeneral

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

def realMatrixKM3 (t00 t01 t02 t11 t12 t22 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, t12, 0], ![t02, t12, t22, 0], ![0, 0, 0, t33]]

theorem classTotal_realMatrixKM3 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KM3 g) :
    classTotal p g = realMatrixKM3 (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 1 2) (classTotal p g 2 2) (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p KM3 g hs 0 3 (by unfold Link KM3; decide)
  have h13 := classTotal_zero_of_inactive p KM3 g hs 1 3 (by unfold Link KM3; decide)
  have h23 := classTotal_zero_of_inactive p KM3 g hs 2 3 (by unfold Link KM3; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKM3, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h13, h23]

def typeWeightKM3 (p : V → Fin 4) (z000 z001 z002 z011 z012 z122 z333 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  tripartiteTypeWeight p 0 1 2 z012 a b c +
  repeatedTypeWeight p 2 1 z122 a b c +
  monoTypeWeight p 3 z333 a b c

theorem typeWeightKM3_symmetric (p : V → Fin 4) (z000 z001 z002 z011 z012 z122 z333 : ℝ) :
    TernarySymmetric (typeWeightKM3 p z000 z001 z002 z011 z012 z122 z333) := by
  unfold typeWeightKM3
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem typeWeightKM3_supported (p : V → Fin 4) (z000 z001 z002 z011 z012 z122 z333 : ℝ) :
    TernarySupported p KM3 (typeWeightKM3 p z000 z001 z002 z011 z012 z122 z333) := by
  unfold typeWeightKM3
  repeat' first
    | exact monoTypeWeight_supported p KM3 _ (by unfold Link KM3; decide) _
    | exact aabLift_supported p KM3 _ _ (by decide) (by unfold Link KM3; decide) _
    | exact abcLift_supported p KM3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KM3; decide) _
    | apply TernarySupported.add

theorem typeWeightKM3_totals (p : V → Fin 4) (z000 z001 z002 z011 z012 z122 z333 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKM3 p z000 z001 z002 z011 z012 z122 z333)) =
      realMatrixKM3 (6 * z000 + 2 * z001 + 2 * z002) (2 * z001 + 2 * z011 + 1 * z012) (2 * z002 + 1 * z012) (2 * z011) (1 * z012 + 2 * z122) (2 * z122) (6 * z333) := by
  funext i j
  unfold typeWeightKM3
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKM3] <;> ring

theorem typeWeightKM3_bound (p : V → Fin 4) (z000 z001 z002 z011 z012 z122 z333 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz000 : |z000| ≤ 2 * E) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz012 : |z012| ≤ 8 * E) (hz122 : |z122| ≤ 8 * E) (hz333 : |z333| ≤ 2 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKM3 p z000 z001 z002 z011 z012 z122 z333 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKM3_supported p z000 z001 z002 z011 z012 z122 z333
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KM3 a b c := by
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
  have e4 := tripartiteType_normalizer_bound p 0 1 2 z012 E δ hE hδ hz012 hm
  have e5 := repeatedType_normalizer_bound p 2 1 z122 E δ hE hδ hz122 hm
  have e6 := mono_normalizer_bound p 3 z333 E δ hE hδ hz333 hm
  dsimp only [typeWeightKM3, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
    aabLift, abcLift, pairSymmetrize, aabBase, abcBase]
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
    | exact hM

theorem exists_type_correction_KM3 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KM3 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KM3 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b12 := abs_le.mp (hbound 1 2)
  have b22 := abs_le.mp (hbound 2 2)
  have b33 := abs_le.mp (hbound 3 3)
  let z000 : ℝ := (1 / 6) * classTotal p g 0 0 + (-1 / 6) * classTotal p g 0 1 + (-1 / 6) * classTotal p g 0 2 + (1 / 6) * classTotal p g 1 1 + (1 / 3) * classTotal p g 1 2 + (-1 / 3) * classTotal p g 2 2
  let z001 : ℝ := (1 / 2) * classTotal p g 0 1 + (-1 / 2) * classTotal p g 1 1 + (-1 / 2) * classTotal p g 1 2 + (1 / 2) * classTotal p g 2 2
  let z002 : ℝ := (1 / 2) * classTotal p g 0 2 + (-1 / 2) * classTotal p g 1 2 + (1 / 2) * classTotal p g 2 2
  let z011 : ℝ := (1 / 2) * classTotal p g 1 1
  let z012 : ℝ := 1 * classTotal p g 1 2 + (-1) * classTotal p g 2 2
  let z122 : ℝ := (1 / 2) * classTotal p g 2 2
  let z333 : ℝ := (1 / 6) * classTotal p g 3 3
  have hz000 : |z000| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z000] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz012 : |z012| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z012] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz122 : |z122| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z122] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hz333 : |z333| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z333] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b22.1, b22.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKM3 p z000 z001 z002 z011 z012 z122 z333, typeWeightKM3_symmetric p _ _ _ _ _ _ _,
    typeWeightKM3_supported p _ _ _ _ _ _ _, ?_,
    typeWeightKM3_bound p _ _ _ _ _ _ _ E δ hE hδ hz000 hz001 hz002 hz011 hz012 hz122 hz333 hm⟩
  rw [typeWeightKM3_totals p _ _ _ _ _ _ _ hn hn1 hn2, classTotal_realMatrixKM3 p g hsym hs]
  congr 1 <;> dsimp only [z000, z001, z002, z011, z012, z122, z333] <;> ring

def vertexWeightKM3 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 0 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) (-1 / 2) 0) a b c +
  tripartiteVertexWeight p 0 1 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  singletonVertexWeight p 2 1 (lc d 0 0 (1 / 2) 0) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) (-1 / 2) (1 / 2) 0) a b c +
  tripartiteVertexWeight p 2 0 1 (lc d 0 1 (-1) 0) a b c +
  repeatedVertexWeight p 2 1 (lc d 0 0 1 0) a b c +
  monoVertexWeight p 3 (lc d 0 0 0 1) a b c

theorem vertexWeightKM3_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKM3 p d) := by
  unfold vertexWeightKM3
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem vertexWeightKM3_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KM3 (vertexWeightKM3 p d) := by
  unfold vertexWeightKM3
  repeat' first
    | exact monoVertexWeight_supported p KM3 _ (by unfold Link KM3; decide) _
    | exact aabLift_supported p KM3 _ _ (by decide) (by unfold Link KM3; decide) _
    | exact abcLift_supported p KM3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KM3; decide) _
    | apply TernarySupported.add

theorem vertexWeightKM3_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KM3 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKM3 p d)) a k = d a k := by
  unfold vertexWeightKM3
  simp only [classRow_ternary_add]
  simp only [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 1 0 0 0 0) (hm2 0) (hm 1),
    singletonVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) (-1 / 2) 0 0) (hm 1) (hm1 1),
    tripartiteVertexWeight_rows p 0 1 2 _ (lc_sum_zero p d hz 0 0 1 0 0) (hm 1) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) 0 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm 0),
    singletonVertexWeight_rows p 2 1 _ (lc_sum_zero p d hz 0 0 (1 / 2) 0 1) (hm 2) (hm1 2),
    singletonVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) (1 / 2) 0 2) (hm 0) (hm1 0),
    tripartiteVertexWeight_rows p 2 0 1 _ (lc_sum_zero p d hz 0 1 (-1) 0 2) (hm 0) (hm 1),
    repeatedVertexWeight_rows p 2 1 _ (lc_sum_zero p d hz 0 0 1 0 2) (hm2 2) (hm 1),
    monoVertexWeight_rows p 3 _ (lc_sum_zero p d hz 0 0 0 1 3) (hm2 3) (hm3 3)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KM3; decide)).symm
    | ring

theorem vertexWeightKM3_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKM3 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hf (a0 a1 a2 a3 m : ℝ) (hm0 : |a0| + |a1| + |a2| + |a3| ≤ m) (v : V) :
      |lc d a0 a1 a2 a3 v| ≤ m * D :=
    (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right hm0 hD)
  have e0 := (vertexMode_bounds p (lc d 1 0 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 1 0 0 0 1 (by norm_num)) hm a b c).1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e0
  have e1 := (vertexMode_bounds p (lc d (-1 / 2) (1 / 2) (-1 / 2) 0) ((3 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 2)) hD) hδ (hf (-1 / 2) (1 / 2) (-1 / 2) 0 (3 / 2) (by norm_num)) hm a b c).2.1 1 0
  rw [show 12 * ((3 / 2) * D) / δ ^ 2 = (12 * (3 / 2)) * (D / δ ^ 2) by ring] at e1
  have e2 := (vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).2.2 0 1 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e2
  have e3 := (vertexMode_bounds p (lc d (1 / 2) (-1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (1 / 2) (-1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e3
  have e4 := (vertexMode_bounds p (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c).1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e4
  have e5 := (vertexMode_bounds p (lc d 0 0 (1 / 2) 0) ((1 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)) hD) hδ (hf 0 0 (1 / 2) 0 (1 / 2) (by norm_num)) hm a b c).2.1 2 1
  rw [show 12 * ((1 / 2) * D) / δ ^ 2 = (12 * (1 / 2)) * (D / δ ^ 2) by ring] at e5
  have e6 := (vertexMode_bounds p (lc d (1 / 2) (-1 / 2) (1 / 2) 0) ((3 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 2)) hD) hδ (hf (1 / 2) (-1 / 2) (1 / 2) 0 (3 / 2) (by norm_num)) hm a b c).2.1 0 2
  rw [show 12 * ((3 / 2) * D) / δ ^ 2 = (12 * (3 / 2)) * (D / δ ^ 2) by ring] at e6
  have e7 := (vertexMode_bounds p (lc d 0 1 (-1) 0) (2 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD) hδ (hf 0 1 (-1) 0 2 (by norm_num)) hm a b c).2.2 2 0 1
  rw [show 12 * (2 * D) / δ ^ 2 = (12 * 2) * (D / δ ^ 2) by ring] at e7
  have e8 := (vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).1 2 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e8
  have e9 := monoVertexWeight_bound p 3 (lc d 0 0 0 1) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 0 1 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e9
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold vertexWeightKM3
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 hM0 ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2, e9.1, e9.2]

def zeroRowWeightKM3 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  internalPairWeight p 1 0 g a b c +
  repeatedPairWeight p 2 1 g a b c +
  internalPairWeight p 2 1 g a b c +
  monoPairWeight p 3 g a b c

theorem zeroRowWeightKM3_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightKM3 p g) := by
  unfold zeroRowWeightKM3
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | exact monoPairWeight_symmetric p _ g hs
    | apply TernarySymmetric.add

theorem zeroRowWeightKM3_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KM3 (zeroRowWeightKM3 p g) := by
  unfold zeroRowWeightKM3
  repeat' first
    | exact monoPairWeight_supported p KM3 _ (by unfold Link KM3; decide) _
    | exact aabLift_supported p KM3 _ _ (by decide) (by unfold Link KM3; decide) _
    | exact abcLift_supported p KM3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KM3; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightKM3_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KM3 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0)
    (hm4 : ∀ i, classSize p i - 4 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightKM3 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  have hmono := fun i a b => monoPairWeight_load p i g hs hr hd (hm4 i) a b
  unfold zeroRowWeightKM3
  simp only [ternaryLoad_add, hint, hrep, htri, hmono]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KM3; decide)).symm

theorem zeroRowWeightKM3_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightKM3 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε (by linarith) hg hm a b c
  have h0 := hi 0 1
  have h1 := hr 0 1
  have h2 := hr 0 2
  have h3 := hi 1 0
  have h4 := hr 2 1
  have h5 := hi 2 1
  have h6 := monoPairWeight_bound p 3 g ε δ hε hδ hg hm a b c
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 hpos ⊢
  unfold zeroRowWeightKM3
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

/-- **The ternary bounded signed inverse for `KM3` (classes of size at least 8).** -/
theorem ternaryInverse₈_KM3 : TernaryInverse₈ KM3 := by
  intro V _ _ p g ε γ hε hγ hγ1 hlarge8 hmin hsym hd hs hg
  have hlarge : 4 ≤ γ * (Fintype.card V : ℝ) := by linarith
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
  have hm3 (i : Fin 4) : classSize p i - 3 ≠ 0 := by have := hmin i; linarith
  have hm4 (i : Fin 4) : classSize p i - 4 ≠ 0 := by have := hmin i; linarith
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
      TernarySymmetric w ∧ TernarySupported p KM3 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KM3 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KM3 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKM3 p d, vertexWeightKM3_symmetric p d,
        vertexWeightKM3_supported p d, vertexWeightKM3_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightKM3_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKM3 p f, zeroRowWeightKM3_symmetric p f hf,
        zeroRowWeightKM3_supported p f,
        zeroRowWeightKM3_load p f hf hr hfd hfs hm hm2 hm4, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightKM3_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge8 hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert₈ KM3`.** -/
theorem completeInverseCert₈_KM3 : CompleteInverseCert₈ KM3 :=
  completeInverseCert₈_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse₈_KM3

end PaddedComponents

#print axioms PaddedComponents.completeInverseCert₈_KM3
