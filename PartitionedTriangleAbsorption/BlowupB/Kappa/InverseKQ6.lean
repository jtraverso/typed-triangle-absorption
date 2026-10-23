/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.G3Families

@[expose] public section

/-!
# The bounded signed inverse for `KQ6` (classes of size at least 8)

Same frame as Aristotle's `InverseFMxx` (generator `gen_km.py`): totals from the types
`001` `011` `222` `223` `233`; vertex rows from repeated, singleton, tripartite and monochromatic vertex
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

def realMatrixKQ6 (t00 t01 t11 t22 t23 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, 0, 0], ![t01, t11, 0, 0], ![0, 0, t22, t23], ![0, 0, t23, t33]]

theorem classTotal_realMatrixKQ6 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KQ6 g) :
    classTotal p g = realMatrixKQ6 (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 1 1) (classTotal p g 2 2) (classTotal p g 2 3) (classTotal p g 3 3) := by
  have h02 := classTotal_zero_of_inactive p KQ6 g hs 0 2 (by unfold Link KQ6; decide)
  have h03 := classTotal_zero_of_inactive p KQ6 g hs 0 3 (by unfold Link KQ6; decide)
  have h12 := classTotal_zero_of_inactive p KQ6 g hs 1 2 (by unfold Link KQ6; decide)
  have h13 := classTotal_zero_of_inactive p KQ6 g hs 1 3 (by unfold Link KQ6; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKQ6, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h02, h03, h12, h13]

def typeWeightKQ6 (p : V → Fin 4) (z001 z011 z222 z223 z233 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  monoTypeWeight p 2 z222 a b c +
  repeatedTypeWeight p 2 3 z223 a b c +
  repeatedTypeWeight p 3 2 z233 a b c

theorem typeWeightKQ6_symmetric (p : V → Fin 4) (z001 z011 z222 z223 z233 : ℝ) :
    TernarySymmetric (typeWeightKQ6 p z001 z011 z222 z223 z233) := by
  unfold typeWeightKQ6
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact monoTypeWeight_symmetric p _ _
    | with_reducible exact repeatedTypeWeight_symmetric p _ _ _
    | with_reducible exact tripartiteTypeWeight_symmetric p _ _ _ _
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem typeWeightKQ6_supported (p : V → Fin 4) (z001 z011 z222 z223 z233 : ℝ) :
    TernarySupported p KQ6 (typeWeightKQ6 p z001 z011 z222 z223 z233) := by
  unfold typeWeightKQ6
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact monoTypeWeight_supported p KQ6 _ (by unfold Link KQ6; decide) _
    | exact aabLift_supported p KQ6 _ _ (by decide) (by unfold Link KQ6; decide) _
    | exact abcLift_supported p KQ6 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KQ6; decide) _
    | apply TernarySupported.add

theorem typeWeightKQ6_totals (p : V → Fin 4) (z001 z011 z222 z223 z233 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKQ6 p z001 z011 z222 z223 z233)) =
      realMatrixKQ6 (2 * z001) (2 * z001 + 2 * z011) (2 * z011) (6 * z222 + 2 * z223) (2 * z223 + 2 * z233) (2 * z233) := by
  funext i j
  unfold typeWeightKQ6
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKQ6] <;> ring

theorem typeWeightKQ6_bound (p : V → Fin 4) (z001 z011 z222 z223 z233 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz001 : |z001| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz222 : |z222| ≤ 2 * E) (hz223 : |z223| ≤ 8 * E) (hz233 : |z233| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKQ6 p z001 z011 z222 z223 z233 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKQ6_supported p z001 z011 z222 z223 z233
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KQ6 a b c := by
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
  have e0 := repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ hz001 hm
  have e1 := repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ hz011 hm
  have e2 := mono_normalizer_bound p 2 z222 E δ hE hδ hz222 hm
  have e3 := repeatedType_normalizer_bound p 2 3 z223 E δ hE hδ hz223 hm
  have e4 := repeatedType_normalizer_bound p 3 2 z233 E δ hE hδ hz233 hm
  dsimp only [typeWeightKQ6, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
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
    | exact hM

/-- The real compatibility of `KQ6` on class totals (the charge vanishes on the totals). -/
def CompatKQ6 (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  (1 : ℝ) * classTotal p g 0 0 + (-1 : ℝ) * classTotal p g 0 1 + (1 : ℝ) * classTotal p g 1 1 = 0

theorem exists_type_correction_KQ6 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KQ6 g)
    (hcompat : CompatKQ6 p g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KQ6 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  unfold CompatKQ6 at hcompat
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b11 := abs_le.mp (hbound 1 1)
  have b22 := abs_le.mp (hbound 2 2)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  let z001 : ℝ := (1 / 2) * classTotal p g 0 0
  let z011 : ℝ := (1 / 2) * classTotal p g 1 1
  let z222 : ℝ := (1 / 6) * classTotal p g 2 2 + (-1 / 6) * classTotal p g 2 3 + (1 / 6) * classTotal p g 3 3
  let z223 : ℝ := (1 / 2) * classTotal p g 2 3 + (-1 / 2) * classTotal p g 3 3
  let z233 : ℝ := (1 / 2) * classTotal p g 3 3
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz222 : |z222| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z222] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz223 : |z223| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z223] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hz233 : |z233| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z233] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b11.1, b11.2, b22.1, b22.2, b23.1, b23.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKQ6 p z001 z011 z222 z223 z233, typeWeightKQ6_symmetric p _ _ _ _ _,
    typeWeightKQ6_supported p _ _ _ _ _, ?_,
    typeWeightKQ6_bound p _ _ _ _ _ E δ hE hδ hz001 hz011 hz222 hz223 hz233 hm⟩
  rw [typeWeightKQ6_totals p _ _ _ _ _ hn hn1 hn2, classTotal_realMatrixKQ6 p g hsym hs]
  congr 1 <;> dsimp only [z001, z011, z222, z223, z233] <;> linarith

def vertexWeightKQ6 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 0 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) 0 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  repeatedVertexWeight p 2 3 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 3 2 (lc d 0 0 (-1 / 2) (1 / 2)) a b c +
  singletonVertexWeight p 2 3 (lc d 0 0 (1 / 2) (-1 / 2)) a b c +
  repeatedVertexWeight p 3 2 (lc d 0 0 0 1) a b c

theorem vertexWeightKQ6_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKQ6 p d) := by
  unfold vertexWeightKQ6
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact repeatedVertexWeight_symmetric p _ _ _
    | with_reducible exact singletonVertexWeight_symmetric p _ _ _
    | with_reducible exact tripartiteVertexWeight_symmetric p _ _ _ _
    | with_reducible exact monoVertexWeight_symmetric p _ _
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem vertexWeightKQ6_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KQ6 (vertexWeightKQ6 p d) := by
  unfold vertexWeightKQ6
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact monoVertexWeight_supported p KQ6 _ (by unfold Link KQ6; decide) _
    | exact aabLift_supported p KQ6 _ _ (by decide) (by unfold Link KQ6; decide) _
    | exact abcLift_supported p KQ6 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KQ6; decide) _
    | apply TernarySupported.add

theorem vertexWeightKQ6_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KQ6 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKQ6 p d)) a k = d a k := by
  unfold vertexWeightKQ6
  simp only [classRow_ternary_add]
  simp only [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 1 0 0 0 0) (hm2 0) (hm 1),
    singletonVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) 0 0 0) (hm 1) (hm1 1),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) 0 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm 0),
    repeatedVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 1 0 2) (hm2 2) (hm 3),
    singletonVertexWeight_rows p 3 2 _ (lc_sum_zero p d hz 0 0 (-1 / 2) (1 / 2) 2) (hm 3) (hm1 3),
    singletonVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 (1 / 2) (-1 / 2) 3) (hm 2) (hm1 2),
    repeatedVertexWeight_rows p 3 2 _ (lc_sum_zero p d hz 0 0 0 1 3) (hm2 3) (hm 2)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KQ6; decide)).symm
    | ring

theorem vertexWeightKQ6_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKQ6 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hf (a0 a1 a2 a3 m : ℝ) (hm0 : |a0| + |a1| + |a2| + |a3| ≤ m) (v : V) :
      |lc d a0 a1 a2 a3 v| ≤ m * D :=
    (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right hm0 hD)
  have e0 := (vertexMode_bounds p (lc d 1 0 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 1 0 0 0 1 (by norm_num)) hm a b c).1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e0
  have e1 := (vertexMode_bounds p (lc d (-1 / 2) (1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (-1 / 2) (1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e1
  have e2 := (vertexMode_bounds p (lc d (1 / 2) (-1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (1 / 2) (-1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e2
  have e3 := (vertexMode_bounds p (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c).1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e3
  have e4 := (vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).1 2 3
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e4
  have e5 := (vertexMode_bounds p (lc d 0 0 (-1 / 2) (1 / 2)) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 (-1 / 2) (1 / 2) 1 (by norm_num)) hm a b c).2.1 3 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e5
  have e6 := (vertexMode_bounds p (lc d 0 0 (1 / 2) (-1 / 2)) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 (1 / 2) (-1 / 2) 1 (by norm_num)) hm a b c).2.1 2 3
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e6
  have e7 := (vertexMode_bounds p (lc d 0 0 0 1) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 0 1 1 (by norm_num)) hm a b c).1 3 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e7
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold vertexWeightKQ6
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 hM0 ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2]

def zeroRowWeightKQ6 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  internalPairWeight p 1 0 g a b c +
  internalPairWeight p 2 3 g a b c +
  repeatedPairWeight p 2 3 g a b c +
  internalPairWeight p 3 2 g a b c

theorem zeroRowWeightKQ6_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightKQ6 p g) := by
  unfold zeroRowWeightKQ6
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact internalPairWeight_symmetric p _ _ g hs
    | with_reducible exact repeatedPairWeight_symmetric p _ _ g
    | with_reducible exact abcLift_symmetric p _ _ _ _
    | with_reducible exact monoPairWeight_symmetric p _ g hs
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | exact monoPairWeight_symmetric p _ g hs
    | apply TernarySymmetric.add

theorem zeroRowWeightKQ6_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KQ6 (zeroRowWeightKQ6 p g) := by
  unfold zeroRowWeightKQ6
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact monoPairWeight_supported p KQ6 _ (by unfold Link KQ6; decide) _
    | exact aabLift_supported p KQ6 _ _ (by decide) (by unfold Link KQ6; decide) _
    | exact abcLift_supported p KQ6 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KQ6; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightKQ6_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KQ6 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0)
    (hm4 : ∀ i, classSize p i - 4 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightKQ6 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  have hmono := fun i a b => monoPairWeight_load p i g hs hr hd (hm4 i) a b
  unfold zeroRowWeightKQ6
  simp only [ternaryLoad_add, hint, hrep, htri, hmono]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KQ6; decide)).symm

theorem zeroRowWeightKQ6_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightKQ6 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε (by linarith) hg hm a b c
  have h0 := hi 0 1
  have h1 := hr 0 1
  have h2 := hi 1 0
  have h3 := hi 2 3
  have h4 := hr 2 3
  have h5 := hi 3 2
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 hpos ⊢
  unfold zeroRowWeightKQ6
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-- **The ternary bounded signed inverse for `KQ6` (classes of size at least 8).** -/
theorem ternaryInverse₈_KQ6 (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (g : V → V → ℝ) (ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge8 : 8 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0) (hs : EdgeSupported p KQ6 g)
    (hg : ∀ a b, |g a b| ≤ ε) (hcompat : CompatKQ6 p g) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p KQ6 w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
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
      TernarySymmetric w ∧ TernarySupported p KQ6 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KQ6 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KQ6 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs hcompat (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKQ6 p d, vertexWeightKQ6_symmetric p d,
        vertexWeightKQ6_supported p d, vertexWeightKQ6_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightKQ6_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKQ6 p f, zeroRowWeightKQ6_symmetric p f hf,
        zeroRowWeightKQ6_supported p f,
        zeroRowWeightKQ6_load p f hf hr hfd hfs hm hm2 hm4, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightKQ6_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge8 hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- The span compatibility of `CompleteInverseCert₈` gives the real compatibility of `KQ6`. -/
theorem compatKQ6_of_span (p : V → Fin 4) (r : Sym2 V → ℝ) (h : SpanCompat p KQ6 r) :
    CompatKQ6 p (fun a b => r s(a, b)) := by
  obtain ⟨c, hc⟩ := h
  have e := fun i j => congrFun (congrFun hc i) j
  have e00 := e 0 0; have e01 := e 0 1; have e11 := e 1 1; have e22 := e 2 2; have e23 := e 2 3; have e33 := e 3 3
  simp (config := {decide := true}) only [KQ6, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    sum_insert, mem_insert, mem_singleton, sum_singleton, typeEdgeVec] at e00 e01 e11 e22 e23 e33
  simp (config := {decide := true}) at e00 e01 e11 e22 e23 e33
  unfold CompatKQ6
  linarith

/-- **`CompleteInverseCert₈ KQ6`** (with the charge compatibility). -/
theorem completeInverseCert₈_KQ6 : CompleteInverseCert₈ KQ6 := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hspan
  have hsE : EdgeSupported p KQ6 (fun a b => r s(a, b)) := fun a b hab =>
    hs.edgeSupported a b hab
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := ternaryInverse₈_KQ6 V p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hsE
    (fun a b => hr s(a, b)) (compatKQ6_of_span p r hspan)
  have htwF : TernarySupported p KQ6 w := htw
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p KQ6 w hsw htwF _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p KQ6 (activeCompleteGraph p KQ6) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p KQ6 (activeCompleteGraph p KQ6) z,
    copyRestriction_supported p KQ6 (activeCompleteGraph p KQ6) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p KQ6 (activeCompleteGraph p KQ6) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p KQ6 (activeCompleteGraph p KQ6) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

end PaddedComponents

#print axioms PaddedComponents.completeInverseCert₈_KQ6
