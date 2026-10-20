/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Defs

@[expose] public section

/-!
# The bounded signed inverse for `FM16 = {000 001 002 012 111 112 333}` (classes of size at least 8)

Generated stage data (see `PROOF_CHARGE_COMPONENTS_20261013.md`): totals from the types
`000 001 002 111 112` and `333`; vertex rows from repeated, singleton, tripartite and monochromatic
vertex modes; zero rows from internal, repeated and tripartite pair modes and the monochromatic
zero-row mode of the isolated class `3`.
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

def realMatrixFM16 (t00 t01 t02 t11 t12 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, t12, 0], ![t02, t12, 0, 0], ![0, 0, 0, t33]]

theorem classTotal_realMatrixFM16 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p FM16 g) :
    classTotal p g = realMatrixFM16 (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 1 2) (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p FM16 g hs 0 3 (by unfold Link FM16; decide)
  have h13 := classTotal_zero_of_inactive p FM16 g hs 1 3 (by unfold Link FM16; decide)
  have h22 := classTotal_zero_of_inactive p FM16 g hs 2 2 (by unfold Link FM16; decide)
  have h23 := classTotal_zero_of_inactive p FM16 g hs 2 3 (by unfold Link FM16; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixFM16, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h13, h22, h23]

def typeWeightFM16 (p : V → Fin 4) (z000 z001 z002 z111 z112 z333 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  monoTypeWeight p 1 z111 a b c +
  repeatedTypeWeight p 1 2 z112 a b c +
  monoTypeWeight p 3 z333 a b c

theorem typeWeightFM16_symmetric (p : V → Fin 4) (z000 z001 z002 z111 z112 z333 : ℝ) :
    TernarySymmetric (typeWeightFM16 p z000 z001 z002 z111 z112 z333) := by
  unfold typeWeightFM16
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem typeWeightFM16_supported (p : V → Fin 4) (z000 z001 z002 z111 z112 z333 : ℝ) :
    TernarySupported p FM16 (typeWeightFM16 p z000 z001 z002 z111 z112 z333) := by
  unfold typeWeightFM16
  repeat' first
    | exact monoTypeWeight_supported p FM16 _ (by unfold Link FM16; decide) _
    | exact aabLift_supported p FM16 _ _ (by decide) (by unfold Link FM16; decide) _
    | exact abcLift_supported p FM16 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link FM16; decide) _
    | apply TernarySupported.add

theorem typeWeightFM16_totals (p : V → Fin 4) (z000 z001 z002 z111 z112 z333 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightFM16 p z000 z001 z002 z111 z112 z333)) =
      realMatrixFM16 (6 * z000 + 2 * z001 + 2 * z002) (2 * z001) (2 * z002) (6 * z111 + 2 * z112) (2 * z112) (6 * z333) := by
  funext i j
  unfold typeWeightFM16
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [realMatrixFM16] <;> ring

theorem typeWeightFM16_bound (p : V → Fin 4) (z000 z001 z002 z111 z112 z333 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz000 : |z000| ≤ 2 * E) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz111 : |z111| ≤ 2 * E) (hz112 : |z112| ≤ 8 * E) (hz333 : |z333| ≤ 2 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightFM16 p z000 z001 z002 z111 z112 z333 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightFM16_supported p z000 z001 z002 z111 z112 z333
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p FM16 a b c := by
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
  have e3 := mono_normalizer_bound p 1 z111 E δ hE hδ hz111 hm
  have e4 := repeatedType_normalizer_bound p 1 2 z112 E δ hE hδ hz112 hm
  have e5 := mono_normalizer_bound p 3 z333 E δ hE hδ hz333 hm
  dsimp only [typeWeightFM16, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
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
    | exact hM

theorem exists_type_correction_FM16 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p FM16 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p FM16 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b12 := abs_le.mp (hbound 1 2)
  have b33 := abs_le.mp (hbound 3 3)
  let z000 : ℝ := (1 / 6 : ℝ) * classTotal p g 0 0 + (-1 / 6 : ℝ) * classTotal p g 0 1 + (-1 / 6 : ℝ) * classTotal p g 0 2
  let z001 : ℝ := (1 / 2 : ℝ) * classTotal p g 0 1
  let z002 : ℝ := (1 / 2 : ℝ) * classTotal p g 0 2
  let z111 : ℝ := (1 / 6 : ℝ) * classTotal p g 1 1 + (-1 / 6 : ℝ) * classTotal p g 1 2
  let z112 : ℝ := (1 / 2 : ℝ) * classTotal p g 1 2
  let z333 : ℝ := (1 / 6 : ℝ) * classTotal p g 3 3
  have hz000 : |z000| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z000] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz111 : |z111| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z111] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz112 : |z112| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z112] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz333 : |z333| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z333] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightFM16 p z000 z001 z002 z111 z112 z333, typeWeightFM16_symmetric p _ _ _ _ _ _,
    typeWeightFM16_supported p _ _ _ _ _ _, ?_,
    typeWeightFM16_bound p _ _ _ _ _ _ E δ hE hδ hz000 hz001 hz002 hz111 hz112 hz333 hm⟩
  rw [typeWeightFM16_totals p _ _ _ _ _ _ hn hn1 hn2, classTotal_realMatrixFM16 p g hsym hs]
  congr 1 <;> dsimp only [z000, z001, z002, z111, z112, z333] <;> ring

def vertexWeightFM16 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  monoVertexWeight p 3 (lc d 0 0 0 1) a b c +
  repeatedVertexWeight p 0 1 (lc d (1 / 2) (1 / 2) (-1 / 2) 0) a b c +
  repeatedVertexWeight p 0 2 (lc d (1 / 2) (-1 / 2) (1 / 2) 0) a b c +
  tripartiteVertexWeight p 0 1 2 (lc d (-1 / 2) (1 / 2) (1 / 2) 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (1 / 2) (-1 / 2) 0) a b c +
  repeatedVertexWeight p 1 2 (lc d 0 1 0 0) a b c +
  tripartiteVertexWeight p 1 0 2 (lc d 0 (-1) 1 0) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) 0 0 0) a b c +
  singletonVertexWeight p 1 2 (lc d 0 (1 / 2) 0 0) a b c

theorem vertexWeightFM16_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightFM16 p d) := by
  unfold vertexWeightFM16
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem vertexWeightFM16_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p FM16 (vertexWeightFM16 p d) := by
  unfold vertexWeightFM16
  repeat' first
    | exact monoVertexWeight_supported p FM16 _ (by unfold Link FM16; decide) _
    | exact aabLift_supported p FM16 _ _ (by decide) (by unfold Link FM16; decide) _
    | exact abcLift_supported p FM16 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link FM16; decide) _
    | apply TernarySupported.add

theorem vertexWeightFM16_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p FM16 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightFM16 p d)) a k = d a k := by
  unfold vertexWeightFM16
  simp only [classRow_ternary_add]
  simp only [monoVertexWeight_rows p 3 _ (lc_sum_zero p d hz 0 0 0 1 3) (hm2 3) (hm3 3),
    repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (1 / 2) (-1 / 2) 0 0) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) (1 / 2) 0 0) (hm2 0) (hm 2),
    tripartiteVertexWeight_rows p 0 1 2 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) (1 / 2) 0 0) (hm 1) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (1 / 2) (-1 / 2) 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 1 2 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm 2),
    tripartiteVertexWeight_rows p 1 0 2 _ (lc_sum_zero p d hz 0 (-1) 1 0 1) (hm 0) (hm 2),
    singletonVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) 0 0 0 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 1 2 _ (lc_sum_zero p d hz 0 (1 / 2) 0 0 2) (hm 1) (hm1 1)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link FM16; decide)).symm
    | ring

theorem vertexWeightFM16_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightFM16 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have hmo (i : Fin 4) (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    monoVertexWeight_bound p i f (2 * D) δ h2D hδ hf hm a b c
  have h24 : 24 * (2 * D) / δ ^ 2 = 2 * (12 * (2 * D) / δ ^ 2) := by ring
  have e0 := hmo 3 (lc d 0 0 0 1) (lc_bound_two d D hD hd 0 0 0 1 (by norm_num))
  have e1 := (hb (lc d (1 / 2) (1 / 2) (-1 / 2) 0) (lc_bound_two d D hD hd (1 / 2) (1 / 2) (-1 / 2) 0 (by norm_num))).1 0 1
  have e2 := (hb (lc d (1 / 2) (-1 / 2) (1 / 2) 0) (lc_bound_two d D hD hd (1 / 2) (-1 / 2) (1 / 2) 0 (by norm_num))).1 0 2
  have e3 := (hb (lc d (-1 / 2) (1 / 2) (1 / 2) 0) (lc_bound_two d D hD hd (-1 / 2) (1 / 2) (1 / 2) 0 (by norm_num))).2.2 0 1 2
  have e4 := (hb (lc d (1 / 2) (1 / 2) (-1 / 2) 0) (lc_bound_two d D hD hd (1 / 2) (1 / 2) (-1 / 2) 0 (by norm_num))).2.1 0 1
  have e5 := (hb (lc d 0 1 0 0) (lc_bound_two d D hD hd 0 1 0 0 (by norm_num))).1 1 2
  have e6 := (hb (lc d 0 (-1) 1 0) (lc_bound_two d D hD hd 0 (-1) 1 0 (by norm_num))).2.2 1 0 2
  have e7 := (hb (lc d (1 / 2) 0 0 0) (lc_bound_two d D hD hd (1 / 2) 0 0 0 (by norm_num))).2.1 0 2
  have e8 := (hb (lc d 0 (1 / 2) 0 0) (lc_bound_two d D hD hd 0 (1 / 2) 0 0 (by norm_num))).2.1 1 2
  rw [h24] at e0
  have hMpos : 0 ≤ 12 * (2 * D) / δ ^ 2 := by positivity
  unfold vertexWeightFM16
  have hM288 : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * (2 * D) / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 hMpos ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2]

def zeroRowWeightFM16 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  monoPairWeight p 3 g a b c +
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  internalPairWeight p 1 2 g a b c +
  repeatedPairWeight p 1 2 g a b c

theorem zeroRowWeightFM16_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightFM16 p g) := by
  unfold zeroRowWeightFM16
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | exact monoPairWeight_symmetric p _ g hs
    | apply TernarySymmetric.add

theorem zeroRowWeightFM16_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p FM16 (zeroRowWeightFM16 p g) := by
  unfold zeroRowWeightFM16
  repeat' first
    | exact monoPairWeight_supported p FM16 _ (by unfold Link FM16; decide) _
    | exact aabLift_supported p FM16 _ _ (by decide) (by unfold Link FM16; decide) _
    | exact abcLift_supported p FM16 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link FM16; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightFM16_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link FM16 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0)
    (hm4 : ∀ i, classSize p i - 4 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightFM16 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  have hmono := fun i a b => monoPairWeight_load p i g hs hr hd (hm4 i) a b
  unfold zeroRowWeightFM16
  simp only [ternaryLoad_add, hint, hrep, htri, hmono]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link FM16; decide)).symm

theorem zeroRowWeightFM16_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightFM16 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε (by linarith) hg hm a b c
  have h0 := monoPairWeight_bound p 3 g ε δ hε hδ hg hm a b c
  have h1 := hi 0 1
  have h2 := hr 0 1
  have h3 := hr 0 2
  have h4 := hi 1 2
  have h5 := hr 1 2
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 hpos ⊢
  unfold zeroRowWeightFM16
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-- **The ternary bounded signed inverse for `FM16` (classes of size at least 8).** -/
theorem ternaryInverse₈_FM16 : TernaryInverse₈ FM16 := by
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
      TernarySymmetric w ∧ TernarySupported p FM16 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p FM16 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_FM16 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightFM16 p d, vertexWeightFM16_symmetric p d,
        vertexWeightFM16_supported p d, vertexWeightFM16_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightFM16_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightFM16 p f, zeroRowWeightFM16_symmetric p f hf,
        zeroRowWeightFM16_supported p f,
        zeroRowWeightFM16_load p f hf hr hfd hfs hm hm2 hm4, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightFM16_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge8 hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert₈ FM16`.** -/
theorem completeInverseCert₈_FM16 : CompleteInverseCert₈ FM16 :=
  completeInverseCert₈_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse₈_FM16

end PaddedComponents

#print axioms PaddedComponents.completeInverseCert₈_FM16
