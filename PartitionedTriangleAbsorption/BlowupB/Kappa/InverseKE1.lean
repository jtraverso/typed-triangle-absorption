/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KEFamilies

@[expose] public section

/-!
# The bounded signed inverse for `KE1` (classes of size at least 8)

Same frame as Aristotle's `InverseFMxx` (generator `gen_km.py`): totals from the types
`000` `111` `222` `333`; vertex rows from repeated, singleton, tripartite and monochromatic vertex
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

def realMatrixKE1 (t00 t11 t22 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, 0, 0, 0], ![0, t11, 0, 0], ![0, 0, t22, 0], ![0, 0, 0, t33]]

theorem classTotal_realMatrixKE1 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KE1 g) :
    classTotal p g = realMatrixKE1 (classTotal p g 0 0) (classTotal p g 1 1) (classTotal p g 2 2) (classTotal p g 3 3) := by
  have h01 := classTotal_zero_of_inactive p KE1 g hs 0 1 (by unfold Link KE1; decide)
  have h02 := classTotal_zero_of_inactive p KE1 g hs 0 2 (by unfold Link KE1; decide)
  have h03 := classTotal_zero_of_inactive p KE1 g hs 0 3 (by unfold Link KE1; decide)
  have h12 := classTotal_zero_of_inactive p KE1 g hs 1 2 (by unfold Link KE1; decide)
  have h13 := classTotal_zero_of_inactive p KE1 g hs 1 3 (by unfold Link KE1; decide)
  have h23 := classTotal_zero_of_inactive p KE1 g hs 2 3 (by unfold Link KE1; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKE1, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h01, h02, h03, h12, h13, h23]

def typeWeightKE1 (p : V → Fin 4) (z000 z111 z222 z333 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  monoTypeWeight p 1 z111 a b c +
  monoTypeWeight p 2 z222 a b c +
  monoTypeWeight p 3 z333 a b c

theorem typeWeightKE1_symmetric (p : V → Fin 4) (z000 z111 z222 z333 : ℝ) :
    TernarySymmetric (typeWeightKE1 p z000 z111 z222 z333) := by
  unfold typeWeightKE1
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem typeWeightKE1_supported (p : V → Fin 4) (z000 z111 z222 z333 : ℝ) :
    TernarySupported p KE1 (typeWeightKE1 p z000 z111 z222 z333) := by
  unfold typeWeightKE1
  repeat' first
    | exact monoTypeWeight_supported p KE1 _ (by unfold Link KE1; decide) _
    | exact aabLift_supported p KE1 _ _ (by decide) (by unfold Link KE1; decide) _
    | exact abcLift_supported p KE1 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KE1; decide) _
    | apply TernarySupported.add

theorem typeWeightKE1_totals (p : V → Fin 4) (z000 z111 z222 z333 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKE1 p z000 z111 z222 z333)) =
      realMatrixKE1 (6 * z000) (6 * z111) (6 * z222) (6 * z333) := by
  funext i j
  unfold typeWeightKE1
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKE1] <;> ring

theorem typeWeightKE1_bound (p : V → Fin 4) (z000 z111 z222 z333 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz000 : |z000| ≤ 2 * E) (hz111 : |z111| ≤ 2 * E) (hz222 : |z222| ≤ 2 * E) (hz333 : |z333| ≤ 2 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKE1 p z000 z111 z222 z333 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKE1_supported p z000 z111 z222 z333
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KE1 a b c := by
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
  have e1 := mono_normalizer_bound p 1 z111 E δ hE hδ hz111 hm
  have e2 := mono_normalizer_bound p 2 z222 E δ hE hδ hz222 hm
  have e3 := mono_normalizer_bound p 3 z333 E δ hE hδ hz333 hm
  dsimp only [typeWeightKE1, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
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
    | exact hM

theorem exists_type_correction_KE1 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KE1 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KE1 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b11 := abs_le.mp (hbound 1 1)
  have b22 := abs_le.mp (hbound 2 2)
  have b33 := abs_le.mp (hbound 3 3)
  let z000 : ℝ := (1 / 6) * classTotal p g 0 0
  let z111 : ℝ := (1 / 6) * classTotal p g 1 1
  let z222 : ℝ := (1 / 6) * classTotal p g 2 2
  let z333 : ℝ := (1 / 6) * classTotal p g 3 3
  have hz000 : |z000| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z000] <;>
      linarith [b00.1, b00.2, b11.1, b11.2, b22.1, b22.2, b33.1, b33.2]
  have hz111 : |z111| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z111] <;>
      linarith [b00.1, b00.2, b11.1, b11.2, b22.1, b22.2, b33.1, b33.2]
  have hz222 : |z222| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z222] <;>
      linarith [b00.1, b00.2, b11.1, b11.2, b22.1, b22.2, b33.1, b33.2]
  have hz333 : |z333| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z333] <;>
      linarith [b00.1, b00.2, b11.1, b11.2, b22.1, b22.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKE1 p z000 z111 z222 z333, typeWeightKE1_symmetric p _ _ _ _,
    typeWeightKE1_supported p _ _ _ _, ?_,
    typeWeightKE1_bound p _ _ _ _ E δ hE hδ hz000 hz111 hz222 hz333 hm⟩
  rw [typeWeightKE1_totals p _ _ _ _ hn hn1 hn2, classTotal_realMatrixKE1 p g hsym hs]
  congr 1 <;> dsimp only [z000, z111, z222, z333] <;> ring

def vertexWeightKE1 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  monoVertexWeight p 0 (lc d 1 0 0 0) a b c +
  monoVertexWeight p 1 (lc d 0 1 0 0) a b c +
  monoVertexWeight p 2 (lc d 0 0 1 0) a b c +
  monoVertexWeight p 3 (lc d 0 0 0 1) a b c

theorem vertexWeightKE1_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKE1 p d) := by
  unfold vertexWeightKE1
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem vertexWeightKE1_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KE1 (vertexWeightKE1 p d) := by
  unfold vertexWeightKE1
  repeat' first
    | exact monoVertexWeight_supported p KE1 _ (by unfold Link KE1; decide) _
    | exact aabLift_supported p KE1 _ _ (by decide) (by unfold Link KE1; decide) _
    | exact abcLift_supported p KE1 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KE1; decide) _
    | apply TernarySupported.add

theorem vertexWeightKE1_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KE1 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKE1 p d)) a k = d a k := by
  unfold vertexWeightKE1
  simp only [classRow_ternary_add]
  simp only [monoVertexWeight_rows p 0 _ (lc_sum_zero p d hz 1 0 0 0 0) (hm2 0) (hm3 0),
    monoVertexWeight_rows p 1 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm3 1),
    monoVertexWeight_rows p 2 _ (lc_sum_zero p d hz 0 0 1 0 2) (hm2 2) (hm3 2),
    monoVertexWeight_rows p 3 _ (lc_sum_zero p d hz 0 0 0 1 3) (hm2 3) (hm3 3)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KE1; decide)).symm
    | ring

theorem vertexWeightKE1_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKE1 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hf (a0 a1 a2 a3 m : ℝ) (hm0 : |a0| + |a1| + |a2| + |a3| ≤ m) (v : V) :
      |lc d a0 a1 a2 a3 v| ≤ m * D :=
    (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right hm0 hD)
  have e0 := monoVertexWeight_bound p 0 (lc d 1 0 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 1 0 0 0 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e0
  have e1 := monoVertexWeight_bound p 1 (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e1
  have e2 := monoVertexWeight_bound p 2 (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e2
  have e3 := monoVertexWeight_bound p 3 (lc d 0 0 0 1) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 0 1 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e3
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold vertexWeightKE1
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e0 e1 e2 e3 hM0 ⊢
  rw [abs_le] at e0 e1 e2 e3 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

def zeroRowWeightKE1 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  monoPairWeight p 0 g a b c +
  monoPairWeight p 1 g a b c +
  monoPairWeight p 2 g a b c +
  monoPairWeight p 3 g a b c

theorem zeroRowWeightKE1_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightKE1 p g) := by
  unfold zeroRowWeightKE1
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | exact monoPairWeight_symmetric p _ g hs
    | apply TernarySymmetric.add

theorem zeroRowWeightKE1_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KE1 (zeroRowWeightKE1 p g) := by
  unfold zeroRowWeightKE1
  repeat' first
    | exact monoPairWeight_supported p KE1 _ (by unfold Link KE1; decide) _
    | exact aabLift_supported p KE1 _ _ (by decide) (by unfold Link KE1; decide) _
    | exact abcLift_supported p KE1 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KE1; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightKE1_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KE1 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0)
    (hm4 : ∀ i, classSize p i - 4 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightKE1 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  have hmono := fun i a b => monoPairWeight_load p i g hs hr hd (hm4 i) a b
  unfold zeroRowWeightKE1
  simp only [ternaryLoad_add, hint, hrep, htri, hmono]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KE1; decide)).symm

theorem zeroRowWeightKE1_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightKE1 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε (by linarith) hg hm a b c
  have h0 := monoPairWeight_bound p 0 g ε δ hε hδ hg hm a b c
  have h1 := monoPairWeight_bound p 1 g ε δ hε hδ hg hm a b c
  have h2 := monoPairWeight_bound p 2 g ε δ hε hδ hg hm a b c
  have h3 := monoPairWeight_bound p 3 g ε δ hε hδ hg hm a b c
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 hpos ⊢
  unfold zeroRowWeightKE1
  rw [abs_le] at h0 h1 h2 h3 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The ternary bounded signed inverse for `KE1` (classes of size at least 8).** -/
theorem ternaryInverse₈_KE1 : TernaryInverse₈ KE1 := by
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
      TernarySymmetric w ∧ TernarySupported p KE1 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KE1 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KE1 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKE1 p d, vertexWeightKE1_symmetric p d,
        vertexWeightKE1_supported p d, vertexWeightKE1_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightKE1_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKE1 p f, zeroRowWeightKE1_symmetric p f hf,
        zeroRowWeightKE1_supported p f,
        zeroRowWeightKE1_load p f hf hr hfd hfs hm hm2 hm4, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightKE1_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge8 hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert₈ KE1`.** -/
theorem completeInverseCert₈_KE1 : CompleteInverseCert₈ KE1 :=
  completeInverseCert₈_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse₈_KE1

end PaddedComponents

#print axioms PaddedComponents.completeInverseCert₈_KE1
