/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoVertexMode
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.FamilyB1

@[expose] public section

/-!
# The bounded signed inverse for `FB1 = {000, 001, 222, 223}`

Stages of `exists_complete_inverse_of_stages`:

* **totals.** Allowed pairs `00, 01, 22, 23`; the four type vectors are independent, so no
  compatibility condition is needed: `z001 = t01/2`, `z000 = (t00 - t01)/6` and the same on
  `{2, 3}`;
* **vertex rows.** A class-0 vertex has rows towards `0` and `1`: the repeated mode `(0,1)` with
  input `d·1` moves both, and the new monochromatic vertex mode (`monoVertexWeight`, type `000`)
  corrects row `0` by `d·0 - d·1`. A class-1 vertex has only the row towards `0`, corrected by the
  singleton mode `(0,1)`. The same on `{2, 3}`;
* **zero rows.** Internal pair modes `00 → 001`, `22 → 223` and repeated pair modes for `01`, `23`.

The final bound is the generic `2^20 ε / (γ^6 n)`.
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
set_option maxHeartbeats 4000000

def realMatrixFB1 (t00 t01 t22 t23 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, 0, 0], ![t01, 0, 0, 0], ![0, 0, t22, t23], ![0, 0, t23, 0]]

theorem classTotal_realMatrixFB1 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p FB1 g) :
    classTotal p g = realMatrixFB1 (classTotal p g 0 0) (classTotal p g 0 1)
      (classTotal p g 2 2) (classTotal p g 2 3) := by
  have h02 := classTotal_zero_of_inactive p FB1 g hs 0 2 (by unfold Link FB1; decide)
  have h03 := classTotal_zero_of_inactive p FB1 g hs 0 3 (by unfold Link FB1; decide)
  have h11 := classTotal_zero_of_inactive p FB1 g hs 1 1 (by unfold Link FB1; decide)
  have h12 := classTotal_zero_of_inactive p FB1 g hs 1 2 (by unfold Link FB1; decide)
  have h13 := classTotal_zero_of_inactive p FB1 g hs 1 3 (by unfold Link FB1; decide)
  have h33 := classTotal_zero_of_inactive p FB1 g hs 3 3 (by unfold Link FB1; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixFB1, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2,
      h02, h03, h11, h12, h13, h33]

def typeWeightFB1 (p : V → Fin 4) (z000 z001 z222 z223 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  repeatedTypeWeight p 0 1 z001 a b c +
  monoTypeWeight p 2 z222 a b c +
  repeatedTypeWeight p 2 3 z223 a b c

theorem typeWeightFB1_symmetric (p : V → Fin 4) (z000 z001 z222 z223 : ℝ) :
    TernarySymmetric (typeWeightFB1 p z000 z001 z222 z223) := by
  unfold typeWeightFB1
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem typeWeightFB1_supported (p : V → Fin 4) (z000 z001 z222 z223 : ℝ) :
    TernarySupported p FB1 (typeWeightFB1 p z000 z001 z222 z223) := by
  unfold typeWeightFB1
  repeat' first
    | exact monoTypeWeight_supported p FB1 _ (by unfold Link FB1; decide) _
    | exact aabLift_supported p FB1 _ _ (by decide) (by unfold Link FB1; decide) _
    | apply TernarySupported.add

theorem typeWeightFB1_totals (p : V → Fin 4) (z000 z001 z222 z223 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightFB1 p z000 z001 z222 z223)) =
      realMatrixFB1 (6 * z000 + 2 * z001) (2 * z001) (6 * z222 + 2 * z223) (2 * z223) := by
  funext i j
  unfold typeWeightFB1
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  simp only [hmo, ht]
  fin_cases i <;> fin_cases j <;> simp [realMatrixFB1]

theorem typeWeightFB1_bound (p : V → Fin 4) (z000 z001 z222 z223 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz000 : |z000| ≤ 2 * E) (hz001 : |z001| ≤ 8 * E)
    (hz222 : |z222| ≤ 2 * E) (hz223 : |z223| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightFB1 p z000 z001 z222 z223 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightFB1_supported p z000 z001 z222 z223
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p FB1 a b c := by
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
  have e2 := mono_normalizer_bound p 2 z222 E δ hE hδ hz222 hm
  have e3 := repeatedType_normalizer_bound p 2 3 z223 E δ hE hδ hz223 hm
  dsimp only [typeWeightFB1, monoTypeWeight, repeatedTypeWeight, aabLift, pairSymmetrize, aabBase]
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

theorem exists_type_correction_FB1 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p FB1 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p FB1 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b22 := abs_le.mp (hbound 2 2)
  have b23 := abs_le.mp (hbound 2 3)
  let z000 : ℝ := (1 / 6 : ℝ) * classTotal p g 0 0 + (-1 / 6 : ℝ) * classTotal p g 0 1
  let z001 : ℝ := (1 / 2 : ℝ) * classTotal p g 0 1
  let z222 : ℝ := (1 / 6 : ℝ) * classTotal p g 2 2 + (-1 / 6 : ℝ) * classTotal p g 2 3
  let z223 : ℝ := (1 / 2 : ℝ) * classTotal p g 2 3
  have hz000 : |z000| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z000] <;>
      linarith [b00.1, b00.2, b01.1, b01.2]
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2]
  have hz222 : |z222| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z222] <;>
      linarith [b22.1, b22.2, b23.1, b23.2]
  have hz223 : |z223| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z223] <;>
      linarith [b22.1, b22.2, b23.1, b23.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightFB1 p z000 z001 z222 z223, typeWeightFB1_symmetric p _ _ _ _,
    typeWeightFB1_supported p _ _ _ _, ?_,
    typeWeightFB1_bound p _ _ _ _ E δ hE hδ hz000 hz001 hz222 hz223 hm⟩
  rw [typeWeightFB1_totals p _ _ _ _ hn hn1 hn2, classTotal_realMatrixFB1 p g hsym hs]
  congr 1 <;> dsimp only [z000, z001, z222, z223] <;> ring

def vertexWeightFB1 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 0 1 0 0) a b c +
  monoVertexWeight p 0 (lc d 1 (-1) 0 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) 0 0 0) a b c +
  repeatedVertexWeight p 2 3 (lc d 0 0 0 1) a b c +
  monoVertexWeight p 2 (lc d 0 0 1 (-1)) a b c +
  singletonVertexWeight p 2 3 (lc d 0 0 (1 / 2) 0) a b c

theorem vertexWeightFB1_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightFB1 p d) := by
  unfold vertexWeightFB1
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem vertexWeightFB1_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p FB1 (vertexWeightFB1 p d) := by
  unfold vertexWeightFB1
  repeat' first
    | exact monoVertexWeight_supported p FB1 _ (by unfold Link FB1; decide) _
    | exact aabLift_supported p FB1 _ _ (by decide) (by unfold Link FB1; decide) _
    | apply TernarySupported.add

theorem vertexWeightFB1_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p FB1 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightFB1 p d)) a k = d a k := by
  unfold vertexWeightFB1
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 0 1 0 0 0) (hm2 0) (hm 1),
    monoVertexWeight_rows p 0 _ (lc_sum_zero p d hz 1 (-1) 0 0 0) (hm2 0) (hm3 0),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) 0 0 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 0 1 2) (hm2 2) (hm 3),
    monoVertexWeight_rows p 2 _ (lc_sum_zero p d hz 0 0 1 (-1) 2) (hm2 2) (hm3 2),
    singletonVertexWeight_rows p 2 3 _ (lc_sum_zero p d hz 0 0 (1 / 2) 0 3) (hm 2) (hm1 2)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals exact (hforb (by unfold Link FB1; decide)).symm

theorem vertexWeightFB1_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightFB1 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have hmo (i : Fin 4) (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    monoVertexWeight_bound p i f (2 * D) δ h2D hδ hf hm a b c
  have e0 := (hb (lc d 0 1 0 0) (lc_bound_two d D hD hd 0 1 0 0 (by norm_num))).1 0 1
  have e1 := hmo 0 (lc d 1 (-1) 0 0) (lc_bound_two d D hD hd 1 (-1) 0 0 (by norm_num))
  have e2 := (hb (lc d (1 / 2) 0 0 0) (lc_bound_two d D hD hd (1 / 2) 0 0 0 (by norm_num))).2.1 0 1
  have e3 := (hb (lc d 0 0 0 1) (lc_bound_two d D hD hd 0 0 0 1 (by norm_num))).1 2 3
  have e4 := hmo 2 (lc d 0 0 1 (-1)) (lc_bound_two d D hD hd 0 0 1 (-1) (by norm_num))
  have e5 := (hb (lc d 0 0 (1 / 2) 0) (lc_bound_two d D hD hd 0 0 (1 / 2) 0 (by norm_num))).2.1 2 3
  have hMpos : 0 ≤ 12 * (2 * D) / δ ^ 2 := by positivity
  have h24 : 24 * (2 * D) / δ ^ 2 = 2 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [h24] at e1 e4
  unfold vertexWeightFB1
  have hM288 : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * (2 * D) / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 hMpos ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2,
    e5.1, e5.2]

def zeroRowWeightFB1 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  internalPairWeight p 2 3 g a b c +
  repeatedPairWeight p 2 3 g a b c

theorem zeroRowWeightFB1_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightFB1 p g) := by
  unfold zeroRowWeightFB1
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | apply TernarySymmetric.add

theorem zeroRowWeightFB1_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p FB1 (zeroRowWeightFB1 p g) := by
  unfold zeroRowWeightFB1
  repeat' first
    | exact aabLift_supported p FB1 _ _ (by decide) (by unfold Link FB1; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightFB1_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link FB1 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightFB1 p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  unfold zeroRowWeightFB1
  simp only [ternaryLoad_add, hint, hrep]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link FB1; decide)).symm

theorem zeroRowWeightFB1_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightFB1 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, -⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hr 0 1
  have h2 := hi 2 3
  have h3 := hr 2 3
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 hpos ⊢
  unfold zeroRowWeightFB1
  rw [abs_le] at h0 h1 h2 h3 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The ternary bounded signed inverse for `FB1`.** -/
theorem ternaryInverse_FB1 : TernaryInverse FB1 := by
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
  have hm3 (i : Fin 4) : classSize p i - 3 ≠ 0 := by have := hmin i; linarith
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
      TernarySymmetric w ∧ TernarySupported p FB1 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p FB1 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_FB1 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightFB1 p d, vertexWeightFB1_symmetric p d,
        vertexWeightFB1_supported p d, vertexWeightFB1_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightFB1_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightFB1 p f, zeroRowWeightFB1_symmetric p f hf,
        zeroRowWeightFB1_supported p f, zeroRowWeightFB1_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightFB1_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert FB1`.** -/
theorem completeInverseCert_FB1 : CompleteInverseCert FB1 :=
  completeInverseCert_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse_FB1

end PaddedComponents

#print axioms PaddedComponents.completeInverseCert_FB1
