/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ChargeFamilies

@[expose] public section

/-!
# The bounded signed inverse for `KCb`

Types: 001 002 011 022 113 (rank 5 in the 6 allowed coordinates 00 01 02 11 13 22). The `FnoC`
inverse with `133` removed: the totals span the hyperplane `T00 - T01 - T02 + T11 - T13 + T22 = 0`
(`CompatKCb`, the real form of the charge), derived from `SpanCompat` by `compatKCb_of_span`. Class 3
has the single active column 1, served by the singleton vertex mode of type 113. Same bound
`2^20 ε/(γ^6 n)`.
-/

noncomputable section

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedFstar PaddedF12 PaddedGeneral PaddedNoCommon

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

def realMatrixKCb (t00 t01 t02 t11 t13 t22 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, 0, t13], ![t02, 0, t22, 0], ![0, t13, 0, 0]]

theorem classTotal_realMatrixKCb (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KCb g) :
    classTotal p g = realMatrixKCb (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 1 3) (classTotal p g 2 2) := by
  have h03 := classTotal_zero_of_inactive p KCb g hs 0 3 (by unfold Link KCb; decide)
  have h12 := classTotal_zero_of_inactive p KCb g hs 1 2 (by unfold Link KCb; decide)
  have h23 := classTotal_zero_of_inactive p KCb g hs 2 3 (by unfold Link KCb; decide)
  have h33 := classTotal_zero_of_inactive p KCb g hs 3 3 (by unfold Link KCb; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKCb, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1, classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h12, h23, h33]

def typeWeightKCb (p : V → Fin 4) (z001 z002 z011 z022 z113 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  repeatedTypeWeight p 2 0 z022 a b c +
  repeatedTypeWeight p 1 3 z113 a b c

theorem typeWeightKCb_symmetric (p : V → Fin 4) (z001 z002 z011 z022 z113 : ℝ) :
    TernarySymmetric (typeWeightKCb p z001 z002 z011 z022 z113) := by
  unfold typeWeightKCb
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact repeatedTypeWeight_symmetric p _ _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem typeWeightKCb_supported (p : V → Fin 4) (z001 z002 z011 z022 z113 : ℝ) :
    TernarySupported p KCb (typeWeightKCb p z001 z002 z011 z022 z113) := by
  unfold typeWeightKCb
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact aabLift_supported p KCb _ _ (by decide) (by unfold Link KCb; decide) _
    | apply TernarySupported.add

theorem typeWeightKCb_totals (p : V → Fin 4) (z001 z002 z011 z022 z113 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKCb p z001 z002 z011 z022 z113)) =
      realMatrixKCb (2 * z001 + 2 * z002) (2 * z001 + 2 * z011) (2 * z002 + 2 * z022) (2 * z011 + 2 * z113) (2 * z113) (2 * z022) := by
  funext i j
  unfold typeWeightKCb
  simp only [classTotal_ternary_add]
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  simp only [ht]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKCb] <;> ring

theorem typeWeightKCb_bound (p : V → Fin 4) (z001 z002 z011 z022 z113 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz022 : |z022| ≤ 8 * E) (hz113 : |z113| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKCb p z001 z002 z011 z022 z113 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKCb_supported p z001 z002 z011 z022 z113
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KCb a b c := by
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
  have e1 := repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ hz001 hm
  have e2 := repeatedType_normalizer_bound p 0 2 z002 E δ hE hδ hz002 hm
  have e3 := repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ hz011 hm
  have e4 := repeatedType_normalizer_bound p 2 0 z022 E δ hE hδ hz022 hm
  have e5 := repeatedType_normalizer_bound p 1 3 z113 E δ hE hδ hz113 hm
  dsimp only [typeWeightKCb, repeatedTypeWeight, aabLift, pairSymmetrize, aabBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact e1
    | exact e2
    | exact e3
    | exact e4
    | exact e5
    | exact hM

/-- The real compatibility of `KCb` on class totals (the charge vanishes on the totals). -/
def CompatKCb (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  1 * classTotal p g 0 0 + (-1) * classTotal p g 0 1 + (-1) * classTotal p g 0 2 + 1 * classTotal p g 1 1 + (-1) * classTotal p g 1 3 + 1 * classTotal p g 2 2 = 0

theorem exists_type_correction_KCb (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KCb g)
    (hcompat : CompatKCb p g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KCb w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  unfold CompatKCb at hcompat
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b13 := abs_le.mp (hbound 1 3)
  have b22 := abs_le.mp (hbound 2 2)
  let z001 : ℝ := (1 / 2) * classTotal p g 0 1 + (-1 / 2) * classTotal p g 1 1 + (1 / 2) * classTotal p g 1 3
  let z002 : ℝ := (1 / 2) * classTotal p g 0 2 + (-1 / 2) * classTotal p g 2 2
  let z011 : ℝ := (1 / 2) * classTotal p g 1 1 + (-1 / 2) * classTotal p g 1 3
  let z022 : ℝ := (1 / 2) * classTotal p g 2 2
  let z113 : ℝ := (1 / 2) * classTotal p g 1 3
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b13.1, b13.2, b22.1, b22.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b13.1, b13.2, b22.1, b22.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b13.1, b13.2, b22.1, b22.2]
  have hz022 : |z022| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z022] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b13.1, b13.2, b22.1, b22.2]
  have hz113 : |z113| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z113] <;> linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b13.1, b13.2, b22.1, b22.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKCb p z001 z002 z011 z022 z113, typeWeightKCb_symmetric p _ _ _ _ _,
    typeWeightKCb_supported p _ _ _ _ _, ?_,
    typeWeightKCb_bound p _ _ _ _ _ E δ hE hδ hz001 hz002 hz011 hz022 hz113 hm⟩
  rw [typeWeightKCb_totals p _ _ _ _ _ hn hn1, classTotal_realMatrixKCb p g hsym hs]
  congr 1 <;> dsimp only [z001, z002, z011, z022, z113] <;> linarith

def vertexWeightKCb (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 (-1) 0) a b c +
  repeatedVertexWeight p 0 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) (1 / 2) 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 (-1)) a b c +
  repeatedVertexWeight p 1 3 (lc d 0 0 0 1) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) 0 (1 / 2)) a b c +
  repeatedVertexWeight p 2 0 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) 0 (-1 / 2) 0) a b c +
  singletonVertexWeight p 1 3 (lc d 0 (1 / 2) 0 0) a b c

theorem vertexWeightKCb_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKCb p d) := by
  unfold vertexWeightKCb
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact repeatedVertexWeight_symmetric p _ _ _
    | with_reducible exact singletonVertexWeight_symmetric p _ _ _
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem vertexWeightKCb_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KCb (vertexWeightKCb p d) := by
  unfold vertexWeightKCb
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact aabLift_supported p KCb _ _ (by decide) (by unfold Link KCb; decide) _
    | apply TernarySupported.add

theorem vertexWeightKCb_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KCb d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKCb p d)) a k = d a k := by
  unfold vertexWeightKCb
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 1 0 (-1) 0 0) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz 0 0 1 0 0) (hm2 0) (hm 2),
    singletonVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) (1 / 2) 0 0) (hm 1) (hm1 1),
    repeatedVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz 0 1 0 (-1) 1) (hm2 1) (hm 0),
    repeatedVertexWeight_rows p 1 3 _ (lc_sum_zero p d hz 0 0 0 1 1) (hm2 1) (hm 3),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) 0 (1 / 2) 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 2 0 _ (lc_sum_zero p d hz 0 0 1 0 2) (hm2 2) (hm 0),
    singletonVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) 0 (-1 / 2) 0 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 1 3 _ (lc_sum_zero p d hz 0 (1 / 2) 0 0 3) (hm 1) (hm1 1)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KCb; decide)).symm
    | ring

theorem vertexWeightKCb_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKCb p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have e0 := (hb (lc d 1 0 (-1) 0) (lc_bound_two d D hD hd 1 0 (-1) 0 (by norm_num))).1 0 1
  have e1 := (hb (lc d 0 0 1 0) (lc_bound_two d D hD hd 0 0 1 0 (by norm_num))).1 0 2
  have e2 := (hb (lc d (-1 / 2) (1 / 2) (1 / 2) 0) (lc_bound_two d D hD hd (-1 / 2) (1 / 2) (1 / 2) 0 (by norm_num))).2.1 1 0
  have e3 := (hb (lc d 0 1 0 (-1)) (lc_bound_two d D hD hd 0 1 0 (-1) (by norm_num))).1 1 0
  have e4 := (hb (lc d 0 0 0 1) (lc_bound_two d D hD hd 0 0 0 1 (by norm_num))).1 1 3
  have e5 := (hb (lc d (1 / 2) (-1 / 2) 0 (1 / 2)) (lc_bound_two d D hD hd (1 / 2) (-1 / 2) 0 (1 / 2) (by norm_num))).2.1 0 1
  have e6 := (hb (lc d 0 0 1 0) (lc_bound_two d D hD hd 0 0 1 0 (by norm_num))).1 2 0
  have e7 := (hb (lc d (1 / 2) 0 (-1 / 2) 0) (lc_bound_two d D hD hd (1 / 2) 0 (-1 / 2) 0 (by norm_num))).2.1 0 2
  have e8 := (hb (lc d 0 (1 / 2) 0 0) (lc_bound_two d D hD hd 0 (1 / 2) 0 0 (by norm_num))).2.1 1 3
  have hMpos : 0 ≤ 12 * (2 * D) / δ ^ 2 := by positivity
  unfold vertexWeightKCb
  have hM288 : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * (2 * D) / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 hMpos ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2]

def zeroRowWeightKCb (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  internalPairWeight p 1 0 g a b c +
  internalPairWeight p 2 0 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  repeatedPairWeight p 1 3 g a b c

theorem zeroRowWeightKCb_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (zeroRowWeightKCb p g) := by
  unfold zeroRowWeightKCb
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact internalPairWeight_symmetric p _ _ g hs
    | with_reducible exact repeatedPairWeight_symmetric p _ _ g
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | apply TernarySymmetric.add

theorem zeroRowWeightKCb_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KCb (zeroRowWeightKCb p g) := by
  unfold zeroRowWeightKCb
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact aabLift_supported p KCb _ _ (by decide) (by unfold Link KCb; decide) _
    | apply TernarySupported.add

theorem zeroRowWeightKCb_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KCb (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (zeroRowWeightKCb p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  unfold zeroRowWeightKCb
  simp only [ternaryLoad_add, hint, hrep]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KCb; decide)).symm

theorem zeroRowWeightKCb_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |zeroRowWeightKCb p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, -⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hi 1 0
  have h2 := hi 2 0
  have h3 := hr 0 1
  have h4 := hr 0 2
  have h5 := hr 1 3
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 hpos ⊢
  unfold zeroRowWeightKCb
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-- **The ternary bounded signed inverse for `KCb`, under the real compatibility.** -/
theorem ternaryInverse_compat_KCb (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (g : V → V → ℝ) (ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0) (hs : EdgeSupported p KCb g)
    (hg : ∀ a b, |g a b| ≤ ε) (hcompat : CompatKCb p g) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p KCb w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
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
      TernarySymmetric w ∧ TernarySupported p KCb w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KCb g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KCb p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs hcompat (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKCb p d, vertexWeightKCb_symmetric p d,
        vertexWeightKCb_supported p d, vertexWeightKCb_rows p d hz hds hm hm1 hm2, ?_⟩
      intro a b c
      exact he1 ▸ vertexWeightKCb_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKCb p f, zeroRowWeightKCb_symmetric p f hf,
        zeroRowWeightKCb_supported p f, zeroRowWeightKCb_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ zeroRowWeightKCb_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- The span compatibility of `CompleteInverseCert` gives the real compatibility of `KCb`. -/
theorem compatKCb_of_span (p : V → Fin 4) (r : Sym2 V → ℝ) (h : SpanCompat p KCb r) :
    CompatKCb p (fun a b => r s(a, b)) := by
  obtain ⟨c, hc⟩ := h
  have e := fun i j => congrFun (congrFun hc i) j
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2; have e11 := e 1 1; have e13 := e 1 3; have e22 := e 2 2
  simp (config := {decide := true}) only [KCb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    sum_insert, mem_insert, mem_singleton, sum_singleton, typeEdgeVec] at e00 e01 e02 e11 e13 e22
  simp (config := {decide := true}) at e00 e01 e02 e11 e13 e22
  unfold CompatKCb
  linarith

/-- **Inverse certificate: `CompleteInverseCert KCb`.** -/
theorem completeInverseCert_KCb : CompleteInverseCert KCb := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hspan
  have hsE : EdgeSupported p KCb (fun a b => r s(a, b)) := fun a b hab =>
    hs.edgeSupported a b hab
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := ternaryInverse_compat_KCb V p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hsE
    (fun a b => hr s(a, b)) (compatKCb_of_span p r hspan)
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p KCb w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p KCb (activeCompleteGraph p KCb) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p KCb (activeCompleteGraph p KCb) z,
    copyRestriction_supported p KCb (activeCompleteGraph p KCb) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p KCb (activeCompleteGraph p KCb) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p KCb (activeCompleteGraph p KCb) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

end PaddedCharge

#print axioms PaddedCharge.completeInverseCert_KCb
