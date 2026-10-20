/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Universal

@[expose] public section

/-!
# The bounded signed inverse for Fbit

All types of Fbit except `000` are of shape `aab`, so every mode is an `aab` lift (plus the
monochromatic `000` mode `PaddedFstar.monoTypeWeight`). The eight type totals are solved along the
chain `001 – 011 – 113 – 133 – 233 – 223 – 022 – 002` with the kernel parameter `z001 = 0`, then
`000` closes `t00`. Vertex rows use, for each class, two `repeated` and two `singleton` modes
(16 modes, each with demand `≤ D`), zero rows use four internal and four cross modes. The bound
`2^20 ε/(γ^6 n)` of the F₁/F₂ inverse is kept.
-/

noncomputable section

namespace PaddedFbit

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedFstar

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### Stage 1: totals -/

def fbitRealMatrix (t00 t01 t02 t11 t13 t22 t23 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, 0, t13], ![t02, 0, t22, t23], ![0, t13, t23, t33]]

theorem classTotal_fbitRealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Fbit g) :
    classTotal p g = fbitRealMatrix (classTotal p g 0 0) (classTotal p g 0 1)
      (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 1 3) (classTotal p g 2 2)
      (classTotal p g 2 3) (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p Fbit g hs 0 3 (by unfold Link Fbit; decide)
  have h12 := classTotal_zero_of_inactive p Fbit g hs 1 2 (by unfold Link Fbit; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fbitRealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h03, h12]

def fbitTypeWeight (p : V → Fin 4) (zA z001 z002 z011 z022 z113 z133 z223 z233 : ℝ)
    (a b c : V) : ℝ :=
  monoTypeWeight p 0 zA a b c + repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c + repeatedTypeWeight p 1 0 z011 a b c +
  repeatedTypeWeight p 2 0 z022 a b c + repeatedTypeWeight p 1 3 z113 a b c +
  repeatedTypeWeight p 3 1 z133 a b c + repeatedTypeWeight p 2 3 z223 a b c +
  repeatedTypeWeight p 3 2 z233 a b c

theorem fbitTypeWeight_symmetric (p : V → Fin 4) (zA z001 z002 z011 z022 z113 z133 z223 z233 : ℝ) :
    TernarySymmetric (fbitTypeWeight p zA z001 z002 z011 z022 z113 z133 z223 z233) := by
  unfold fbitTypeWeight
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem fbitTypeWeight_supported (p : V → Fin 4)
    (zA z001 z002 z011 z022 z113 z133 z223 z233 : ℝ) :
    TernarySupported p Fbit (fbitTypeWeight p zA z001 z002 z011 z022 z113 z133 z223 z233) := by
  unfold fbitTypeWeight
  repeat' first
    | exact monoTypeWeight_supported p Fbit _ (by unfold Link Fbit; decide) _
    | exact aabLift_supported p Fbit _ _ (by decide) (by unfold Link Fbit; decide) _
    | apply TernarySupported.add

theorem fbitTypeWeight_totals (p : V → Fin 4) (zA z001 z002 z011 z022 z113 z133 z223 z233 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (fbitTypeWeight p zA z001 z002 z011 z022 z113 z133 z223 z233)) =
      fbitRealMatrix (6 * zA + 2 * z001 + 2 * z002) (2 * z001 + 2 * z011) (2 * z002 + 2 * z022)
        (2 * z011 + 2 * z113) (2 * z113 + 2 * z133) (2 * z022 + 2 * z223)
        (2 * z223 + 2 * z233) (2 * z133 + 2 * z233) := by
  funext i j
  unfold fbitTypeWeight
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  simp only [hmo, ht]
  fin_cases i <;> fin_cases j <;> simp [fbitRealMatrix] <;> ring

theorem fbitTypeWeight_bound (p : V → Fin 4) (zA z001 z002 z011 z022 z113 z133 z223 z233 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hzA : |zA| ≤ 2 * E)
    (hz : ∀ z ∈ [z001, z002, z011, z022, z113, z133, z223, z233], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fbitTypeWeight p zA z001 z002 z011 z022 z113 z133 z223 z233 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := fbitTypeWeight_supported p zA z001 z002 z011 z022 z113 z133 z223 z233
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p Fbit a b c := by
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
  have h0 := mono_normalizer_bound p 0 zA E δ hE hδ hzA hm
  have h1 := repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ (hz z001 (by simp)) hm
  have h2 := repeatedType_normalizer_bound p 0 2 z002 E δ hE hδ (hz z002 (by simp)) hm
  have h3 := repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ (hz z011 (by simp)) hm
  have h4 := repeatedType_normalizer_bound p 2 0 z022 E δ hE hδ (hz z022 (by simp)) hm
  have h5 := repeatedType_normalizer_bound p 1 3 z113 E δ hE hδ (hz z113 (by simp)) hm
  have h6 := repeatedType_normalizer_bound p 3 1 z133 E δ hE hδ (hz z133 (by simp)) hm
  have h7 := repeatedType_normalizer_bound p 2 3 z223 E δ hE hδ (hz z223 (by simp)) hm
  have h8 := repeatedType_normalizer_bound p 3 2 z233 E δ hE hδ (hz z233 (by simp)) hm
  dsimp only [fbitTypeWeight, monoTypeWeight, repeatedTypeWeight,
    aabLift, pairSymmetrize, aabBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact h6
    | exact h7
    | exact h8
    | exact hM

theorem exists_type_correction_Fbit (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Fbit g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p Fbit w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b13 := abs_le.mp (hbound 1 3)
  have b22 := abs_le.mp (hbound 2 2)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  let z001 : ℝ := 0
  let z011 := classTotal p g 0 1 / 2
  let z113 := classTotal p g 1 1 / 2 - z011
  let z133 := classTotal p g 1 3 / 2 - z113
  let z233 := classTotal p g 3 3 / 2 - z133
  let z223 := classTotal p g 2 3 / 2 - z233
  let z022 := classTotal p g 2 2 / 2 - z223
  let z002 := classTotal p g 0 2 / 2 - z022
  let zA := (classTotal p g 0 0 - 2 * z002) / 6
  have hzA : |zA| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;>
      dsimp only [zA, z002, z022, z223, z233, z133, z113, z011] <;> linarith
  have hz : ∀ z ∈ [z001, z002, z011, z022, z113, z133, z223, z233], |z| ≤ 8 * E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;>
      dsimp only [z001, z002, z022, z223, z233, z133, z113, z011] <;> linarith
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨fbitTypeWeight p zA z001 z002 z011 z022 z113 z133 z223 z233,
    fbitTypeWeight_symmetric p _ _ _ _ _ _ _ _ _,
    fbitTypeWeight_supported p _ _ _ _ _ _ _ _ _, ?_,
    fbitTypeWeight_bound p _ _ _ _ _ _ _ _ _ E δ hE hδ hzA hz hm⟩
  rw [fbitTypeWeight_totals p _ _ _ _ _ _ _ _ _ hn hn1 hn2,
    classTotal_fbitRealMatrix p g hsym hs]
  congr 1 <;> dsimp only [zA, z001, z002, z022, z223, z233, z133, z113, z011] <;> ring

/-! ### Stage 2: vertex rows -/

def fbitVertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  -- class 0: rows toward 0, 1, 2
  repeatedVertexWeight p 0 1 (fun v => d v 0 / 2) a b c +
  repeatedVertexWeight p 0 2 (fun v => d v 0 / 2) a b c +
  singletonVertexWeight p 1 0 (fun v => (d v 1 - d v 0 / 2) / 2) a b c +
  singletonVertexWeight p 2 0 (fun v => (d v 2 - d v 0 / 2) / 2) a b c +
  -- class 1: rows toward 0, 1, 3
  repeatedVertexWeight p 1 0 (fun v => d v 1 / 2) a b c +
  repeatedVertexWeight p 1 3 (fun v => d v 1 / 2) a b c +
  singletonVertexWeight p 0 1 (fun v => (d v 0 - d v 1 / 2) / 2) a b c +
  singletonVertexWeight p 3 1 (fun v => (d v 3 - d v 1 / 2) / 2) a b c +
  -- class 2: rows toward 0, 2, 3
  repeatedVertexWeight p 2 0 (fun v => d v 2 / 2) a b c +
  repeatedVertexWeight p 2 3 (fun v => d v 2 / 2) a b c +
  singletonVertexWeight p 0 2 (fun v => (d v 0 - d v 2 / 2) / 2) a b c +
  singletonVertexWeight p 3 2 (fun v => (d v 3 - d v 2 / 2) / 2) a b c +
  -- class 3: rows toward 1, 2, 3
  repeatedVertexWeight p 3 1 (fun v => d v 3 / 2) a b c +
  repeatedVertexWeight p 3 2 (fun v => d v 3 / 2) a b c +
  singletonVertexWeight p 1 3 (fun v => (d v 1 - d v 3 / 2) / 2) a b c +
  singletonVertexWeight p 2 3 (fun v => (d v 2 - d v 3 / 2) / 2) a b c

theorem fbitVertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (fbitVertexWeight p d) := by
  unfold fbitVertexWeight
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem fbitVertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p Fbit (fbitVertexWeight p d) := by
  unfold fbitVertexWeight
  repeat' first
    | exact aabLift_supported p Fbit _ _ (by decide) (by unfold Link Fbit; decide) _
    | apply TernarySupported.add

theorem fbitVertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p Fbit d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (fbitVertexWeight p d)) a k = d a k := by
  unfold VertexDemandZero at hz
  have z1 : ∀ (i x : Fin 4), (∑ v ∈ classVertices p i, d v x / 2) = 0 := by
    intro i x; rw [← sum_div, hz, zero_div]
  have z4 : ∀ (i x y : Fin 4), (∑ v ∈ classVertices p i, (d v x - d v y / 2) / 2) = 0 := by
    intro i x y
    rw [← sum_div, sum_sub_distrib, ← sum_div, hz, hz, zero_div, sub_zero, zero_div]
  unfold fbitVertexWeight
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (z1 0 0) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (z1 0 0) (hm2 0) (hm 2),
    singletonVertexWeight_rows p 1 0 _ (z4 0 1 0) (hm 1) (hm1 1),
    singletonVertexWeight_rows p 2 0 _ (z4 0 2 0) (hm 2) (hm1 2),
    repeatedVertexWeight_rows p 1 0 _ (z1 1 1) (hm2 1) (hm 0),
    repeatedVertexWeight_rows p 1 3 _ (z1 1 1) (hm2 1) (hm 3),
    singletonVertexWeight_rows p 0 1 _ (z4 1 0 1) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 3 1 _ (z4 1 3 1) (hm 3) (hm1 3),
    repeatedVertexWeight_rows p 2 0 _ (z1 2 2) (hm2 2) (hm 0),
    repeatedVertexWeight_rows p 2 3 _ (z1 2 2) (hm2 2) (hm 3),
    singletonVertexWeight_rows p 0 2 _ (z4 2 0 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 3 2 _ (z4 2 3 2) (hm 3) (hm1 3),
    repeatedVertexWeight_rows p 3 1 _ (z1 3 3) (hm2 3) (hm 1),
    repeatedVertexWeight_rows p 3 2 _ (z1 3 3) (hm2 3) (hm 2),
    singletonVertexWeight_rows p 1 3 _ (z4 3 1 3) (hm 1) (hm1 1),
    singletonVertexWeight_rows p 2 3 _ (z4 3 2 3) (hm 2) (hm1 2)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp
  all_goals first
    | exact (hforb (by unfold Link Fbit; decide)).symm
    | ring

theorem fbitVertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fbitVertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ D) := vertexMode_bounds p f D δ hD hδ hf hm a b c
  have hhalf (v : V) (x : Fin 4) : |d v x / 2| ≤ D := by
    rw [abs_div, abs_two]; have := hd v x; have := abs_nonneg (d v x); linarith
  have hmix (v : V) (x y : Fin 4) : |(d v x - d v y / 2) / 2| ≤ D := by
    have hx := abs_le.mp (hd v x)
    have hy := abs_le.mp (hd v y)
    apply abs_le.mpr; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have e1 := (hb _ (fun v => hhalf v 0)).1 0 1
  have e2 := (hb _ (fun v => hhalf v 0)).1 0 2
  have e3 := (hb _ (fun v => hmix v 1 0)).2.1 1 0
  have e4 := (hb _ (fun v => hmix v 2 0)).2.1 2 0
  have e5 := (hb _ (fun v => hhalf v 1)).1 1 0
  have e6 := (hb _ (fun v => hhalf v 1)).1 1 3
  have e7 := (hb _ (fun v => hmix v 0 1)).2.1 0 1
  have e8 := (hb _ (fun v => hmix v 3 1)).2.1 3 1
  have e9 := (hb _ (fun v => hhalf v 2)).1 2 0
  have e10 := (hb _ (fun v => hhalf v 2)).1 2 3
  have e11 := (hb _ (fun v => hmix v 0 2)).2.1 0 2
  have e12 := (hb _ (fun v => hmix v 3 2)).2.1 3 2
  have e13 := (hb _ (fun v => hhalf v 3)).1 3 1
  have e14 := (hb _ (fun v => hhalf v 3)).1 3 2
  have e15 := (hb _ (fun v => hmix v 1 3)).2.1 1 3
  have e16 := (hb _ (fun v => hmix v 2 3)).2.1 2 3
  have hMpos : 0 ≤ 12 * D / δ ^ 2 := by positivity
  unfold fbitVertexWeight
  have hM288 : 288 * D / δ ^ 2 = 24 * (12 * D / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * D / δ ^ 2 = M at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 hMpos ⊢
  rw [abs_le] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2,
    e6.1, e6.2, e7.1, e7.2, e8.1, e8.2, e9.1, e9.2, e10.1, e10.2, e11.1, e11.2, e12.1, e12.2,
    e13.1, e13.2, e14.1, e14.2, e15.1, e15.2, e16.1, e16.2]

/-! ### Stage 3: zero rows -/

def fbitZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c + internalPairWeight p 1 0 g a b c +
  internalPairWeight p 2 0 g a b c + internalPairWeight p 3 1 g a b c +
  repeatedPairWeight p 0 1 g a b c + repeatedPairWeight p 0 2 g a b c +
  repeatedPairWeight p 1 3 g a b c + repeatedPairWeight p 2 3 g a b c

theorem fbitZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (fbitZeroRowWeight p g) := by
  unfold fbitZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | apply TernarySymmetric.add

theorem fbitZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p Fbit (fbitZeroRowWeight p g) := by
  unfold fbitZeroRowWeight
  repeat' first
    | exact aabLift_supported p Fbit _ _ (by decide) (by unfold Link Fbit; decide) _
    | apply TernarySupported.add

theorem fbitZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link Fbit (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (fbitZeroRowWeight p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  unfold fbitZeroRowWeight
  simp only [ternaryLoad_add, hint, hrep]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link Fbit; decide)).symm

theorem fbitZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fbitZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, -⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hi 1 0
  have h2 := hi 2 0
  have h3 := hi 3 1
  have h4 := hr 0 1
  have h5 := hr 0 2
  have h6 := hr 1 3
  have h7 := hr 2 3
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 h7 hpos ⊢
  unfold fbitZeroRowWeight
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2,
    h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

/-! ### The complete inverse and the certificate -/

theorem exists_complete_inverse_Fbit (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p Fbit g) (hg : ∀ a b, |g a b| ≤ ε) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p Fbit w ∧
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
      TernarySymmetric w ∧ TernarySupported p Fbit w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p Fbit g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_Fbit p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨fbitVertexWeight p d, fbitVertexWeight_symmetric p d,
        fbitVertexWeight_supported p d, fbitVertexWeight_rows p d hz hds hm hm1 hm2, ?_⟩
      intro a b c
      exact he1 ▸ fbitVertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨fbitZeroRowWeight p f, fbitZeroRowWeight_symmetric p f hf,
        fbitZeroRowWeight_supported p f, fbitZeroRowWeight_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ fbitZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert Fbit`** (no compatibility condition is needed). -/
theorem completeInverseCert_Fbit : PaddedGeneral.CompleteInverseCert Fbit := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_Fbit p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hs.edgeSupported
    (fun a b => hr s(a, b))
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p Fbit w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p Fbit (activeCompleteGraph p Fbit) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p Fbit (activeCompleteGraph p Fbit) z,
    copyRestriction_supported p Fbit (activeCompleteGraph p Fbit) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p Fbit (activeCompleteGraph p Fbit) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p Fbit (activeCompleteGraph p Fbit) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

#print axioms exists_complete_inverse_Fbit
#print axioms completeInverseCert_Fbit

end PaddedFbit
