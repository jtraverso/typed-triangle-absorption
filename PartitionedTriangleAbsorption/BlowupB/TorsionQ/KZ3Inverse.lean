/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.MonoVertex
public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.KZ3Universal

@[expose] public section

/-!
# The bounded signed inverse for `KZ3 = F* ∖ {233}`

Totals: the F* modes without `233` (`zE = t23`, `zD = t12 - t23`, `zF = (t13 - t23)/2`,
`zH = (t33 - 2 zF)/6`, then halving). Vertex rows of class 2 use the tripartite mode `213` instead of
the singleton `332`; class 3 uses `312`, `331` and the new monochromatic vertex mode
(`monoVertexWeight`), with a sharper per-mode budget (total `246 D/δ² ≤ 288 D/δ²`). Zero rows cover
the 23-edges with the tripartite mode `231`. The bound `2^20 ε/(γ^6 n)` is kept.
-/

noncomputable section

namespace TorsionQ.KZ3

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

/-! ### Stage 1: totals -/

def kz3RealMatrix (t00 t01 t02 t12 t13 t23 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, 0, t12, t13], ![t02, t12, 0, t23], ![0, t13, t23, t33]]

theorem classTotal_kz3RealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KZ3 g) :
    classTotal p g = kz3RealMatrix (classTotal p g 0 0) (classTotal p g 0 1)
      (classTotal p g 0 2) (classTotal p g 1 2) (classTotal p g 1 3) (classTotal p g 2 3)
      (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p KZ3 g hs 0 3 (by unfold Link KZ3; decide)
  have h11 := classTotal_zero_of_inactive p KZ3 g hs 1 1 (by unfold Link KZ3; decide)
  have h22 := classTotal_zero_of_inactive p KZ3 g hs 2 2 (by unfold Link KZ3; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [kz3RealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h03, h11, h22]

def kz3TypeWeight (p : V → Fin 4) (zA zB zC zD zE zF zH : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 zA a b c + repeatedTypeWeight p 0 1 zB a b c +
  repeatedTypeWeight p 0 2 zC a b c + tripartiteTypeWeight p 0 1 2 zD a b c +
  tripartiteTypeWeight p 1 2 3 zE a b c + repeatedTypeWeight p 3 1 zF a b c +
  monoTypeWeight p 3 zH a b c

theorem kz3TypeWeight_symmetric (p : V → Fin 4) (zA zB zC zD zE zF zH : ℝ) :
    TernarySymmetric (kz3TypeWeight p zA zB zC zD zE zF zH) := by
  unfold kz3TypeWeight
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem kz3TypeWeight_supported (p : V → Fin 4) (zA zB zC zD zE zF zH : ℝ) :
    TernarySupported p KZ3 (kz3TypeWeight p zA zB zC zD zE zF zH) := by
  unfold kz3TypeWeight
  repeat' first
    | exact monoTypeWeight_supported p KZ3 _ (by unfold Link KZ3; decide) _
    | exact aabLift_supported p KZ3 _ _ (by decide) (by unfold Link KZ3; decide) _
    | exact abcLift_supported p KZ3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KZ3; decide) _
    | apply TernarySupported.add

theorem kz3TypeWeight_totals (p : V → Fin 4) (zA zB zC zD zE zF zH : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (kz3TypeWeight p zA zB zC zD zE zF zH)) =
      kz3RealMatrix (6 * zA + 2 * zB + 2 * zC) (2 * zB + zD) (2 * zC + zD) (zD + zE)
        (zE + 2 * zF) (zE) (2 * zF + 6 * zH) := by
  funext i j
  unfold kz3TypeWeight
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [kz3RealMatrix] <;> ring

theorem kz3TypeWeight_bound (p : V → Fin 4) (zA zB zC zD zE zF zH E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hzA : |zA| ≤ 2 * E) (hzH : |zH| ≤ 2 * E)
    (hz : ∀ z ∈ [zB, zC, zD, zE, zF], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |kz3TypeWeight p zA zB zC zD zE zF zH a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := kz3TypeWeight_supported p zA zB zC zD zE zF zH
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KZ3 a b c := by
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
  have h7 := mono_normalizer_bound p 3 zH E δ hE hδ hzH hm
  have h1 := repeatedType_normalizer_bound p 0 1 zB E δ hE hδ (hz zB (by simp)) hm
  have h2 := repeatedType_normalizer_bound p 0 2 zC E δ hE hδ (hz zC (by simp)) hm
  have h3 := tripartiteType_normalizer_bound p 0 1 2 zD E δ hE hδ (hz zD (by simp)) hm
  have h4 := tripartiteType_normalizer_bound p 1 2 3 zE E δ hE hδ (hz zE (by simp)) hm
  have h5 := repeatedType_normalizer_bound p 3 1 zF E δ hE hδ (hz zF (by simp)) hm
  dsimp only [kz3TypeWeight, monoTypeWeight, repeatedTypeWeight,
    tripartiteTypeWeight, aabLift, abcLift, pairSymmetrize, aabBase, abcBase]
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
    | exact h7
    | exact hM

theorem exists_type_correction_KZ3 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KZ3 g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KZ3 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b12 := abs_le.mp (hbound 1 2)
  have b13 := abs_le.mp (hbound 1 3)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  let zE := classTotal p g 2 3
  let zD := classTotal p g 1 2 - zE
  let zF := (classTotal p g 1 3 - zE) / 2
  let zH := (classTotal p g 3 3 - 2 * zF) / 6
  let zB := (classTotal p g 0 1 - zD) / 2
  let zC := (classTotal p g 0 2 - zD) / 2
  let zA := (classTotal p g 0 0 - 2 * zB - 2 * zC) / 6
  have hzA : |zA| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [zA, zB, zC, zD, zE] <;> linarith
  have hzH : |zH| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [zH, zF, zE] <;> linarith
  have hz : ∀ z ∈ [zB, zC, zD, zE, zF], |z| ≤ 8 * E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> dsimp only [zB, zC, zD, zE, zF] <;> linarith
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨kz3TypeWeight p zA zB zC zD zE zF zH, kz3TypeWeight_symmetric p _ _ _ _ _ _ _,
    kz3TypeWeight_supported p _ _ _ _ _ _ _, ?_,
    kz3TypeWeight_bound p _ _ _ _ _ _ _ E δ hE hδ hzA hzH hz hm⟩
  rw [kz3TypeWeight_totals p _ _ _ _ _ _ _ hn hn1 hn2, classTotal_kz3RealMatrix p g hsym hs]
  congr 1 <;> dsimp only [zA, zB, zC, zD, zE, zF, zH] <;> ring

/-! ### Stage 2: vertex rows (with the monochromatic vertex mode for class 3) -/

def kz3VertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (fun v => (d v 0 + d v 1 - d v 2) / 2) a b c +
  repeatedVertexWeight p 0 2 (fun v => (d v 0 + d v 2 - d v 1) / 2) a b c +
  tripartiteVertexWeight p 0 1 2 (fun v => (d v 1 + d v 2 - d v 0) / 2) a b c +
  tripartiteVertexWeight p 1 0 2 (fun v => d v 2) a b c +
  singletonVertexWeight p 0 1 (fun v => (d v 0 - d v 2) / 2) a b c +
  singletonVertexWeight p 3 1 (fun v => d v 3 / 2) a b c +
  tripartiteVertexWeight p 2 0 1 (fun v => d v 1 - d v 3) a b c +
  singletonVertexWeight p 0 2 (fun v => (d v 0 - d v 1 + d v 3) / 2) a b c +
  tripartiteVertexWeight p 2 1 3 (fun v => d v 3) a b c +
  tripartiteVertexWeight p 3 1 2 (fun v => d v 2) a b c +
  repeatedVertexWeight p 3 1 (fun v => d v 1 - d v 2) a b c +
  monoVertexWeight p 3 (fun v => (d v 3 - d v 1 + d v 2) / 2) a b c

theorem kz3VertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (kz3VertexWeight p d) := by
  unfold kz3VertexWeight
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add

theorem kz3VertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KZ3 (kz3VertexWeight p d) := by
  unfold kz3VertexWeight
  repeat' first
    | exact monoVertexWeight_supported p KZ3 _ (by unfold Link KZ3; decide) _
    | exact aabLift_supported p KZ3 _ _ (by decide) (by unfold Link KZ3; decide) _
    | exact abcLift_supported p KZ3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KZ3; decide) _
    | apply TernarySupported.add

theorem kz3VertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KZ3 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (kz3VertexWeight p d)) a k = d a k := by
  unfold VertexDemandZero at hz
  have zs : ∀ (i : Fin 4) (f : V → ℝ), f = (fun v => f v) → True := fun _ _ _ => trivial
  have s3 : ∀ (i x y w : Fin 4), (∑ v ∈ classVertices p i, (d v x + d v y - d v w) / 2) = 0 := by
    intro i x y w
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have s2 : ∀ (i x y : Fin 4), (∑ v ∈ classVertices p i, (d v x - d v y) / 2) = 0 := by
    intro i x y
    simp only [← sum_div, sum_sub_distrib, hz, sub_self, zero_div]
  have s1 : ∀ (i x : Fin 4), (∑ v ∈ classVertices p i, d v x / 2) = 0 := by
    intro i x; rw [← sum_div, hz, zero_div]
  have s0 : ∀ (i x : Fin 4), (∑ v ∈ classVertices p i, d v x) = 0 := fun i x => hz i x
  have sd : ∀ (i x y : Fin 4), (∑ v ∈ classVertices p i, (d v x - d v y)) = 0 := by
    intro i x y; rw [sum_sub_distrib, hz, hz, sub_self]
  have sm : ∀ (i x y w : Fin 4), (∑ v ∈ classVertices p i, (d v x - d v y + d v w) / 2) = 0 := by
    intro i x y w
    simp only [← sum_div, sum_add_distrib, sum_sub_distrib, hz, sub_self, add_zero, zero_div]
  unfold kz3VertexWeight
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (s3 0 0 1 2) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (s3 0 0 2 1) (hm2 0) (hm 2),
    tripartiteVertexWeight_rows p 0 1 2 _ (s3 0 1 2 0) (hm 1) (hm 2),
    tripartiteVertexWeight_rows p 1 0 2 _ (s0 1 2) (hm 0) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (s2 1 0 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 3 1 _ (s1 1 3) (hm 3) (hm1 3),
    tripartiteVertexWeight_rows p 2 0 1 _ (sd 2 1 3) (hm 0) (hm 1),
    singletonVertexWeight_rows p 0 2 _ (sm 2 0 1 3) (hm 0) (hm1 0),
    tripartiteVertexWeight_rows p 2 1 3 _ (s0 2 3) (hm 1) (hm 3),
    tripartiteVertexWeight_rows p 3 1 2 _ (s0 3 2) (hm 1) (hm 2),
    repeatedVertexWeight_rows p 3 1 _ (sd 3 1 2) (hm2 3) (hm 1),
    monoVertexWeight_rows p 3 _ (sm 3 3 1 2) (hm2 3) (hm3 3)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp
  all_goals first
    | exact (hforb (by unfold Link KZ3; decide)).symm
    | ring

theorem kz3VertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |kz3VertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hb (f : V → ℝ) (D' : ℝ) (hD' : 0 ≤ D') (hf : ∀ v, |f v| ≤ D') :=
    vertexMode_bounds p f D' δ hD' hδ hf hm a b c
  have q4 (v : V) := And.intro (abs_le.mp (hd v 0)) (And.intro (abs_le.mp (hd v 1))
    (And.intro (abs_le.mp (hd v 2)) (abs_le.mp (hd v 3))))
  have hD32 : 0 ≤ 3 / 2 * D := by positivity
  have hD2 : 0 ≤ 2 * D := by positivity
  have hD12 : 0 ≤ 1 / 2 * D := by positivity
  have e1 := (hb (fun v => (d v 0 + d v 1 - d v 2) / 2) (3 / 2 * D) hD32 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h0.1, h0.2,
      h1.1, h1.2, h2.1, h2.2])).1 0 1
  have e2 := (hb (fun v => (d v 0 + d v 2 - d v 1) / 2) (3 / 2 * D) hD32 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h0.1, h0.2,
      h1.1, h1.2, h2.1, h2.2])).1 0 2
  have e3 := (hb (fun v => (d v 1 + d v 2 - d v 0) / 2) (3 / 2 * D) hD32 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h0.1, h0.2,
      h1.1, h1.2, h2.1, h2.2])).2.2 0 1 2
  have e4 := (hb (fun v => d v 2) D hD (fun v => hd v 2)).2.2 1 0 2
  have e5 := (hb (fun v => (d v 0 - d v 2) / 2) D hD (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h0.1, h0.2,
      h2.1, h2.2])).2.1 0 1
  have e6 := (hb (fun v => d v 3 / 2) (1 / 2 * D) hD12 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h3.1, h3.2])).2.1 3 1
  have e7 := (hb (fun v => d v 1 - d v 3) (2 * D) hD2 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h1.1, h1.2,
      h3.1, h3.2])).2.2 2 0 1
  have e8 := (hb (fun v => (d v 0 - d v 1 + d v 3) / 2) (3 / 2 * D) hD32 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h0.1, h0.2,
      h1.1, h1.2, h3.1, h3.2])).2.1 0 2
  have e9 := (hb (fun v => d v 3) D hD (fun v => hd v 3)).2.2 2 1 3
  have e10 := (hb (fun v => d v 2) D hD (fun v => hd v 2)).2.2 3 1 2
  have e11 := (hb (fun v => d v 1 - d v 2) (2 * D) hD2 (fun v => by
    obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h1.1, h1.2,
      h2.1, h2.2])).1 3 1
  have e12 := monoVertexWeight_bound p 3 (fun v => (d v 3 - d v 1 + d v 2) / 2) (3 / 2 * D) δ hD32
    hδ (fun v => by
      obtain ⟨h0, h1, h2, h3⟩ := q4 v; apply abs_le.mpr; constructor <;> linarith [h1.1, h1.2,
        h2.1, h2.2, h3.1, h3.2]) hm a b c
  have hδ0 : 0 < δ ^ 2 := by positivity
  have r32 : 12 * (3 / 2 * D) / δ ^ 2 = 18 * (D / δ ^ 2) := by ring
  have r1 : 12 * D / δ ^ 2 = 12 * (D / δ ^ 2) := by ring
  have r12 : 12 * (1 / 2 * D) / δ ^ 2 = 6 * (D / δ ^ 2) := by ring
  have r2 : 12 * (2 * D) / δ ^ 2 = 24 * (D / δ ^ 2) := by ring
  have rm : 48 * (3 / 2 * D) / δ ^ 2 = 72 * (D / δ ^ 2) := by ring
  rw [r32] at e1 e2 e3 e8
  rw [r1] at e4 e5 e9 e10
  rw [r12] at e6
  rw [r2] at e7 e11
  rw [rm] at e12
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold kz3VertexWeight
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 hM0 ⊢
  rw [abs_le] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2,
    e7.1, e7.2, e8.1, e8.2, e9.1, e9.2, e10.1, e10.2, e11.1, e11.2, e12.1, e12.2]

/-! ### Stage 3: zero rows -/

def kz3ZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c + internalPairWeight p 3 1 g a b c +
  repeatedPairWeight p 0 1 g a b c + repeatedPairWeight p 0 2 g a b c +
  tripartitePairWeight p 1 2 0 g a b c + repeatedPairWeight p 3 1 g a b c +
  tripartitePairWeight p 2 3 1 g a b c

theorem kz3ZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (kz3ZeroRowWeight p g) := by
  unfold kz3ZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem kz3ZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p KZ3 (kz3ZeroRowWeight p g) := by
  unfold kz3ZeroRowWeight
  repeat' first
    | exact aabLift_supported p KZ3 _ _ (by decide) (by unfold Link KZ3; decide) _
    | exact abcLift_supported p KZ3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KZ3; decide) _
    | apply TernarySupported.add

theorem kz3ZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link KZ3 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (kz3ZeroRowWeight p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  unfold kz3ZeroRowWeight
  simp only [ternaryLoad_add, hint, hrep, htri]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link KZ3; decide)).symm

theorem kz3ZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |kz3ZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hi 3 1
  have h2 := hr 0 1
  have h3 := hr 0 2
  have h4 := ht 1 2 0
  have h5 := hr 3 1
  have h6 := ht 2 3 1
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 hpos ⊢
  unfold kz3ZeroRowWeight
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2,
    h5.1, h5.2, h6.1, h6.2]

/-! ### The complete inverse and the certificate -/

theorem exists_complete_inverse_KZ3 (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p KZ3 g) (hg : ∀ a b, |g a b| ≤ ε) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p KZ3 w ∧
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
      TernarySymmetric w ∧ TernarySupported p KZ3 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p KZ3 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_KZ3 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨kz3VertexWeight p d, kz3VertexWeight_symmetric p d,
        kz3VertexWeight_supported p d, kz3VertexWeight_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ kz3VertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨kz3ZeroRowWeight p f, kz3ZeroRowWeight_symmetric p f hf,
        kz3ZeroRowWeight_supported p f, kz3ZeroRowWeight_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ kz3ZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert KZ3`** (no compatibility condition is needed). -/
theorem completeInverseCert_KZ3 : PaddedGeneral.CompleteInverseCert KZ3 := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_KZ3 p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hs.edgeSupported
    (fun a b => hr s(a, b))
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p KZ3 w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p KZ3 (activeCompleteGraph p KZ3) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p KZ3 (activeCompleteGraph p KZ3) z,
    copyRestriction_supported p KZ3 (activeCompleteGraph p KZ3) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p KZ3 (activeCompleteGraph p KZ3) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p KZ3 (activeCompleteGraph p KZ3) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity


end TorsionQ.KZ3

#print axioms TorsionQ.KZ3.exists_complete_inverse_KZ3
#print axioms TorsionQ.KZ3.completeInverseCert_KZ3
