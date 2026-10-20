/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.MonoMode
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Family

@[expose] public section

/-!
# The bounded signed inverse for `Ftriv`

`Ftriv = {000, 001, 002, 012, 123, 133, 233, 333}`; allowed pairs `00, 01, 02, 12, 13, 23, 33`.
The three stages of `exists_complete_inverse_of_stages`:

* **totals.** The type edge vectors span the whole space of class totals (rank 7), so no
  real compatibility condition is needed. We use the seven types `000, 001, 002, 012, 123,
  133, 233` (not `333`):
  `z₁₂₃ = (x₁₃ + x₂₃ - x₃₃)/2`, `z₃₁ = (x₁₃ - z₁₂₃)/2`, `z₃₂ = (x₂₃ - z₁₂₃)/2`,
  `z₀₁₂ = x₁₂ - z₁₂₃`, `z₀₁ = (x₀₁ - z₀₁₂)/2`, `z₀₂ = (x₀₂ - z₀₁₂)/2`,
  `m = (x₀₀ - 2 z₀₁ - 2 z₀₂)/6` (with `x_ii` the ordered internal total). Then
  `|m| ≤ 2E` and all other `|z| ≤ 8E`, where `E` bounds the class totals;
* **vertex rows.** Class 0 (and symmetrically class 3) has the triangle link `01, 02, 12`;
  class 1 has the link `00 (loop), 02, 23`; class 2 has `00 (loop), 01, 13`;
* **zero rows.** One edge mode per allowed pair: internal modes `00 → 001`, `33 → 133`, and
  tripartite modes through `012` and `123`.

The final bound is the generic `2^20 ε / (γ^6 n)`.
-/

noncomputable section

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### Stage 1: class totals -/

def trivRealMatrix (x00 x01 x02 x12 x13 x23 x33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![x00, x01, x02, 0], ![x01, 0, x12, x13], ![x02, x12, 0, x23], ![0, x13, x23, x33]]

theorem classTotal_trivRealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Ftriv g) :
    classTotal p g = trivRealMatrix (classTotal p g 0 0) (classTotal p g 0 1)
      (classTotal p g 0 2) (classTotal p g 1 2) (classTotal p g 1 3) (classTotal p g 2 3)
      (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p Ftriv g hs 0 3 (by unfold Link Ftriv; decide)
  have h30 := classTotal_zero_of_inactive p Ftriv g hs 3 0 (by unfold Link Ftriv; decide)
  have h11 := classTotal_zero_of_inactive p Ftriv g hs 1 1 (by unfold Link Ftriv; decide)
  have h22 := classTotal_zero_of_inactive p Ftriv g hs 2 2 (by unfold Link Ftriv; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [trivRealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h30, h11, h22]

def trivTypeWeight (p : V → Fin 4) (m z01 z02 z012 z123 z31 z32 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 m a b c + repeatedTypeWeight p 0 1 z01 a b c +
  repeatedTypeWeight p 0 2 z02 a b c + tripartiteTypeWeight p 0 1 2 z012 a b c +
  tripartiteTypeWeight p 1 2 3 z123 a b c + repeatedTypeWeight p 3 1 z31 a b c +
  repeatedTypeWeight p 3 2 z32 a b c

theorem trivTypeWeight_symmetric (p : V → Fin 4) (m z01 z02 z012 z123 z31 z32 : ℝ) :
    TernarySymmetric (trivTypeWeight p m z01 z02 z012 z123 z31 z32) := by
  unfold trivTypeWeight
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem trivTypeWeight_supported (p : V → Fin 4) (m z01 z02 z012 z123 z31 z32 : ℝ) :
    TernarySupported p Ftriv (trivTypeWeight p m z01 z02 z012 z123 z31 z32) := by
  unfold trivTypeWeight
  repeat' first
    | exact monoTypeWeight_supported p Ftriv 0 (by unfold Link Ftriv; decide) _
    | exact aabLift_supported p Ftriv _ _ (by decide) (by unfold Link Ftriv; decide) _
    | exact abcLift_supported p Ftriv _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Ftriv; decide) _
    | apply TernarySupported.add

theorem trivTypeWeight_totals (p : V → Fin 4) (m z01 z02 z012 z123 z31 z32 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (trivTypeWeight p m z01 z02 z012 z123 z31 z32)) =
      trivRealMatrix (6 * m + 2 * z01 + 2 * z02) (2 * z01 + z012) (2 * z02 + z012)
        (z012 + z123) (2 * z31 + z123) (2 * z32 + z123) (2 * z31 + 2 * z32) := by
  funext i j
  unfold trivTypeWeight
  simp only [classTotal_ternary_add]
  have hmono := monoTypeWeight_totals p 0 m (hm 0) (hm1 0) (hm2 0) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmono, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [trivRealMatrix] <;> ring

theorem trivTypeWeight_bound (p : V → Fin 4) (m z01 z02 z012 z123 z31 z32 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hmz : |m| ≤ 2 * E)
    (hz : ∀ z ∈ [z01, z02, z012, z123, z31, z32], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |trivTypeWeight p m z01 z02 z012 z123 z31 z32 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := trivTypeWeight_supported p m z01 z02 z012 z123 z31 z32
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p Ftriv a b c := by
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
  have h0 := monoType_normalizer_bound p 0 m E δ hE hδ hmz hm
  have h1 := repeatedType_normalizer_bound p 0 1 z01 E δ hE hδ (hz z01 (by simp)) hm
  have h2 := repeatedType_normalizer_bound p 0 2 z02 E δ hE hδ (hz z02 (by simp)) hm
  have h3 := tripartiteType_normalizer_bound p 0 1 2 z012 E δ hE hδ (hz z012 (by simp)) hm
  have h4 := tripartiteType_normalizer_bound p 1 2 3 z123 E δ hE hδ (hz z123 (by simp)) hm
  have h5 := repeatedType_normalizer_bound p 3 1 z31 E δ hE hδ (hz z31 (by simp)) hm
  have h6 := repeatedType_normalizer_bound p 3 2 z32 E δ hE hδ (hz z32 (by simp)) hm
  dsimp only [trivTypeWeight, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
    aabLift, abcLift, pairSymmetrize, aabBase, abcBase]
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
    | exact hM

theorem exists_type_correction_Ftriv (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Ftriv g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p Ftriv w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b12 := abs_le.mp (hbound 1 2)
  have b13 := abs_le.mp (hbound 1 3)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  set x00 := classTotal p g 0 0
  set x01 := classTotal p g 0 1
  set x02 := classTotal p g 0 2
  set x12 := classTotal p g 1 2
  set x13 := classTotal p g 1 3
  set x23 := classTotal p g 2 3
  set x33 := classTotal p g 3 3
  let z123 := (x13 + x23 - x33) / 2
  let z31 := (x13 - z123) / 2
  let z32 := (x23 - z123) / 2
  let z012 := x12 - z123
  let z01 := (x01 - z012) / 2
  let z02 := (x02 - z012) / 2
  let m := (x00 - 2 * z01 - 2 * z02) / 6
  have hmz : |m| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [m, z01, z02, z012, z123] <;> linarith
  have hz : ∀ z ∈ [z01, z02, z012, z123, z31, z32], |z| ≤ 8 * E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> dsimp only [z01, z02, z012, z123, z31, z32] <;>
      linarith
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨trivTypeWeight p m z01 z02 z012 z123 z31 z32, trivTypeWeight_symmetric p _ _ _ _ _ _ _,
    trivTypeWeight_supported p _ _ _ _ _ _ _, ?_,
    trivTypeWeight_bound p _ _ _ _ _ _ _ E δ hE hδ hmz hz hm⟩
  rw [trivTypeWeight_totals p _ _ _ _ _ _ _ hn hn1 hn2, classTotal_trivRealMatrix p g hsym hs]
  congr 1 <;> dsimp only [m, z01, z02, z012, z123, z31, z32] <;> ring

/-! ### Stage 2: vertex rows -/

def trivVertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (fun v => (d v 0 + d v 1 - d v 2) / 2) a b c +
  repeatedVertexWeight p 0 2 (fun v => (d v 0 + d v 2 - d v 1) / 2) a b c +
  tripartiteVertexWeight p 0 1 2 (fun v => (d v 1 + d v 2 - d v 0) / 2) a b c +
  repeatedVertexWeight p 3 1 (fun v => (d v 3 + d v 1 - d v 2) / 2) a b c +
  repeatedVertexWeight p 3 2 (fun v => (d v 3 + d v 2 - d v 1) / 2) a b c +
  tripartiteVertexWeight p 3 1 2 (fun v => (d v 1 + d v 2 - d v 3) / 2) a b c +
  singletonVertexWeight p 0 1 (fun v => (d v 0 - d v 2 + d v 3) / 2) a b c +
  tripartiteVertexWeight p 1 0 2 (fun v => d v 2 - d v 3) a b c +
  tripartiteVertexWeight p 1 2 3 (fun v => d v 3) a b c +
  singletonVertexWeight p 0 2 (fun v => (d v 0 - d v 1 + d v 3) / 2) a b c +
  tripartiteVertexWeight p 2 0 1 (fun v => d v 1 - d v 3) a b c +
  tripartiteVertexWeight p 2 1 3 (fun v => d v 3) a b c

theorem trivVertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (trivVertexWeight p d) := by
  unfold trivVertexWeight
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem trivVertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p Ftriv (trivVertexWeight p d) := by
  unfold trivVertexWeight
  repeat' first
    | exact aabLift_supported p Ftriv _ _ (by decide) (by unfold Link Ftriv; decide) _
    | exact abcLift_supported p Ftriv _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Ftriv; decide) _
    | apply TernarySupported.add

theorem trivVertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p Ftriv d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (trivVertexWeight p d)) a k = d a k := by
  unfold VertexDemandZero at hz
  have hsum : ∀ (i : Fin 4) (x y w : ℝ) (j1 j2 j3 : Fin 4),
      (∑ v ∈ classVertices p i, (x * d v j1 + y * d v j2 + w * d v j3)) = 0 := by
    intro i x y w j1 j2 j3
    simp only [sum_add_distrib, ← mul_sum, hz, mul_zero, add_zero]
  have e1 : ∀ (i : Fin 4) (j1 j2 j3 : Fin 4),
      (∑ v ∈ classVertices p i, (d v j1 + d v j2 - d v j3) / 2) = 0 := by
    intro i j1 j2 j3
    have := hsum i (1 / 2) (1 / 2) (-1 / 2) j1 j2 j3
    rw [← this]; exact sum_congr rfl fun v _ => by ring
  have e2 : ∀ (i : Fin 4) (j1 j2 j3 : Fin 4),
      (∑ v ∈ classVertices p i, (d v j1 - d v j2 + d v j3) / 2) = 0 := by
    intro i j1 j2 j3
    have := hsum i (1 / 2) (-1 / 2) (1 / 2) j1 j2 j3
    rw [← this]; exact sum_congr rfl fun v _ => by ring
  have e3 : ∀ (i : Fin 4) (j1 j2 : Fin 4),
      (∑ v ∈ classVertices p i, (d v j1 - d v j2)) = 0 := by
    intro i j1 j2
    rw [sum_sub_distrib, hz, hz, sub_zero]
  unfold trivVertexWeight
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (e1 0 0 1 2) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (e1 0 0 2 1) (hm2 0) (hm 2),
    tripartiteVertexWeight_rows p 0 1 2 _ (e1 0 1 2 0) (hm 1) (hm 2),
    repeatedVertexWeight_rows p 3 1 _ (e1 3 3 1 2) (hm2 3) (hm 1),
    repeatedVertexWeight_rows p 3 2 _ (e1 3 3 2 1) (hm2 3) (hm 2),
    tripartiteVertexWeight_rows p 3 1 2 _ (e1 3 1 2 3) (hm 1) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (e2 1 0 2 3) (hm 0) (hm1 0),
    tripartiteVertexWeight_rows p 1 0 2 _ (e3 1 2 3) (hm 0) (hm 2),
    tripartiteVertexWeight_rows p 1 2 3 _ (hz 1 3) (hm 2) (hm 3),
    singletonVertexWeight_rows p 0 2 _ (e2 2 0 1 3) (hm 0) (hm1 0),
    tripartiteVertexWeight_rows p 2 0 1 _ (e3 2 1 3) (hm 0) (hm 1),
    tripartiteVertexWeight_rows p 2 1 3 _ (hz 2 3) (hm 1) (hm 3)]
  have hforb := hs a k
  generalize hpa : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp
  all_goals first
    | ring1
    | simpa using (hforb (by unfold Link Ftriv; decide)).symm

theorem trivVertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |trivVertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc (v : V) := triangle_link_bound _ _ _ D (hd v 0) (hd v 1) (hd v 2)
  have hc3 (v : V) := triangle_link_bound _ _ _ D (hd v 3) (hd v 1) (hd v 2)
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) := vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have k1 : ∀ v, |(d v 0 - d v 2 + d v 3) / 2| ≤ 2 * D := by
    intro v
    have := abs_le.mp (hd v 0); have := abs_le.mp (hd v 2); have := abs_le.mp (hd v 3)
    apply abs_le.mpr; constructor <;> linarith
  have k2 : ∀ v, |d v 2 - d v 3| ≤ 2 * D := by
    intro v
    have := abs_le.mp (hd v 2); have := abs_le.mp (hd v 3)
    apply abs_le.mpr; constructor <;> linarith
  have k3 : ∀ v, |d v 3| ≤ 2 * D := fun v => (hd v 3).trans (by linarith)
  have k4 : ∀ v, |(d v 0 - d v 1 + d v 3) / 2| ≤ 2 * D := by
    intro v
    have := abs_le.mp (hd v 0); have := abs_le.mp (hd v 1); have := abs_le.mp (hd v 3)
    apply abs_le.mpr; constructor <;> linarith
  have k5 : ∀ v, |d v 1 - d v 3| ≤ 2 * D := by
    intro v
    have := abs_le.mp (hd v 1); have := abs_le.mp (hd v 3)
    apply abs_le.mpr; constructor <;> linarith
  have t1 := (hb _ fun v => (hc v).1).1 0 1
  have t2 := (hb _ fun v => (hc v).2.1).1 0 2
  have t3 := (hb _ fun v => (hc v).2.2).2.2 0 1 2
  have t4 := (hb _ fun v => (hc3 v).1).1 3 1
  have t5 := (hb _ fun v => (hc3 v).2.1).1 3 2
  have t6 := (hb _ fun v => (hc3 v).2.2).2.2 3 1 2
  have t7 := (hb _ k1).2.1 0 1
  have t8 := (hb _ k2).2.2 1 0 2
  have t9 := (hb _ k3).2.2 1 2 3
  have t10 := (hb _ k4).2.1 0 2
  have t11 := (hb _ k5).2.2 2 0 1
  have t12 := (hb _ k3).2.2 2 1 3
  have hM : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM]
  generalize 12 * (2 * D) / δ ^ 2 = M at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ⊢
  unfold trivVertexWeight
  rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
    t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2, t10.1, t10.2, t11.1, t11.2, t12.1, t12.2]

/-! ### Stage 3: zero rows -/

def trivZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c + tripartitePairWeight p 0 1 2 g a b c +
  tripartitePairWeight p 0 2 1 g a b c + tripartitePairWeight p 1 2 0 g a b c +
  tripartitePairWeight p 1 3 2 g a b c + tripartitePairWeight p 2 3 1 g a b c +
  internalPairWeight p 3 1 g a b c

theorem trivZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (trivZeroRowWeight p g) := by
  unfold trivZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ _ hs
    | exact abcLift_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem trivZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p Ftriv (trivZeroRowWeight p g) := by
  unfold trivZeroRowWeight
  repeat' first
    | exact aabLift_supported p Ftriv _ _ (by decide) (by unfold Link Ftriv; decide) _
    | exact abcLift_supported p Ftriv _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Ftriv; decide) _
    | apply TernarySupported.add

theorem trivZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link Ftriv (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (a b : V) :
    ternaryLoad (trivZeroRowWeight p g) a b = g a b := by
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  unfold trivZeroRowWeight
  simp only [ternaryLoad_add, htri, hint]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link Ftriv; decide)).symm

theorem trivZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |trivZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, _, ht⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := ht 0 1 2
  have h2 := ht 0 2 1
  have h3 := ht 1 2 0
  have h4 := ht 1 3 2
  have h5 := ht 2 3 1
  have h6 := hi 3 1
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 hpos ⊢
  unfold trivZeroRowWeight
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2,
    h5.1, h5.2, h6.1, h6.2]

end PaddedTrivial
