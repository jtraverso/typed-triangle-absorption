/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Universal
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-!
# The bounded signed inverse for F*

Totals use a new MONOCHROMATIC mode (`monoTypeWeight`, type `iii`) for 000 and 333, together with
repeated and tripartite modes. The type vectors span all seven allowed total coordinates, so no
compatibility condition is needed. Vertex rows and zero rows use only existing modes (no
monochromatic one). The bound `2^20 ε/(γ^6 n)` of the F₁/F₂ inverse is kept.
-/

noncomputable section

namespace PaddedFstar

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### The monochromatic mode -/

/-- Uniform weight `z` of type `iii`, spread over the ordered triples of distinct `V_i`-vertices. -/
def monoTypeWeight (p : V → Fin 4) (i : Fin 4) (z : ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) else 0

theorem monoTypeWeight_symmetric (p : V → Fin 4) (i : Fin 4) (z : ℝ) :
    TernarySymmetric (monoTypeWeight p i z) := by
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩ <;> unfold monoTypeWeight
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h2, h1, h3, h4, h6, h5⟩
      exact h ⟨h1, h2, h3, Ne.symm h4, h5, h6⟩
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h3, h2, h5, h4, h6⟩
      exact h ⟨h1, h2, h3, h4, h5, Ne.symm h6⟩

theorem monoTypeWeight_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (i : Fin 4)
    (hF : Link F i i i) (z : ℝ) : TernarySupported p F (monoTypeWeight p i z) := by
  intro a b c hbad
  unfold monoTypeWeight
  rw [if_neg]
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact hbad ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩

theorem monoTypeWeight_load (p : V → Fin 4) (i : Fin 4) (z : ℝ)
    (hm : classSize p i ≠ 0) (hm1 : classSize p i - 1 ≠ 0) (hm2 : classSize p i - 2 ≠ 0)
    (a b : V) :
    ternaryLoad (monoTypeWeight p i z) a b =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) a b := by
  classical
  unfold ternaryLoad monoTypeWeight constInternalBlock
  by_cases hab : p a = i ∧ p b = i ∧ a ≠ b
  · obtain ⟨ha, hb, hne⟩ := hab
    rw [if_pos ⟨ha, hb⟩, if_pos hne]
    have hset : (univ.filter fun c => p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) =
        ((classVertices p i).erase a).erase b := by
      ext c
      rw [mem_filter, mem_erase, mem_erase]
      simp only [mem_univ, true_and, classVertices, mem_filter]
      constructor
      · rintro ⟨-, -, h3, -, h5, h6⟩; exact ⟨Ne.symm h6, Ne.symm h5, h3⟩
      · rintro ⟨h6, h5, h3⟩; exact ⟨ha, hb, h3, hne, Ne.symm h5, Ne.symm h6⟩
    have haV : a ∈ classVertices p i := by simp [classVertices, ha]
    have hbV : b ∈ (classVertices p i).erase a := by
      simp [classVertices, hb, Ne.symm hne]
    have hcard : (((classVertices p i).erase a).erase b).card = (classVertices p i).card - 2 := by
      rw [card_erase_of_mem hbV, card_erase_of_mem haV]
      omega
    have hge : 2 ≤ (classVertices p i).card := by
      have h1 := card_erase_of_mem haV
      have h2 : 0 < ((classVertices p i).erase a).card := card_pos.mpr ⟨b, hbV⟩
      omega
    rw [← sum_filter, hset, sum_const, nsmul_eq_mul, hcard]
    have hcast : (((classVertices p i).card - 2 : ℕ) : ℝ) = classSize p i - 2 := by
      unfold classSize; rw [Nat.cast_sub hge]; norm_num
    rw [hcast]
    field_simp
  · have hzero : ∀ c, ¬ (p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
      rintro c ⟨h1, h2, -, h4, -, -⟩; exact hab ⟨h1, h2, h4⟩
    simp only [hzero, if_false, sum_const_zero]
    by_cases h12 : p a = i ∧ p b = i
    · rw [if_pos h12, if_neg]
      intro hne; exact hab ⟨h12.1, h12.2, hne⟩
    · rw [if_neg h12]

theorem monoTypeWeight_totals (p : V → Fin 4) (i : Fin 4) (z : ℝ)
    (hm : classSize p i ≠ 0) (hm1 : classSize p i - 1 ≠ 0) (hm2 : classSize p i - 2 ≠ 0)
    (k l : Fin 4) :
    classTotal p (ternaryLoad (monoTypeWeight p i z)) k l =
      if k = i ∧ l = i then 6 * z else 0 := by
  have he : ternaryLoad (monoTypeWeight p i z) =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) := by
    funext a b; exact monoTypeWeight_load p i z hm hm1 hm2 a b
  rw [he, classTotal_constInternalBlock]
  split_ifs
  · field_simp
  · rfl

theorem mono_normalizer_bound (p : V → Fin 4) (i : Fin 4) (z E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz : |z| ≤ 2 * E) (hm : ∀ i, δ ≤ classSize p i) :
    |6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2))| ≤ 32 * E / δ ^ 3 := by
  have hmi := hm i
  set m := classSize p i with hmdef
  have hd : 0 < δ := by linarith
  have hm0 : 0 < m := by linarith
  have h1 : 3 * m / 4 ≤ m - 1 := by linarith
  have h2 : m / 2 ≤ m - 2 := by linarith
  have hden : 3 * δ ^ 3 / 8 ≤ m * (m - 1) * (m - 2) := by
    have hδm : δ ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ hd.le hmi 3
    have hprod : m * (3 * m / 4) * (m / 2) ≤ m * (m - 1) * (m - 2) := by
      have hA : m * (3 * m / 4) ≤ m * (m - 1) := mul_le_mul_of_nonneg_left h1 hm0.le
      exact mul_le_mul hA h2 (by positivity) (by nlinarith)
    nlinarith
  have hdenpos : 0 < m * (m - 1) * (m - 2) := lt_of_lt_of_le (by positivity) hden
  rw [abs_div, abs_of_pos hdenpos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
  rw [div_le_div_iff₀ hdenpos (by positivity)]
  have h6 : 6 * |z| ≤ 12 * E := by linarith
  nlinarith [mul_le_mul h6 hden (by positivity) (by positivity)]

/-! ### Stage 1: totals -/

def fstarRealMatrix (t00 t01 t02 t12 t13 t23 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, 0, t12, t13], ![t02, t12, 0, t23], ![0, t13, t23, t33]]

theorem classTotal_fstarRealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Fstar g) :
    classTotal p g = fstarRealMatrix (classTotal p g 0 0) (classTotal p g 0 1)
      (classTotal p g 0 2) (classTotal p g 1 2) (classTotal p g 1 3) (classTotal p g 2 3)
      (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p Fstar g hs 0 3 (by unfold Link Fstar; decide)
  have h11 := classTotal_zero_of_inactive p Fstar g hs 1 1 (by unfold Link Fstar; decide)
  have h22 := classTotal_zero_of_inactive p Fstar g hs 2 2 (by unfold Link Fstar; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fstarRealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h03, h11, h22]

def fstarTypeWeight (p : V → Fin 4) (zA zB zC zD zE zF zG zH : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 zA a b c + repeatedTypeWeight p 0 1 zB a b c +
  repeatedTypeWeight p 0 2 zC a b c + tripartiteTypeWeight p 0 1 2 zD a b c +
  tripartiteTypeWeight p 1 2 3 zE a b c + repeatedTypeWeight p 3 1 zF a b c +
  repeatedTypeWeight p 3 2 zG a b c + monoTypeWeight p 3 zH a b c

theorem fstarTypeWeight_symmetric (p : V → Fin 4) (zA zB zC zD zE zF zG zH : ℝ) :
    TernarySymmetric (fstarTypeWeight p zA zB zC zD zE zF zG zH) := by
  unfold fstarTypeWeight
  repeat' first
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem fstarTypeWeight_supported (p : V → Fin 4) (zA zB zC zD zE zF zG zH : ℝ) :
    TernarySupported p Fstar (fstarTypeWeight p zA zB zC zD zE zF zG zH) := by
  unfold fstarTypeWeight
  repeat' first
    | exact monoTypeWeight_supported p Fstar _ (by unfold Link Fstar; decide) _
    | exact aabLift_supported p Fstar _ _ (by decide) (by unfold Link Fstar; decide) _
    | exact abcLift_supported p Fstar _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Fstar; decide) _
    | apply TernarySupported.add

theorem fstarTypeWeight_totals (p : V → Fin 4) (zA zB zC zD zE zF zG zH : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (fstarTypeWeight p zA zB zC zD zE zF zG zH)) =
      fstarRealMatrix (6 * zA + 2 * zB + 2 * zC) (2 * zB + zD) (2 * zC + zD) (zD + zE)
        (zE + 2 * zF) (zE + 2 * zG) (2 * zF + 2 * zG + 6 * zH) := by
  funext i j
  unfold fstarTypeWeight
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [fstarRealMatrix] <;> ring

theorem fstarTypeWeight_bound (p : V → Fin 4) (zA zB zC zD zE zF zG zH E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hzA : |zA| ≤ 2 * E) (hzH : |zH| ≤ 2 * E)
    (hz : ∀ z ∈ [zB, zC, zD, zE, zF, zG], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fstarTypeWeight p zA zB zC zD zE zF zG zH a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := fstarTypeWeight_supported p zA zB zC zD zE zF zG zH
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p Fstar a b c := by
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
  have h6 := repeatedType_normalizer_bound p 3 2 zG E δ hE hδ (hz zG (by simp)) hm
  dsimp only [fstarTypeWeight, monoTypeWeight, repeatedTypeWeight,
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
    | exact h6
    | exact h7
    | exact hM

theorem exists_type_correction_Fstar (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p Fstar g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p Fstar w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b12 := abs_le.mp (hbound 1 2)
  have b13 := abs_le.mp (hbound 1 3)
  have b23 := abs_le.mp (hbound 2 3)
  have b33 := abs_le.mp (hbound 3 3)
  let zA := (classTotal p g 0 0 - classTotal p g 0 1 - classTotal p g 0 2) / 6
  let zB := classTotal p g 0 1 / 2
  let zC := classTotal p g 0 2 / 2
  let zD : ℝ := 0
  let zE := classTotal p g 1 2
  let zF := (classTotal p g 1 3 - classTotal p g 1 2) / 2
  let zG := (classTotal p g 2 3 - classTotal p g 1 2) / 2
  let zH := (classTotal p g 3 3 - classTotal p g 1 3 - classTotal p g 2 3 +
    2 * classTotal p g 1 2) / 6
  have hzA : |zA| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [zA] <;> linarith
  have hzH : |zH| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [zH] <;> linarith
  have hz : ∀ z ∈ [zB, zC, zD, zE, zF, zG], |z| ≤ 8 * E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> dsimp only [zB, zC, zD, zE, zF, zG] <;> linarith
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨fstarTypeWeight p zA zB zC zD zE zF zG zH, fstarTypeWeight_symmetric p _ _ _ _ _ _ _ _,
    fstarTypeWeight_supported p _ _ _ _ _ _ _ _, ?_,
    fstarTypeWeight_bound p _ _ _ _ _ _ _ _ E δ hE hδ hzA hzH hz hm⟩
  rw [fstarTypeWeight_totals p _ _ _ _ _ _ _ _ hn hn1 hn2, classTotal_fstarRealMatrix p g hsym hs]
  congr 1 <;> dsimp only [zA, zB, zC, zD, zE, zF, zG, zH] <;> ring

/-! ### Stage 2: vertex rows -/

def fstarVertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  -- class 0: rows toward 0, 1, 2
  repeatedVertexWeight p 0 1 (fun v => (d v 0 + d v 1 - d v 2) / 2) a b c +
  repeatedVertexWeight p 0 2 (fun v => (d v 0 + d v 2 - d v 1) / 2) a b c +
  tripartiteVertexWeight p 0 1 2 (fun v => (d v 1 + d v 2 - d v 0) / 2) a b c +
  -- class 3: rows toward 1, 2, 3
  repeatedVertexWeight p 3 1 (fun v => (d v 3 + d v 1 - d v 2) / 2) a b c +
  repeatedVertexWeight p 3 2 (fun v => (d v 3 + d v 2 - d v 1) / 2) a b c +
  tripartiteVertexWeight p 3 1 2 (fun v => (d v 1 + d v 2 - d v 3) / 2) a b c +
  -- class 1: rows toward 0, 2, 3
  tripartiteVertexWeight p 1 0 2 (fun v => d v 2) a b c +
  singletonVertexWeight p 0 1 (fun v => (d v 0 - d v 2) / 2) a b c +
  singletonVertexWeight p 3 1 (fun v => d v 3 / 2) a b c +
  -- class 2: rows toward 0, 1, 3
  tripartiteVertexWeight p 2 0 1 (fun v => d v 1) a b c +
  singletonVertexWeight p 0 2 (fun v => (d v 0 - d v 1) / 2) a b c +
  singletonVertexWeight p 3 2 (fun v => d v 3 / 2) a b c

theorem fstarVertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (fstarVertexWeight p d) := by
  unfold fstarVertexWeight
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem fstarVertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p Fstar (fstarVertexWeight p d) := by
  unfold fstarVertexWeight
  repeat' first
    | exact aabLift_supported p Fstar _ _ (by decide) (by unfold Link Fstar; decide) _
    | exact abcLift_supported p Fstar _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Fstar; decide) _
    | apply TernarySupported.add

theorem fstarVertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p Fstar d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (fstarVertexWeight p d)) a k = d a k := by
  unfold VertexDemandZero at hz
  have z3 : ∀ (i x y w : Fin 4), (∑ v ∈ classVertices p i, (d v x + d v y - d v w) / 2) = 0 := by
    intro i x y w
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have z2 : ∀ (i x y : Fin 4), (∑ v ∈ classVertices p i, (d v x - d v y) / 2) = 0 := by
    intro i x y
    simp only [← sum_div, sum_sub_distrib, hz, sub_self, zero_div]
  have z1 : ∀ (i x : Fin 4), (∑ v ∈ classVertices p i, d v x / 2) = 0 := by
    intro i x; rw [← sum_div, hz, zero_div]
  unfold fstarVertexWeight
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p 0 1 _ (z3 0 0 1 2) (hm2 0) (hm 1),
    repeatedVertexWeight_rows p 0 2 _ (z3 0 0 2 1) (hm2 0) (hm 2),
    tripartiteVertexWeight_rows p 0 1 2 _ (z3 0 1 2 0) (hm 1) (hm 2),
    repeatedVertexWeight_rows p 3 1 _ (z3 3 3 1 2) (hm2 3) (hm 1),
    repeatedVertexWeight_rows p 3 2 _ (z3 3 3 2 1) (hm2 3) (hm 2),
    tripartiteVertexWeight_rows p 3 1 2 _ (z3 3 1 2 3) (hm 1) (hm 2),
    tripartiteVertexWeight_rows p 1 0 2 _ (hz 1 2) (hm 0) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (z2 1 0 2) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 3 1 _ (z1 1 3) (hm 3) (hm1 3),
    tripartiteVertexWeight_rows p 2 0 1 _ (hz 2 1) (hm 0) (hm 1),
    singletonVertexWeight_rows p 0 2 _ (z2 2 0 1) (hm 0) (hm1 0),
    singletonVertexWeight_rows p 3 2 _ (z1 2 3) (hm 3) (hm1 3)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp
  all_goals first
    | exact (hforb (by unfold Link Fstar; decide)).symm
    | ring

theorem fstarVertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fstarVertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc (v : V) (x y w : Fin 4) := triangle_link_bound _ _ _ D (hd v x) (hd v y) (hd v w)
  have hs1 (v : V) (x y z : Fin 4) := star_loop_link_bound _ _ _ D (hd v x) (hd v y) (hd v z)
  have hb (f : V → ℝ) (hf : ∀ v, |f v| ≤ 2 * D) :=
    vertexMode_bounds p f (2 * D) δ h2D hδ hf hm a b c
  have hdd (v : V) (x : Fin 4) : |d v x| ≤ 2 * D := by have := hd v x; linarith
  have e1 := (hb _ (fun v => (hc v 0 1 2).1)).1 0 1
  have e2 := (hb _ (fun v => (hc v 0 2 1).1)).1 0 2
  have e3 := (hb _ (fun v => (hc v 1 2 0).1)).2.2 0 1 2
  have e4 := (hb _ (fun v => (hc v 3 1 2).1)).1 3 1
  have e5 := (hb _ (fun v => (hc v 3 2 1).1)).1 3 2
  have e6 := (hb _ (fun v => (hc v 1 2 3).1)).2.2 3 1 2
  have e7 := (hb _ (fun v => hdd v 2)).2.2 1 0 2
  have e8 := (hb (fun v => (d v 0 - d v 2) / 2) (fun v => by
    have := (hs1 v 2 0 3).2.2.1; linarith)).2.1 0 1
  have e9 := (hb (fun v => d v 3 / 2) (fun v => by
    have := (hs1 v 2 0 3).2.2.2; linarith)).2.1 3 1
  have e10 := (hb _ (fun v => hdd v 1)).2.2 2 0 1
  have e11 := (hb (fun v => (d v 0 - d v 1) / 2) (fun v => by
    have := (hs1 v 1 0 3).2.2.1; linarith)).2.1 0 2
  have e12 := (hb (fun v => d v 3 / 2) (fun v => by
    have := (hs1 v 1 0 3).2.2.2; linarith)).2.1 3 2
  unfold fstarVertexWeight
  have hM288 : 288 * D / δ ^ 2 = 12 * (12 * (2 * D) / δ ^ 2) := by ring
  rw [hM288]
  generalize 12 * (2 * D) / δ ^ 2 = M at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 ⊢
  rw [abs_le] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2,
    e6.1, e6.2, e7.1, e7.2, e8.1, e8.2, e9.1, e9.2, e10.1, e10.2, e11.1, e11.2, e12.1, e12.2]

/-! ### Stage 3: zero rows -/

def fstarZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c + internalPairWeight p 3 1 g a b c +
  repeatedPairWeight p 0 1 g a b c + repeatedPairWeight p 0 2 g a b c +
  tripartitePairWeight p 1 2 0 g a b c + repeatedPairWeight p 3 1 g a b c +
  repeatedPairWeight p 3 2 g a b c

theorem fstarZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (fstarZeroRowWeight p g) := by
  unfold fstarZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem fstarZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p Fstar (fstarZeroRowWeight p g) := by
  unfold fstarZeroRowWeight
  repeat' first
    | exact aabLift_supported p Fstar _ _ (by decide) (by unfold Link Fstar; decide) _
    | exact abcLift_supported p Fstar _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link Fstar; decide) _
    | apply TernarySupported.add

theorem fstarZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link Fstar (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (fstarZeroRowWeight p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  unfold fstarZeroRowWeight
  simp only [ternaryLoad_add, hint, hrep, htri]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link Fstar; decide)).symm

theorem fstarZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |fstarZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := hi 0 1
  have h1 := hi 3 1
  have h2 := hr 0 1
  have h3 := hr 0 2
  have h4 := ht 1 2 0
  have h5 := hr 3 1
  have h6 := hr 3 2
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 h6 hpos ⊢
  unfold fstarZeroRowWeight
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2,
    h5.1, h5.2, h6.1, h6.2]

/-! ### The complete inverse and the certificate -/

theorem exists_complete_inverse_Fstar (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p Fstar g) (hg : ∀ a b, |g a b| ≤ ε) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p Fstar w ∧
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
      TernarySymmetric w ∧ TernarySupported p Fstar w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p Fstar g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_Fstar p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨fstarVertexWeight p d, fstarVertexWeight_symmetric p d,
        fstarVertexWeight_supported p d, fstarVertexWeight_rows p d hz hds hm hm1 hm2, ?_⟩
      intro a b c
      exact he1 ▸ fstarVertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨fstarZeroRowWeight p f, fstarZeroRowWeight_symmetric p f hf,
        fstarZeroRowWeight_supported p f, fstarZeroRowWeight_load p f hf hr hfd hfs hm hm2, ?_⟩
      intro a b c
      exact he2 ▸ fstarZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

/-- **`CompleteInverseCert Fstar`** (no compatibility condition is needed). -/
theorem completeInverseCert_Fstar : PaddedGeneral.CompleteInverseCert Fstar := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_Fstar p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hs.edgeSupported
    (fun a b => hr s(a, b))
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p Fstar w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p Fstar (activeCompleteGraph p Fstar) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p Fstar (activeCompleteGraph p Fstar) z,
    copyRestriction_supported p Fstar (activeCompleteGraph p Fstar) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p Fstar (activeCompleteGraph p Fstar) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p Fstar (activeCompleteGraph p Fstar) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

#print axioms monoTypeWeight_totals
#print axioms exists_complete_inverse_Fstar
#print axioms completeInverseCert_Fstar

end PaddedFstar
