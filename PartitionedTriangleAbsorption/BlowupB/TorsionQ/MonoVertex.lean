/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse

@[expose] public section

/-!
# A monochromatic VERTEX mode (type `iii`)

`monoVertexWeight p i f` spreads `2 (f a + f b + f c) / ((m - 2)(m - 3))` (with `m = |V_i|`) over the
ordered triples of distinct `V_i`-vertices. When `∑_{V_i} f = 0` its class rows are exactly
`2 f a` toward `i` for `a ∈ V_i`, and `0` otherwise (`monoVertexWeight_rows`). It is needed for
families whose class-`i` vertex demands are not spanned by the repeated, singleton and tripartite
modes (e.g. class 3 of `KZ3`, which only has the types `123`, `133`, `333` through class 3).
-/

noncomputable section

namespace TorsionQ.KZ3

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

def monoVertexWeight (p : V → Fin 4) (i : Fin 4) (f : V → ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    2 * (f a + f b + f c) / ((classSize p i - 2) * (classSize p i - 3)) else 0

theorem monoVertexWeight_symmetric (p : V → Fin 4) (i : Fin 4) (f : V → ℝ) :
    TernarySymmetric (monoVertexWeight p i f) := by
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩ <;> unfold monoVertexWeight
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩]
      ring_nf
    · rw [if_neg h, if_neg]
      rintro ⟨h2, h1, h3, h4, h6, h5⟩
      exact h ⟨h1, h2, h3, Ne.symm h4, h5, h6⟩
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩]
      ring_nf
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h3, h2, h5, h4, h6⟩
      exact h ⟨h1, h2, h3, h4, h5, Ne.symm h6⟩

theorem monoVertexWeight_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (i : Fin 4)
    (hF : Link F i i i) (f : V → ℝ) : TernarySupported p F (monoVertexWeight p i f) := by
  intro a b c hbad
  unfold monoVertexWeight
  rw [if_neg]
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact hbad ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩

theorem card_classVertices_cast (p : V → Fin 4) (i : Fin 4) :
    ((classVertices p i).card : ℝ) = classSize p i := rfl

/-- The pair load of the monochromatic vertex mode. -/
theorem monoVertexWeight_pair (p : V → Fin 4) (i : Fin 4) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0) {a b : V} (ha : p a = i) (hb : p b = i)
    (hab : a ≠ b) :
    ternaryLoad (monoVertexWeight p i f) a b =
      2 * ((classSize p i - 3) * (f a + f b)) / ((classSize p i - 2) * (classSize p i - 3)) := by
  classical
  unfold ternaryLoad monoVertexWeight
  have hset : (univ.filter fun c => p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) =
      ((classVertices p i).erase a).erase b := by
    ext c
    rw [mem_filter, mem_erase, mem_erase]
    simp only [mem_univ, true_and, mem_classVertices]
    constructor
    · rintro ⟨-, -, h3, -, h5, h6⟩; exact ⟨Ne.symm h6, Ne.symm h5, h3⟩
    · rintro ⟨h6, h5, h3⟩; exact ⟨ha, hb, h3, hab, Ne.symm h5, Ne.symm h6⟩
  have haV : a ∈ classVertices p i := by simp [ha]
  have hbV : b ∈ (classVertices p i).erase a := by simp [hb, Ne.symm hab]
  have hcard : (((classVertices p i).erase a).erase b).card = (classVertices p i).card - 2 := by
    rw [card_erase_of_mem hbV, card_erase_of_mem haV]
    omega
  have hge : 2 ≤ (classVertices p i).card := by
    have h1 := card_erase_of_mem haV
    have h2 : 0 < ((classVertices p i).erase a).card := card_pos.mpr ⟨b, hbV⟩
    omega
  rw [← sum_filter, hset]
  have hsumf : ∑ c ∈ ((classVertices p i).erase a).erase b, f c = - f a - f b := by
    rw [sum_erase_eq_sub hbV, sum_erase_eq_sub haV, hf]; ring
  have hcast : (((classVertices p i).card - 2 : ℕ) : ℝ) = classSize p i - 2 := by
    unfold classSize; rw [Nat.cast_sub hge]; norm_num
  simp only [← sum_div, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, hcard, hcast, hsumf]
  congr 1
  ring

theorem monoVertexWeight_rows (p : V → Fin 4) (i : Fin 4) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0)
    (hm2 : classSize p i - 2 ≠ 0) (hm3 : classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (monoVertexWeight p i f)) a k =
      if p a = i ∧ k = i then 2 * f a else 0 := by
  classical
  unfold classRow
  by_cases hak : p a = i ∧ k = i
  · obtain ⟨ha, hk⟩ := hak
    subst k
    rw [if_pos ⟨ha, rfl⟩]
    have haV : a ∈ classVertices p i := by simp [ha]
    rw [← add_sum_erase _ _ haV]
    have hzero : ternaryLoad (monoVertexWeight p i f) a a = 0 := by
      unfold ternaryLoad monoVertexWeight
      apply sum_eq_zero; intro c _; rw [if_neg]; rintro ⟨-, -, -, h, -, -⟩; exact h rfl
    rw [hzero, zero_add]
    have hterm : ∀ b ∈ (classVertices p i).erase a,
        ternaryLoad (monoVertexWeight p i f) a b =
          2 * ((classSize p i - 3) * (f a + f b)) /
            ((classSize p i - 2) * (classSize p i - 3)) := by
      intro b hb
      have hb' := mem_erase.mp hb
      exact monoVertexWeight_pair p i f hf ha ((mem_classVertices _ _ _).mp hb'.2) (Ne.symm hb'.1)
    rw [sum_congr rfl hterm]
    have hsumf : ∑ b ∈ (classVertices p i).erase a, f b = - f a := by
      rw [sum_erase_eq_sub haV, hf]; ring
    have hcard : (((classVertices p i).erase a).card : ℝ) = classSize p i - 1 := by
      rw [card_erase_of_mem haV]
      have : 1 ≤ (classVertices p i).card := card_pos.mpr ⟨a, haV⟩
      unfold classSize; rw [Nat.cast_sub this]; norm_num
    rw [← sum_div, ← mul_sum, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, hcard, hsumf]
    field_simp
    ring
  · rw [if_neg hak]
    apply sum_eq_zero
    intro b hb
    unfold ternaryLoad monoVertexWeight
    apply sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨h1, h2, -, -, -, -⟩
    exact hak ⟨h1, by rw [← (mem_classVertices _ _ _).mp hb, h2]⟩

theorem monoVertexWeight_bound (p : V → Fin 4) (i : Fin 4) (f : V → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hf : ∀ a, |f a| ≤ D) (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |monoVertexWeight p i f a b c| ≤ 48 * D / δ ^ 2 := by
  have hmi := hm i
  set m := classSize p i with hmdef
  have hd : 0 < δ := by linarith
  have hM : 0 ≤ 48 * D / δ ^ 2 := by positivity
  unfold monoVertexWeight
  split_ifs
  · have h2 : m / 2 ≤ m - 2 := by linarith
    have h3 : m / 4 ≤ m - 3 := by linarith
    have hden : δ ^ 2 / 8 ≤ (m - 2) * (m - 3) := by
      have hδm : δ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hd.le hmi 2
      have hprod : (m / 2) * (m / 4) ≤ (m - 2) * (m - 3) :=
        mul_le_mul h2 h3 (by linarith) (by linarith)
      nlinarith
    have hdenpos : 0 < (m - 2) * (m - 3) := lt_of_lt_of_le (by positivity) hden
    have hsum : |f a + f b + f c| ≤ 3 * D := by
      have := hf a; have := hf b; have := hf c
      calc |f a + f b + f c| ≤ |f a + f b| + |f c| := abs_add_le _ _
        _ ≤ |f a| + |f b| + |f c| := by linarith [abs_add_le (f a) (f b)]
        _ ≤ 3 * D := by linarith
    rw [abs_div, abs_of_pos hdenpos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [div_le_div_iff₀ hdenpos (by positivity)]
    have h6 : 2 * |f a + f b + f c| ≤ 6 * D := by linarith
    nlinarith [mul_le_mul h6 hden (by positivity) (by positivity)]
  · rw [abs_zero]; exact hM

end TorsionQ.KZ3

#print axioms TorsionQ.KZ3.monoVertexWeight_rows
#print axioms TorsionQ.KZ3.monoVertexWeight_bound
