/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.MonoMode

@[expose] public section

/-!
# The monochromatic vertex mode

`monoVertexWeight p i f` puts weight `(f a + f b + f c) / ((s - 2)(s - 3))` (`s = |V_i|`) on every
ordered triple of distinct vertices of `V_i`. If `∑_{V_i} f = 0` its load is the internal vertex
kernel `(f a + f b)/(s - 2)` on `V_i`, so its only nonzero rows are `row(a, i) = f a` for `a ∈ V_i`.

This corrects the row of a vertex towards its own class using only the type `{i, i, i}`. It is the
vertex mode that was missing for families in which a class sees its own class only through
`{i,i,i}` (for instance `{000, 001}`: a class-0 vertex has rows `0` and `1`, and `001` alone
moves both together).
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

/-- The monochromatic vertex weight. -/
def monoVertexWeight (p : V → Fin t) (i : Fin t) (f : V → ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    (f a + f b + f c) / ((classSize p i - 2) * (classSize p i - 3)) else 0

theorem monoVertexWeight_symmetric (p : V → Fin t) (i : Fin t) (f : V → ℝ) :
    TernarySymmetric (monoVertexWeight p i f) := by
  constructor
  · intro a b c
    unfold monoVertexWeight
    by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩]
      ring
    · have h' : ¬ (p b = i ∧ p a = i ∧ p c = i ∧ b ≠ a ∧ b ≠ c ∧ a ≠ c) := by
        rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact h ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩
      rw [if_neg h, if_neg h']
  · intro a b c
    unfold monoVertexWeight
    by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩]
      ring
    · have h' : ¬ (p a = i ∧ p c = i ∧ p b = i ∧ a ≠ c ∧ a ≠ b ∧ c ≠ b) := by
        rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact h ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩
      rw [if_neg h, if_neg h']

theorem monoVertexWeight_supported (p : V → Fin t) (F : Finset (Multiset (Fin t))) (i : Fin t)
    (hF : Link F i i i) (f : V → ℝ) : TernarySupported p F (monoVertexWeight p i f) := by
  intro a b c hbad
  unfold monoVertexWeight
  split_ifs with h
  · exfalso
    apply hbad
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩
  · rfl

theorem sum_erase_erase_class (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ c ∈ classVertices p i, f c = 0) (a b : V) (ha : p a = i) (hb : p b = i)
    (hab : a ≠ b) :
    ∑ c ∈ ((classVertices p i).erase a).erase b, f c = -f a - f b := by
  have hamem : a ∈ classVertices p i := (mem_classVertices p i a).mpr ha
  have hbmem : b ∈ (classVertices p i).erase a :=
    mem_erase.mpr ⟨Ne.symm hab, (mem_classVertices p i b).mpr hb⟩
  have h1 := sum_erase_add (classVertices p i) f hamem
  have h2 := sum_erase_add ((classVertices p i).erase a) f hbmem
  linarith

/-- The load of the monochromatic vertex weight is the internal vertex kernel. -/
theorem monoVertexWeight_load (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ c ∈ classVertices p i, f c = 0)
    (hi2 : classSize p i - 2 ≠ 0) (hi3 : classSize p i - 3 ≠ 0) (a b : V) :
    ternaryLoad (monoVertexWeight p i f) a b = vertexInternalKernel p i f a b := by
  unfold ternaryLoad monoVertexWeight vertexInternalKernel
  by_cases hab : p a = i ∧ p b = i
  · obtain ⟨ha, hb⟩ := hab
    by_cases he : a = b
    · subst he
      simp
    · simp only [ha, hb, true_and, ne_eq, he, not_false_eq_true, and_self, ite_true]
      have hsum : (∑ c : V, if p c = i ∧ ¬a = c ∧ ¬b = c then
          (f a + f b + f c) / ((classSize p i - 2) * (classSize p i - 3)) else 0) =
          ∑ c ∈ ((classVertices p i).erase a).erase b,
            (f a + f b + f c) / ((classSize p i - 2) * (classSize p i - 3)) := by
        rw [← sum_filter]
        apply sum_congr _ (fun _ _ => rfl)
        ext c
        simp only [mem_filter, mem_univ, true_and, mem_erase, mem_classVertices]
        tauto
      rw [hsum, ← sum_div, sum_add_distrib, sum_const, nsmul_eq_mul,
        PaddedTrivial.card_erase_erase_class p i a b ha hb he, sum_erase_erase_class p i f hf a b ha hb he]
      field_simp
      ring
  · have : ∀ c, ¬ (p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :=
      fun c h => hab ⟨h.1, h.2.1⟩
    simp only [this, ite_false, sum_const_zero]
    exact (ite_eq_right_iff.mpr fun h => absurd h hab).symm

/-- **Rows of the monochromatic vertex weight.** -/
theorem monoVertexWeight_rows (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ c ∈ classVertices p i, f c = 0)
    (hi2 : classSize p i - 2 ≠ 0) (hi3 : classSize p i - 3 ≠ 0) (a : V) (k : Fin t) :
    classRow p (ternaryLoad (monoVertexWeight p i f)) a k =
      if p a = i ∧ k = i then f a else 0 := by
  have he : ternaryLoad (monoVertexWeight p i f) = vertexInternalKernel p i f := by
    funext a b
    exact monoVertexWeight_load p i f hf hi2 hi3 a b
  rw [he, classRow_vertexInternalKernel p i f hf hi2]

omit [Fintype V] [DecidableEq V] in
theorem abs_le_of_abs_le_three {x y z D : ℝ} (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |x + y + z| ≤ 3 * D := by
  rw [abs_le] at hx hy hz ⊢
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2]

/-- **Bound for the monochromatic vertex weight.** -/
theorem monoVertexWeight_bound (p : V → Fin t) (i : Fin t) (f : V → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hf : ∀ a, |f a| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |monoVertexWeight p i f a b c| ≤ 24 * D / δ ^ 2 := by
  have hd : 0 < δ := by linarith
  have hM : 0 ≤ 24 * D / δ ^ 2 := by positivity
  unfold monoVertexWeight
  split_ifs
  · have hs := hm i
    have h2 : δ / 2 ≤ classSize p i - 2 := by linarith
    have h3 : δ / 4 ≤ classSize p i - 3 := by linarith
    have hpos2 : 0 < classSize p i - 2 := by linarith
    have hpos3 : 0 < classSize p i - 3 := by linarith
    have hden : δ ^ 2 / 8 ≤ (classSize p i - 2) * (classSize p i - 3) := by
      have := mul_le_mul h2 h3 (by positivity) hpos2.le
      nlinarith
    have hdenpos : 0 < (classSize p i - 2) * (classSize p i - 3) := by positivity
    have hnum := abs_le_of_abs_le_three (hf a) (hf b) (hf c)
    rw [abs_div, abs_of_pos hdenpos, div_le_div_iff₀ hdenpos (by positivity)]
    have hnum0 : 0 ≤ |f a + f b + f c| := abs_nonneg _
    nlinarith [mul_le_mul hnum hden (by positivity) (by linarith)]
  · simpa using hM

end PaddedComponents

#print axioms PaddedComponents.monoVertexWeight_rows
#print axioms PaddedComponents.monoVertexWeight_bound
