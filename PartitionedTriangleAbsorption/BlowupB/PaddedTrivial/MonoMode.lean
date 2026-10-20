/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Inverse

@[expose] public section

/-!
# The uniform physical lift of a monochromatic type `{i, i, i}`

`monoTypeWeight p i z` puts the same weight `6 z / (s (s - 1) (s - 2))` (`s = |V_i|`) on every
ordered triple of distinct vertices of `V_i`. Its class totals are `6 z` at `(i, i)` and zero
elsewhere, i.e. `z` times the ordered edge vector of `{i, i, i}`.
-/

noncomputable section

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

/-- The uniform weight on triangles inside one class. -/
def monoTypeWeight (p : V → Fin t) (i : Fin t) (z : ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) else 0

theorem monoTypeWeight_symmetric (p : V → Fin t) (i : Fin t) (z : ℝ) :
    TernarySymmetric (monoTypeWeight p i z) := by
  constructor
  · intro a b c
    unfold monoTypeWeight
    congr 1
    apply propext
    constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
      exact ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩
  · intro a b c
    unfold monoTypeWeight
    congr 1
    apply propext
    constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
      exact ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩

theorem monoTypeWeight_supported (p : V → Fin t) (F : Finset (Multiset (Fin t))) (i : Fin t)
    (hF : Link F i i i) (z : ℝ) : TernarySupported p F (monoTypeWeight p i z) := by
  intro a b c hbad
  unfold monoTypeWeight
  split_ifs with h
  · exfalso
    apply hbad
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩
  · rfl

theorem card_erase_erase_class (p : V → Fin t) (i : Fin t) (a b : V) (ha : p a = i)
    (hb : p b = i) (hab : a ≠ b) :
    ((((classVertices p i).erase a).erase b).card : ℝ) = classSize p i - 2 := by
  have hamem : a ∈ classVertices p i := (mem_classVertices p i a).mpr ha
  have hbmem : b ∈ (classVertices p i).erase a :=
    mem_erase.mpr ⟨Ne.symm hab, (mem_classVertices p i b).mpr hb⟩
  rw [card_erase_of_mem hbmem, card_erase_of_mem hamem]
  have h2 : 2 ≤ (classVertices p i).card := by
    have : 1 ≤ ((classVertices p i).erase a).card := card_pos.mpr ⟨b, hbmem⟩
    rw [card_erase_of_mem hamem] at this
    omega
  unfold classSize
  rw [Nat.sub_sub, Nat.cast_sub h2]
  norm_num

theorem monoTypeWeight_load (p : V → Fin t) (i : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (hi2 : classSize p i - 2 ≠ 0)
    (a b : V) :
    ternaryLoad (monoTypeWeight p i z) a b =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) a b := by
  unfold ternaryLoad monoTypeWeight constInternalBlock
  by_cases hab : p a = i ∧ p b = i
  · obtain ⟨ha, hb⟩ := hab
    by_cases he : a = b
    · subst he
      simp
    · simp only [ha, hb, true_and, ne_eq, he, not_false_eq_true, and_self, ite_true]
      have hsum : (∑ c : V, if p c = i ∧ ¬a = c ∧ ¬b = c then
          6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) else 0) =
          ∑ c ∈ ((classVertices p i).erase a).erase b,
            6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) := by
        rw [← sum_filter]
        apply sum_congr _ (fun _ _ => rfl)
        ext c
        simp only [mem_filter, mem_univ, true_and, mem_erase, mem_classVertices]
        tauto
      rw [hsum, sum_const, nsmul_eq_mul, card_erase_erase_class p i a b ha hb he]
      field_simp
  · have : ∀ c, ¬ (p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :=
      fun c h => hab ⟨h.1, h.2.1⟩
    simp only [this, ite_false, sum_const_zero]
    exact (ite_eq_right_iff.mpr fun h => absurd h hab).symm

theorem monoTypeWeight_totals (p : V → Fin t) (i : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (hi2 : classSize p i - 2 ≠ 0)
    (k l : Fin t) :
    classTotal p (ternaryLoad (monoTypeWeight p i z)) k l =
      if k = i ∧ l = i then 6 * z else 0 := by
  have he : ternaryLoad (monoTypeWeight p i z) =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) := by
    funext a b
    exact monoTypeWeight_load p i z hi hi1 hi2 a b
  rw [he, classTotal_constInternalBlock]
  have h : classSize p i * (classSize p i - 1) *
      (6 * z / (classSize p i * (classSize p i - 1))) = 6 * z := by field_simp
  rw [h]

omit [DecidableEq V] in
theorem monoType_normalizer_bound (p : V → Fin t) (i : Fin t) (z E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz : |z| ≤ 2 * E) (hm : ∀ i, δ ≤ classSize p i) :
    |6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2))| ≤
      32 * E / δ ^ 3 := by
  have hd : 0 < δ := by linarith
  have hs := hm i
  have hpos : 0 < classSize p i := by linarith
  have hpos1 : 3 * δ / 4 ≤ classSize p i - 1 := by linarith
  have hpos2 : δ / 2 ≤ classSize p i - 2 := by linarith
  have hdenpos : 0 < classSize p i * (classSize p i - 1) * (classSize p i - 2) := by
    have h1 : 0 < classSize p i - 1 := by linarith
    have h2 : 0 < classSize p i - 2 := by linarith
    positivity
  have hden : 3 * δ ^ 3 / 8 ≤ classSize p i * (classSize p i - 1) * (classSize p i - 2) := by
    have h1 := mul_le_mul hs hpos1 (by positivity) hpos.le
    have h2 := mul_le_mul h1 hpos2 (by positivity) (by nlinarith)
    nlinarith
  have hnum : |6 * z| ≤ 12 * E := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    linarith
  apply (uniform_bound (6 * z) (12 * E) _ hnum hdenpos).trans
  rw [div_le_div_iff₀ hdenpos (pow_pos hd 3)]
  nlinarith [mul_nonneg hE (sub_nonneg.mpr hden)]

end PaddedTrivial
