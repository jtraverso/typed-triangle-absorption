/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoVertexMode
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ReductionLarge

@[expose] public section

/-!
# The inverse frame for classes of size at least 8, and the monochromatic zero-row mode

* `monoPairWeight p i g` puts weight `(g ab + g ac + g bc)/(s - 4)` on the ordered triples of
  distinct vertices of `V_i`. If the class rows of `g` vanish, its load is `g` on the pairs inside
  `V_i` (and `0` elsewhere). This is the zero-row mode of an isolated monochromatic class; it needs
  `s ≥ 5` (in `K₄` it does not exist, see `MonoObstruction.lean`).
* `TernaryInverse₈ F` is `TernaryInverse F` under `8 ≤ γ n`, and
  `completeInverseCert₈_of_ternary` gives `CompleteInverseCert₈ F` for every `F ⊇ F₀` with the same
  allowed pairs.
-/

noncomputable section

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedF12 PaddedGeneral PaddedNoCommon

section Mode

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

/-- The monochromatic zero-row weight. -/
def monoPairWeight (p : V → Fin t) (i : Fin t) (g : V → V → ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    (g a b + g a c + g b c) / (classSize p i - 4) else 0

theorem monoPairWeight_symmetric (p : V → Fin t) (i : Fin t) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (monoPairWeight p i g) := by
  constructor
  · intro a b c
    unfold monoPairWeight
    by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩, hs b a]
      ring
    · have h' : ¬ (p b = i ∧ p a = i ∧ p c = i ∧ b ≠ a ∧ b ≠ c ∧ a ≠ c) := by
        rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact h ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩
      rw [if_neg h, if_neg h']
  · intro a b c
    unfold monoPairWeight
    by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩, hs c b]
      ring
    · have h' : ¬ (p a = i ∧ p c = i ∧ p b = i ∧ a ≠ c ∧ a ≠ b ∧ c ≠ b) := by
        rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact h ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩
      rw [if_neg h, if_neg h']

theorem monoPairWeight_supported (p : V → Fin t) (F : Finset (Multiset (Fin t))) (i : Fin t)
    (hF : Link F i i i) (g : V → V → ℝ) : TernarySupported p F (monoPairWeight p i g) := by
  intro a b c hbad
  unfold monoPairWeight
  split_ifs with h
  · exfalso
    apply hbad
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩
  · rfl

theorem sum_erase_erase_row (p : V → Fin t) (i : Fin t) (g : V → V → ℝ)
    (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0) (hs : ∀ a b, g a b = g b a)
    (x a b : V) (hx : x = a ∨ x = b) (ha : p a = i) (hb : p b = i) (hab : a ≠ b) :
    ∑ c ∈ ((classVertices p i).erase a).erase b, g x c = -g a b := by
  have hamem : a ∈ classVertices p i := (mem_classVertices p i a).mpr ha
  have hbmem : b ∈ (classVertices p i).erase a :=
    mem_erase.mpr ⟨Ne.symm hab, (mem_classVertices p i b).mpr hb⟩
  have h1 := sum_erase_add (classVertices p i) (g x) hamem
  have h2 := sum_erase_add ((classVertices p i).erase a) (g x) hbmem
  have h0 := hr x i
  rcases hx with rfl | rfl
  · rw [hd] at h1
    linarith
  · rw [hd] at h2
    rw [hs x a] at h1
    linarith

/-- The load of the monochromatic zero-row weight. -/
theorem monoPairWeight_load (p : V → Fin t) (i : Fin t) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hi4 : classSize p i - 4 ≠ 0) (a b : V) :
    ternaryLoad (monoPairWeight p i g) a b = if p a = i ∧ p b = i then g a b else 0 := by
  unfold ternaryLoad monoPairWeight
  by_cases hab : p a = i ∧ p b = i
  · obtain ⟨ha, hb⟩ := hab
    by_cases he : a = b
    · subst he
      simp [hd]
    · simp only [ha, hb, true_and, ne_eq, he, not_false_eq_true, and_self, ite_true]
      have hsum : (∑ c : V, if p c = i ∧ ¬a = c ∧ ¬b = c then
          (g a b + g a c + g b c) / (classSize p i - 4) else 0) =
          ∑ c ∈ ((classVertices p i).erase a).erase b,
            (g a b + g a c + g b c) / (classSize p i - 4) := by
        rw [← sum_filter]
        apply sum_congr _ (fun _ _ => rfl)
        ext c
        simp only [mem_filter, mem_univ, true_and, mem_erase, mem_classVertices]
        tauto
      rw [hsum, ← sum_div, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
        PaddedTrivial.card_erase_erase_class p i a b ha hb he,
        sum_erase_erase_row p i g hr hd hs a a b (Or.inl rfl) ha hb he,
        sum_erase_erase_row p i g hr hd hs b a b (Or.inr rfl) ha hb he]
      field_simp
      ring
  · have : ∀ c, ¬ (p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :=
      fun c h => hab ⟨h.1, h.2.1⟩
    simp only [this, ite_false, sum_const_zero]
    exact (ite_eq_right_iff.mpr fun h => absurd h hab).symm

/-- Bound for the monochromatic zero-row weight (classes of size at least `δ ≥ 8`). -/
theorem monoPairWeight_bound (p : V → Fin t) (i : Fin t) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |monoPairWeight p i g a b c| ≤ 12 * ε / δ := by
  have hd : 0 < δ := by linarith
  have hM : 0 ≤ 12 * ε / δ := by positivity
  unfold monoPairWeight
  split_ifs
  · have hs := hm i
    have h4 : δ / 2 ≤ classSize p i - 4 := by linarith
    have hpos4 : 0 < classSize p i - 4 := by linarith
    have hnum := abs_le_of_abs_le_three (hg a b) (hg a c) (hg b c)
    rw [abs_div, abs_of_pos hpos4, div_le_div_iff₀ hpos4 hd]
    have hnum0 : 0 ≤ |g a b + g a c + g b c| := abs_nonneg _
    nlinarith [mul_le_mul hnum h4 (by positivity) (by linarith)]
  · simpa using hM

end Mode

/-- The ternary bounded signed inverse for classes of size at least `8`. -/
def TernaryInverse₈ (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 8 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    (∀ a b, g a b = g b a) → (∀ a, g a a = 0) → EdgeSupported p F g →
    (∀ a b, |g a b| ≤ ε) →
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))

/-- **`CompleteInverseCert₈` from a ternary inverse of a base with the same allowed pairs.** -/
theorem completeInverseCert₈_of_ternary {F0 F : Finset (Multiset (Fin 4))} (hsub : F0 ⊆ F)
    (hallow : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link F0 i j k))
    (hT : TernaryInverse₈ F0) : CompleteInverseCert₈ F := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  have hsE : EdgeSupported p F0 (fun a b => r s(a, b)) := by
    intro a b hab
    exact hs.edgeSupported a b (fun h => hab ((hallow _ _).mp h))
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := hT V p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hsE
    (fun a b => hr s(a, b))
  have htwF : TernarySupported p F w := by
    intro a b c hna
    exact htw a b c fun h => hna ⟨h.1, h.2.1, h.2.2.1, hsub h.2.2.2⟩
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p F w hsw htwF _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p F (activeCompleteGraph p F) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p F (activeCompleteGraph p F) z,
    copyRestriction_supported p F (activeCompleteGraph p F) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p F (activeCompleteGraph p F) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p F (activeCompleteGraph p F) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

end PaddedComponents

#print axioms PaddedComponents.monoPairWeight_load
#print axioms PaddedComponents.monoPairWeight_bound
#print axioms PaddedComponents.completeInverseCert₈_of_ternary
