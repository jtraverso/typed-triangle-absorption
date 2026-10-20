/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingPivot
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Finite descent for integral flow rounding. The pivot and the termination
argument are proved here. The final graph-specific obligation is that a
nonintegral flow with integral divergence has a signed fractional cycle. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingDescent

variable {E W : Type*} [Fintype E] [AddCommGroup W] [Module ℝ W]

noncomputable def fractional (f : E → ℝ) : Finset E := by
  classical
  exact Finset.univ.filter fun e => f e ∉ Set.range (Int.cast : ℤ → ℝ)

@[simp] theorem mem_fractional (f : E → ℝ) (e : E) :
    e ∈ fractional f ↔ f e ∉ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  simp [fractional]

/-- One signed cycle strictly reduces the fractional support while
preserving the linear image and the original integral box. -/
theorem decrease (B : (E → ℝ) →ₗ[ℝ] W) (f d : E → ℝ)
    (lower upper : E → ℤ) (s : Finset E) (hs : s.Nonempty)
    (hsub : s ⊆ fractional f)
    (hbox : ∀ e, (lower e : ℝ) ≤ f e ∧ f e ≤ (upper e : ℝ))
    (hsign : ∀ e ∈ s, d e = 1 ∨ d e = -1)
    (hzero : ∀ e ∉ s, d e = 0) (hkernel : B d = 0) :
    ∃ g : E → ℝ, B g = B f ∧
      (∀ e, (lower e : ℝ) ≤ g e ∧ g e ≤ (upper e : ℝ)) ∧
      (fractional g).card < (fractional f).card := by
  classical
  have hstrict : ∀ e ∈ s, (lower e : ℝ) < f e ∧ f e < (upper e : ℝ) := by
    intro e he
    have hn := (mem_fractional f e).mp (hsub he)
    have hl : (lower e : ℝ) ≠ f e := fun h => hn ⟨lower e, h⟩
    have hu : (upper e : ℝ) ≠ f e := fun h => hn ⟨upper e, h⟩
    constructor
    · by_contra h
      apply hl
      linarith [hbox e]
    · by_contra h
      apply hu
      linarith [hbox e]
  obtain ⟨t, -, hB, hbox', hsame, e₀, he₀, hbound⟩ :=
    FlowRoundingPivot.first_boundary B f d (fun e => (lower e : ℝ))
      (fun e => (upper e : ℝ)) s hs hbox hstrict hsign hzero hkernel
  refine ⟨f + t • d, hB, hbox', Finset.card_lt_card ?_⟩
  have hsubset : fractional (f + t • d) ⊆ fractional f := by
    intro e he
    by_cases hes : e ∈ s
    · exact hsub hes
    · simpa only [mem_fractional, hsame e hes] using he
  apply (Finset.ssubset_iff_of_subset hsubset).mpr
  refine ⟨e₀, hsub he₀, ?_⟩
  rw [mem_fractional]
  intro hn
  apply hn
  rcases hbound with hl | hu
  · exact ⟨lower e₀, hl.symm⟩
  · exact ⟨upper e₀, hu.symm⟩

/-- Every feasible integral box has a representative with the same image
and no nonempty signed kernel direction supported on fractional entries.
No graph-cycle existence or integrality theorem is assumed. -/
theorem reduced_representative (B : (E → ℝ) →ₗ[ℝ] W)
    (f : E → ℝ) (lower upper : E → ℤ)
    (hbox : ∀ e, (lower e : ℝ) ≤ f e ∧ f e ≤ (upper e : ℝ)) :
    ∃ g : E → ℝ, B g = B f ∧
      (∀ e, (lower e : ℝ) ≤ g e ∧ g e ≤ (upper e : ℝ)) ∧
      ∀ (s : Finset E) (d : E → ℝ), s.Nonempty → s ⊆ fractional g →
        (∀ e ∈ s, d e = 1 ∨ d e = -1) →
        (∀ e ∉ s, d e = 0) → B d = 0 → False := by
  classical
  let P : ℕ → Prop := fun k => ∃ g : E → ℝ, B g = B f ∧
    (∀ e, (lower e : ℝ) ≤ g e ∧ g e ≤ (upper e : ℝ)) ∧ (fractional g).card = k
  have hex : ∃ k, P k := ⟨(fractional f).card, f, rfl, hbox, rfl⟩
  obtain ⟨g, hg, hgb, hgc⟩ := Nat.find_spec hex
  refine ⟨g, hg, hgb, ?_⟩
  intro s d hs hsub hsign hzero hkernel
  obtain ⟨g', hg', hgb', hc⟩ := decrease B g d lower upper s hs hsub hgb hsign hzero hkernel
  have hmin : Nat.find hex ≤ (fractional g').card :=
    Nat.find_min' hex ⟨g', hg'.trans hg, hgb', rfl⟩
  rw [hgc] at hc
  exact (not_lt_of_ge hmin) hc

end PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingDescent

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingDescent.decrease
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingDescent.reduced_representative
