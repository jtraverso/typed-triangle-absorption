/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction
public import PartitionedTriangleAbsorption.BlowupB.TeoremaBBalanced

@[expose] public section

/-!
# The trivial-lattice family `Ftriv` on four classes

`Ftriv = {000, 001, 002, 012, 123, 133, 233, 333}`.

Its allowed class pairs are `00, 01, 02, 12, 13, 23, 33`; the forbidden ones are
`03, 11, 22`. Among the 765 families on four classes (up to relabelling) with a forbidden
partner for every class and using all classes, it is the only one whose integral divisibility
on allowed-support graphs is exactly ordinary divisibility (even degrees and `3 ∣ e`), which
satisfies `ThreeStepLinks`, and in which every two classes have a common allowed partner
(census in `PROOF.md`, computed by `scripts/analyze2.py`; this census is exploratory and not
part of the Lean development).

This file records the finite facts, all checked by `decide`.
-/

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer

/-- The trivial-lattice family. -/
noncomputable def Ftriv : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {2, 3, 3}, {3, 3, 3}}

theorem Ftriv_card_three : ∀ τ ∈ Ftriv, Multiset.card τ = 3 := by
  unfold Ftriv; decide

/-- The allowed pairs of `Ftriv`: all pairs except `03`, `11`, `22`. -/
def trivAllowed (i j : Fin 4) : Prop :=
  s(i, j) ≠ s(0, 3) ∧ s(i, j) ≠ s(1, 1) ∧ s(i, j) ≠ s(2, 2)

instance (i j : Fin 4) : Decidable (trivAllowed i j) := by
  unfold trivAllowed; infer_instance

theorem Ftriv_allowed_iff : ∀ i j : Fin 4, (∃ k, Link Ftriv i j k) ↔ trivAllowed i j := by
  unfold Link Ftriv trivAllowed; decide

theorem Ftriv_three_step : ThreeStepLinks Ftriv := by
  unfold ThreeStepLinks Link Ftriv; decide

theorem Ftriv_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link Ftriv a c k) ∧ (∃ k, Link Ftriv b c k) := by
  unfold Link Ftriv; decide

theorem Ftriv_allowed_of_triangle : ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ Ftriv →
    (∃ a, Link Ftriv i k a) ∧ (∃ a, Link Ftriv j k a) := by
  unfold Link Ftriv; decide

theorem Ftriv_forbidden : ∀ i : Fin 4, ∃ j, ¬ ∃ k, Link Ftriv i j k := by
  unfold Link Ftriv; decide

theorem familyFacts_Ftriv : PaddedGeneral.FamilyFacts Ftriv :=
  ⟨Ftriv_card_three, Ftriv_allowed_of_triangle, Ftriv_forbidden⟩


theorem sum_completions_Ftriv (a b : Fin 4) (w : Multiset (Fin 4) → ℝ) :
    ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ Ftriv),
      w (c ::ₘ ({a, b} : Multiset (Fin 4))) =
    ∑ c : Fin 4, if c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ Ftriv then w (c ::ₘ {a, b}) else 0 := by
  rw [sum_filter]

/-- **No balanced type weights for `Ftriv`.** The balance equations at `00, 01, 02` give
`w₀₀₀ = 2 w₀₁₂ - 4`, and those at `12, 13, 23, 33` give `w₃₃₃ = 4 - 2 w₀₁₂`; both cannot be
positive. Hence `teoremaB_balanced` does not apply to `Ftriv`. -/
theorem not_balancedWeights_Ftriv (w : Multiset (Fin 4) → ℝ) :
    ¬ BlowupB.BalancedWeights Ftriv w := by
  rintro ⟨hpos, hsum⟩
  have hA : ∀ a b : Fin 4, (∃ k, Link Ftriv a b k) → PaddedInputs.AllowedPair Ftriv a b :=
    fun a b h => (PaddedInputs.allowedPair_iff_link Ftriv a b).mpr h
  have h00 := hsum 0 0 (hA 0 0 ⟨0, by unfold Link Ftriv; decide⟩)
  have h01 := hsum 0 1 (hA 0 1 ⟨0, by unfold Link Ftriv; decide⟩)
  have h02 := hsum 0 2 (hA 0 2 ⟨0, by unfold Link Ftriv; decide⟩)
  have h12 := hsum 1 2 (hA 1 2 ⟨0, by unfold Link Ftriv; decide⟩)
  have h13 := hsum 1 3 (hA 1 3 ⟨2, by unfold Link Ftriv; decide⟩)
  have h23 := hsum 2 3 (hA 2 3 ⟨1, by unfold Link Ftriv; decide⟩)
  have h33 := hsum 3 3 (hA 3 3 ⟨1, by unfold Link Ftriv; decide⟩)
  simp only [sum_completions_Ftriv, Fin.sum_univ_four] at h00 h01 h02 h12 h13 h23 h33
  simp (config := {decide := true}) only at h00 h01 h02 h12 h13 h23 h33
  have p000 := hpos {0, 0, 0} (by unfold Ftriv; decide)
  have p333 := hpos {3, 3, 3} (by unfold Ftriv; decide)
  simp only [ite_true, ite_false, add_zero, zero_add] at h00 h01 h02 h12 h13 h23 h33
  have e1 : ((1 : Fin 4) ::ₘ ({0, 0} : Multiset (Fin 4))) = {0, 0, 1} := by decide
  have e2 : ((2 : Fin 4) ::ₘ ({0, 0} : Multiset (Fin 4))) = {0, 0, 2} := by decide
  have e3 : ((0 : Fin 4) ::ₘ ({0, 1} : Multiset (Fin 4))) = {0, 0, 1} := by decide
  have e4 : ((2 : Fin 4) ::ₘ ({0, 1} : Multiset (Fin 4))) = {0, 1, 2} := by decide
  have e5 : ((0 : Fin 4) ::ₘ ({0, 2} : Multiset (Fin 4))) = {0, 0, 2} := by decide
  have e6 : ((1 : Fin 4) ::ₘ ({0, 2} : Multiset (Fin 4))) = {0, 1, 2} := by decide
  have e7 : ((0 : Fin 4) ::ₘ ({1, 2} : Multiset (Fin 4))) = {0, 1, 2} := by decide
  have e8 : ((3 : Fin 4) ::ₘ ({1, 2} : Multiset (Fin 4))) = {1, 2, 3} := by decide
  have e9 : ((2 : Fin 4) ::ₘ ({1, 3} : Multiset (Fin 4))) = {1, 2, 3} := by decide
  have e10 : ((3 : Fin 4) ::ₘ ({1, 3} : Multiset (Fin 4))) = {1, 3, 3} := by decide
  have e11 : ((1 : Fin 4) ::ₘ ({2, 3} : Multiset (Fin 4))) = {1, 2, 3} := by decide
  have e12 : ((3 : Fin 4) ::ₘ ({2, 3} : Multiset (Fin 4))) = {2, 3, 3} := by decide
  have e13 : ((1 : Fin 4) ::ₘ ({3, 3} : Multiset (Fin 4))) = {1, 3, 3} := by decide
  have e14 : ((2 : Fin 4) ::ₘ ({3, 3} : Multiset (Fin 4))) = {2, 3, 3} := by decide
  have e15 : ((0 : Fin 4) ::ₘ ({0, 0} : Multiset (Fin 4))) = {0, 0, 0} := by decide
  have e16 : ((3 : Fin 4) ::ₘ ({3, 3} : Multiset (Fin 4))) = {3, 3, 3} := by decide
  rw [e15, e1, e2] at h00
  rw [e3, e4] at h01
  rw [e5, e6] at h02
  rw [e7, e8] at h12
  rw [e9, e10] at h13
  rw [e11, e12] at h23
  rw [e13, e14, e16] at h33
  norm_num at h00 h01 h02 h12 h13 h23 h33 p000 p333
  linarith

#print axioms familyFacts_Ftriv
#print axioms not_balancedWeights_Ftriv

end PaddedTrivial
