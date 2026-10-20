/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.InverseFB1
public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.Closed

@[expose] public section

/-!
# A disconnected family closed: `KeevashPaddedSpec FB1` and all its relabellings

`FB1 = {000, 001, 222, 223}` (census row `Y | N | 2 | N | Z/3 | 4`), two components `{0,1}` and
`{2,3}`:

* `UniversalCert FB1` (`universalCert_FB1`): the componentwise refiner
  (`universalCert_of_even3_components`), with the component lattices `Even3` and the witness
  bound `B = 1360`; terminal order `36·168 + 105·1360 + 4 = 148852 ≤ 2^21`;
* `CompleteInverseCert FB1` (`completeInverseCert_FB1`), with the monochromatic vertex mode;
* `KeevashPaddedSpec FB1` by `keevashPaddedSpec_of_certs`, and every relabelling.

`FB1` has no balanced type weights (`not_balancedWeights_FB1`), so Theorem B is stated in the
weighted form. `CoveredFamily₆` adds all relabellings of `FB1` to `CoveredFamily₅`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption PaddedGeneral
open PartitionedTriangleAbsorption.TypedTransformer

/-- **Both certificates for `FB1`.** -/
theorem certs_FB1 : UniversalCert FB1 ∧ CompleteInverseCert FB1 :=
  ⟨universalCert_FB1, completeInverseCert_FB1⟩

/-- **The padded Keevash statement for `FB1`.** -/
theorem keevashPaddedSpec_FB1 : PaddedInputs.KeevashPaddedSpec FB1 :=
  keevashPaddedSpec_of_certs FB1 familyFacts_FB1 universalCert_FB1 completeInverseCert_FB1

/-- **The padded Keevash statement for every relabelling of `FB1`.** -/
theorem keevashPaddedSpec_perm_FB1 (σ : Equiv.Perm (Fin 4)) :
    PaddedInputs.KeevashPaddedSpec (BlowupB.permFam σ FB1) :=
  BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB1

theorem sum_completions_FB1 (a b : Fin 4) (w : Multiset (Fin 4) → ℝ) :
    ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ FB1),
      w (c ::ₘ ({a, b} : Multiset (Fin 4))) =
    ∑ c : Fin 4, if c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ FB1 then w (c ::ₘ {a, b}) else 0 := by
  rw [sum_filter]

/-- **No balanced type weights for `FB1`.** The balance equation at `01` gives `w₀₀₁ = 4`, and
the one at `00` gives `w₀₀₀ + w₀₀₁ = 4`, so `w₀₀₀ = 0`. -/
theorem not_balancedWeights_FB1 (w : Multiset (Fin 4) → ℝ) :
    ¬ BlowupB.BalancedWeights FB1 w := by
  rintro ⟨hpos, hsum⟩
  have hA : ∀ a b : Fin 4, (∃ k, Link FB1 a b k) → PaddedInputs.AllowedPair FB1 a b :=
    fun a b h => (PaddedInputs.allowedPair_iff_link FB1 a b).mpr h
  have h00 := hsum 0 0 (hA 0 0 ⟨0, by unfold Link FB1; decide⟩)
  have h01 := hsum 0 1 (hA 0 1 ⟨0, by unfold Link FB1; decide⟩)
  simp only [sum_completions_FB1, Fin.sum_univ_four] at h00 h01
  simp (config := {decide := true}) only at h00 h01
  have p000 := hpos {0, 0, 0} (by unfold FB1; decide)
  simp only [ite_true, ite_false, add_zero] at h00 h01
  have e1 : ((0 : Fin 4) ::ₘ ({0, 0} : Multiset (Fin 4))) = {0, 0, 0} := by decide
  have e2 : ((1 : Fin 4) ::ₘ ({0, 0} : Multiset (Fin 4))) = {0, 0, 1} := by decide
  have e3 : ((0 : Fin 4) ::ₘ ({0, 1} : Multiset (Fin 4))) = {0, 0, 1} := by decide
  rw [e1, e2] at h00
  rw [e3] at h01
  norm_num at h00 h01 p000
  linarith

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedComponents

/-- `CoveredFamily₅` plus all relabellings of the disconnected family `FB1`. -/
def CoveredFamily₆ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₅ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ FB1

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₆ F) := by
  unfold CoveredFamily₆; infer_instance

theorem keevashPaddedSpec_of_covered₆ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₆ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_covered₅ F hF
  · exact keevashPaddedSpec_perm_FB1 σ

/-- The proved fragment of `TeoremaBTarget.TargetFour`, extended by `FB1`. -/
theorem targetFour_on_covered₆ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₆ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₆ F hF

/-- **Theorem B** (weighted form) for every family in `CoveredFamily₆`. -/
theorem teoremaB_covered₆ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₆ F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ F, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair F a b →
            |(∑ τ ∈ F, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset :=
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₆ F hF))
    γ ω₁ hγ hω₁

/-- **Theorem B for `FB1`** (weighted form), for every relabelling. -/
theorem teoremaB_perm_FB1 (σ : Equiv.Perm (Fin 4)) (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair (permFam σ FB1) (p u) (p v)) →
        (∀ v, missDeg p (permFam σ FB1) G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ permFam σ FB1, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair (permFam σ FB1) a b →
            |(∑ τ ∈ permFam σ FB1, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p (permFam σ FB1) G.edgeFinset → HasDecomp p (permFam σ FB1) G.edgeFinset :=
  teoremaB_covered₆ (permFam σ FB1) (Or.inr ⟨σ, rfl⟩)
    (card_three_perm (σ := σ) FB1_card) γ ω₁ hγ hω₁

/-- Sanity: `FB1` is covered (decidably), and it was not covered before. -/
example : CoveredFamily₆ FB1 := by decide
example : ¬ CoveredFamily₅ FB1 := by decide

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.universalCert_FB1
#print axioms PaddedComponents.completeInverseCert_FB1
#print axioms PaddedComponents.certs_FB1
#print axioms PaddedComponents.keevashPaddedSpec_FB1
#print axioms PaddedComponents.keevashPaddedSpec_perm_FB1
#print axioms PaddedComponents.not_balancedWeights_FB1
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₆
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_covered₆
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₆
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_perm_FB1
