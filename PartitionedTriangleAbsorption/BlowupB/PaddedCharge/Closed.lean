/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.Cert
public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.InverseFnoC
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Closed

@[expose] public section

/-!
# Target A closed: `KeevashPaddedSpec FnoC` and all its relabellings

`FnoC = {001, 002, 011, 022, 113, 133}` (the census row `Y | N | 1 | Y | charges`):

* `UniversalCert FnoC` (`universalCert_FnoC`, `PaddedCharge/Cert.lean`): virtual refiner in `⊤`,
  paths of length four, then a physical charge-token layer (`token_layer` with tokens from
  `host_charge_tokens`), terminal absorbers for pieces of `≤ 504` edges;
* `CompleteInverseCert FnoC` (`completeInverseCert_FnoC`, `PaddedCharge/InverseFnoC.lean`), using
  the span compatibility `SpanCompat`;
* `KeevashPaddedSpec FnoC` by `keevashPaddedSpec_of_certs`, and every relabelling by
  `keevashPaddedSpec_perm`.

`FnoC` has no balanced type weights (`not_balancedWeights_FnoC`: the equations at `02` and `22`
force `w₀₀₂ = 0`), so Theorem B is stated in the weighted form of `teoremaB_of_keevash`.

`CoveredFamily₅` adds all relabellings of `FnoC` to `CoveredFamily₄`.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption PaddedGeneral PaddedNoCommon
open PartitionedTriangleAbsorption.TypedTransformer

theorem familyFacts_FnoC : FamilyFacts FnoC := baseFacts_FnoC.facts

/-- **Target A: both certificates for `FnoC`.** -/
theorem certs_FnoC : UniversalCert FnoC ∧ CompleteInverseCert FnoC :=
  ⟨universalCert_FnoC, completeInverseCert_FnoC⟩

/-- **Target A: the padded Keevash statement for `FnoC`.** -/
theorem keevashPaddedSpec_FnoC : PaddedInputs.KeevashPaddedSpec FnoC :=
  keevashPaddedSpec_of_certs FnoC familyFacts_FnoC universalCert_FnoC completeInverseCert_FnoC

/-- **Target A for every relabelling of `FnoC`.** -/
theorem keevashPaddedSpec_perm_FnoC (σ : Equiv.Perm (Fin 4)) :
    PaddedInputs.KeevashPaddedSpec (BlowupB.permFam σ FnoC) :=
  BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FnoC

theorem sum_completions_FnoC (a b : Fin 4) (w : Multiset (Fin 4) → ℝ) :
    ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ FnoC),
      w (c ::ₘ ({a, b} : Multiset (Fin 4))) =
    ∑ c : Fin 4, if c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ FnoC then w (c ::ₘ {a, b}) else 0 := by
  rw [sum_filter]

/-- **No balanced type weights for `FnoC`.** The balance equation at `22` gives `w₀₂₂ = 4`, and the
one at `02` gives `w₀₀₂ + w₀₂₂ = 4`, so `w₀₀₂ = 0`. Hence `teoremaB_balanced` does not apply. -/
theorem not_balancedWeights_FnoC (w : Multiset (Fin 4) → ℝ) :
    ¬ BlowupB.BalancedWeights FnoC w := by
  rintro ⟨hpos, hsum⟩
  have hA : ∀ a b : Fin 4, (∃ k, Link FnoC a b k) → PaddedInputs.AllowedPair FnoC a b :=
    fun a b h => (PaddedInputs.allowedPair_iff_link FnoC a b).mpr h
  have h02 := hsum 0 2 (hA 0 2 ⟨0, by unfold Link FnoC; decide⟩)
  have h22 := hsum 2 2 (hA 2 2 ⟨0, by unfold Link FnoC; decide⟩)
  simp only [sum_completions_FnoC, Fin.sum_univ_four] at h02 h22
  simp (config := {decide := true}) only at h02 h22
  have p002 := hpos {0, 0, 2} (by unfold FnoC; decide)
  simp only [ite_true, ite_false, add_zero, zero_add] at h02 h22
  have e5 : ((0 : Fin 4) ::ₘ ({0, 2} : Multiset (Fin 4))) = {0, 0, 2} := by decide
  have e6 : ((2 : Fin 4) ::ₘ ({0, 2} : Multiset (Fin 4))) = {0, 2, 2} := by decide
  have e7 : ((0 : Fin 4) ::ₘ ({2, 2} : Multiset (Fin 4))) = {0, 2, 2} := by decide
  rw [e5, e6] at h02
  rw [e7] at h22
  norm_num at h02 h22 p002
  linarith

end PaddedCharge

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedCharge

/-- `CoveredFamily₄` plus all relabellings of `FnoC` (target A). -/
def CoveredFamily₅ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₄ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ FnoC

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₅ F) := by
  unfold CoveredFamily₅; infer_instance

theorem keevashPaddedSpec_of_covered₅ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₅ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_covered₄ F hF
  · exact keevashPaddedSpec_perm_FnoC σ

/-- The proved fragment of `TeoremaBTarget.TargetFour`, extended by target A. -/
theorem targetFour_on_covered₅ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₅ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₅ F hF

/-- **Theorem B** (weighted form) for every family in `CoveredFamily₅`. -/
theorem teoremaB_covered₅ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₅ F)
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
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₅ F hF))
    γ ω₁ hγ hω₁

/-- **Theorem B for target A** (weighted form), for every relabelling of `FnoC`. -/
theorem teoremaB_perm_FnoC (σ : Equiv.Perm (Fin 4)) (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair (permFam σ FnoC) (p u) (p v)) →
        (∀ v, missDeg p (permFam σ FnoC) G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ permFam σ FnoC, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair (permFam σ FnoC) a b →
            |(∑ τ ∈ permFam σ FnoC, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p (permFam σ FnoC) G.edgeFinset → HasDecomp p (permFam σ FnoC) G.edgeFinset :=
  teoremaB_covered₅ (permFam σ FnoC) (Or.inr ⟨σ, rfl⟩)
    (card_three_perm (σ := σ) baseFacts_FnoC.card) γ ω₁ hγ hω₁

/-- Sanity: `FnoC` is covered (decidably), and it was not covered before. -/
example : CoveredFamily₅ FnoC := by decide
example : ¬ CoveredFamily₄ FnoC := by decide

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedCharge.universalCert_FnoC
#print axioms PaddedCharge.completeInverseCert_FnoC
#print axioms PaddedCharge.certs_FnoC
#print axioms PaddedCharge.keevashPaddedSpec_FnoC
#print axioms PaddedCharge.keevashPaddedSpec_perm_FnoC
#print axioms PaddedCharge.not_balancedWeights_FnoC
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₅
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_covered₅
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₅
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_perm_FnoC
