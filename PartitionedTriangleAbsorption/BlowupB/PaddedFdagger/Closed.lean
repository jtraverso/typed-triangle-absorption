/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFdagger.Inverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Covered

@[expose] public section

/-!
# The padded Keevash statement and Theorem B for F†

`Fdag = {000, 001, 002, 012, 123, 133, 233}` (F* without 333) is the first bit-only family of the
census (quotient `ℤ/2`) to be closed. Its universal certificate goes through the ordinary refiner
and ONE torsion layer (`universal_simple_Fdag`); the inverse is explicit
(`completeInverseCert_Fdag`). `PaddedGeneral.keevashPaddedSpec_of_certs` then gives
`KeevashPaddedSpec Fdag`. Theorem B is stated in the weighted form (`teoremaB_of_keevash`).

`CoveredFamily₂` extends Aristotle's decidable `PaddedTrivial.CoveredFamily` (relabellings of
F₁, F₂, F₃, F*) by the relabellings of F†.
-/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedFdagger

theorem familyFacts_Fdag : PaddedGeneral.FamilyFacts Fdag :=
  ⟨Fdag_card, by unfold Link Fdag; decide, by intro i; fin_cases i <;> (unfold Link Fdag; decide)⟩

theorem universalCert_Fdag : PaddedGeneral.UniversalCert Fdag :=
  fun V _ _ p G _ ω hG hs hω hω1 hn => universal_simple_Fdag p G ω hG hs hω hω1 hn

/-- **`KeevashPaddedSpec` for F†**, unconditional. -/
theorem keevashPaddedSpec_Fdag : KeevashPaddedSpec Fdag := by
  change PaddedInputs.KeevashPaddedSpec Fdag
  exact PaddedGeneral.keevashPaddedSpec_of_certs Fdag familyFacts_Fdag universalCert_Fdag
    completeInverseCert_Fdag

theorem keevashTypedSpec_Fdag : KeevashTypedSpec Fdag :=
  keevashTypedSpec_of_padded Fdag_card keevashPaddedSpec_Fdag

theorem keevashPaddedSpec_perm_Fdag (σ : Equiv.Perm (Fin 4)) :
    KeevashPaddedSpec (permFam σ Fdag) :=
  keevashPaddedSpec_perm σ keevashPaddedSpec_Fdag

/-- **Theorem B for F†** (weighted form), unconditional. -/
theorem teoremaB_Fdag (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair Fdag (p u) (p v)) → (∀ v, missDeg p Fdag G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ Fdag, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair Fdag a b →
            |(∑ τ ∈ Fdag, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p Fdag G.edgeFinset → HasDecomp p Fdag G.edgeFinset :=
  teoremaB_of_keevash keevashTypedSpec_Fdag γ ω₁ hγ hω₁

/-- The covered class extended by the relabellings of F†. -/
def CoveredFamily₂ (F : Finset (Multiset (Fin 4))) : Prop :=
  PaddedTrivial.CoveredFamily F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ Fdag

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₂ F) := by
  unfold CoveredFamily₂; infer_instance

theorem keevashPaddedSpec_of_covered₂ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₂ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact PaddedTrivial.keevashPaddedSpec_of_covered F hF
  · exact keevashPaddedSpec_perm_Fdag σ

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_Fdag
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_Fdag
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₂
