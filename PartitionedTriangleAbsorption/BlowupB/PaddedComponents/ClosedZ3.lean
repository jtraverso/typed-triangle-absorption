/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.InverseFB2
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.InverseFB3
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ClosedB1

@[expose] public section

/-!
# The six disconnected `ℤ/3` families without an isolated monochromatic class

For `F ∈ {FB1, …, FB6}` (and every relabelling): `UniversalCert F` (componentwise refiner),
`CompleteInverseCert F` (`FB4` from `FB2`, `FB5` and `FB6` from `FB3`, by
`completeInverseCert_of_ternary`: same allowed pairs, more types), hence
`KeevashPaddedSpec F`. `CoveredFamily₇` adds the six families to `CoveredFamily₅`.

The other 39 `ℤ/3` rows of the census have an isolated monochromatic class; for them
`CompleteInverseCert` is false (`not_completeInverseCert_of_isolatedMono`).
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption PaddedGeneral PaddedNoCommon
open PartitionedTriangleAbsorption.TypedTransformer

theorem completeInverseCert_FB2 : CompleteInverseCert FB2 :=
  completeInverseCert_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse_FB2

theorem completeInverseCert_FB3 : CompleteInverseCert FB3 :=
  completeInverseCert_of_ternary (Finset.Subset.refl _) (fun _ _ => Iff.rfl) ternaryInverse_FB3

theorem completeInverseCert_FB4 : CompleteInverseCert FB4 :=
  completeInverseCert_of_ternary (by unfold FB2 FB4; decide)
    (by unfold Link FB2 FB4; decide) ternaryInverse_FB2

theorem completeInverseCert_FB5 : CompleteInverseCert FB5 :=
  completeInverseCert_of_ternary (by unfold FB3 FB5; decide)
    (by unfold Link FB3 FB5; decide) ternaryInverse_FB3

theorem completeInverseCert_FB6 : CompleteInverseCert FB6 :=
  completeInverseCert_of_ternary (by unfold FB3 FB6; decide)
    (by unfold Link FB3 FB6; decide) ternaryInverse_FB3

theorem keevashPaddedSpec_FB2 : PaddedInputs.KeevashPaddedSpec FB2 :=
  keevashPaddedSpec_of_certs FB2 familyFacts_FB2 universalCert_FB2 completeInverseCert_FB2

theorem keevashPaddedSpec_FB3 : PaddedInputs.KeevashPaddedSpec FB3 :=
  keevashPaddedSpec_of_certs FB3 familyFacts_FB3 universalCert_FB3 completeInverseCert_FB3

theorem keevashPaddedSpec_FB4 : PaddedInputs.KeevashPaddedSpec FB4 :=
  keevashPaddedSpec_of_certs FB4 familyFacts_FB4 universalCert_FB4 completeInverseCert_FB4

theorem keevashPaddedSpec_FB5 : PaddedInputs.KeevashPaddedSpec FB5 :=
  keevashPaddedSpec_of_certs FB5 familyFacts_FB5 universalCert_FB5 completeInverseCert_FB5

theorem keevashPaddedSpec_FB6 : PaddedInputs.KeevashPaddedSpec FB6 :=
  keevashPaddedSpec_of_certs FB6 familyFacts_FB6 universalCert_FB6 completeInverseCert_FB6

/-- The six disconnected `ℤ/3` families without an isolated monochromatic class, up to
relabelling. -/
def CoveredZ3 (F : Finset (Multiset (Fin 4))) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), F = BlowupB.permFam σ FB1 ∨ F = BlowupB.permFam σ FB2 ∨
    F = BlowupB.permFam σ FB3 ∨ F = BlowupB.permFam σ FB4 ∨ F = BlowupB.permFam σ FB5 ∨
    F = BlowupB.permFam σ FB6

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredZ3 F) := by
  unfold CoveredZ3; infer_instance

/-- **The padded Keevash statement for every family in `CoveredZ3`.** -/
theorem keevashPaddedSpec_of_coveredZ3 (F : Finset (Multiset (Fin 4))) (hF : CoveredZ3 F) :
    PaddedInputs.KeevashPaddedSpec F := by
  obtain ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl⟩ := hF
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB1
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB2
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB3
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB4
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB5
  · exact BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_FB6

theorem card_three_of_coveredZ3 (F : Finset (Multiset (Fin 4))) (hF : CoveredZ3 F) :
    ∀ τ ∈ F, Multiset.card τ = 3 := by
  obtain ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl⟩ := hF
  · exact BlowupB.card_three_perm (σ := σ) FB1_card
  · exact BlowupB.card_three_perm (σ := σ) FB2_card
  · exact BlowupB.card_three_perm (σ := σ) FB3_card
  · exact BlowupB.card_three_perm (σ := σ) FB4_card
  · exact BlowupB.card_three_perm (σ := σ) FB5_card
  · exact BlowupB.card_three_perm (σ := σ) FB6_card

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedComponents

/-- `CoveredFamily₅` plus the six disconnected `ℤ/3` families of `CoveredZ3`. -/
def CoveredFamily₇ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₅ F ∨ CoveredZ3 F

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₇ F) := by
  unfold CoveredFamily₇; infer_instance

theorem keevashPaddedSpec_of_covered₇ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₇ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | hF
  · exact keevashPaddedSpec_of_covered₅ F hF
  · exact keevashPaddedSpec_of_coveredZ3 F hF

/-- The proved fragment of `TeoremaBTarget.TargetFour`, extended by the six `ℤ/3` families. -/
theorem targetFour_on_covered₇ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₇ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₇ F hF

/-- **Theorem B** (weighted form) for every family in `CoveredFamily₇`. -/
theorem teoremaB_covered₇ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₇ F)
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
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₇ F hF))
    γ ω₁ hγ hω₁

/-- **Theorem B** (weighted form) for every family in `CoveredZ3`, with no card hypothesis. -/
theorem teoremaB_coveredZ3 (F : Finset (Multiset (Fin 4))) (hF : CoveredZ3 F)
    (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
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
  teoremaB_covered₇ F (Or.inr hF) (card_three_of_coveredZ3 F hF) γ ω₁ hγ hω₁

example : CoveredFamily₇ FB4 := by decide
example : ¬ CoveredFamily₅ FB6 := by decide

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.completeInverseCert_FB2
#print axioms PaddedComponents.completeInverseCert_FB3
#print axioms PaddedComponents.completeInverseCert_FB4
#print axioms PaddedComponents.completeInverseCert_FB5
#print axioms PaddedComponents.completeInverseCert_FB6
#print axioms PaddedComponents.keevashPaddedSpec_of_coveredZ3
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₇
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_covered₇
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₇
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_coveredZ3
