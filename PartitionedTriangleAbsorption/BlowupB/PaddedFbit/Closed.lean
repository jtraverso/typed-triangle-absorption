/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Supersets
public import PartitionedTriangleAbsorption.BlowupB.PaddedFdagger.Closed

@[expose] public section

/-!
# The census class with three-step links and common neighbour classes, closed

The local census (765 `S₄`-classes of four-class families with a forbidden pair at every class)
has exactly ten classes with `ThreeStepLinks` and common neighbour classes (Python, not Lean):

| family | quotient `Λ_ord / L_F` | Lean |
|---|---|---|
| F₃ | ℤ² | `PaddedF3.keevashPaddedSpec_F3` |
| F₁, F₂ | ℤ ⊕ ℤ/2 | `PaddedF12.keevashPaddedSpec_F1/F2` |
| F* (= Aristotle's Ftriv) | 0 | `keevashPaddedSpec_Fstar`, `PaddedTrivial.keevashPaddedSpec_Ftriv` |
| F† | ℤ/2 | `keevashPaddedSpec_Fdag` |
| Fbit, Fbit+333, Fbit+111, Fbit+111+222, Fbit+111+222+333 | ℤ/2 | `PaddedFbit.keevashPaddedSpec_*` |

`CoveredFamily₃` is the decidable predicate "a relabelling of one of these ten", and
`keevashPaddedSpec_of_covered₃` proves the padded Keevash statement for all of them.
-/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedFbit

/-- Relabellings of the ten base families. -/
def CoveredFamily₃ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₂ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ Fbit ∨ F = permFam σ Fbit333 ∨
    F = permFam σ Fbit111 ∨ F = permFam σ Fbit111222 ∨ F = permFam σ FbitMono

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₃ F) := by
  unfold CoveredFamily₃; infer_instance

theorem keevashPaddedSpec_of_covered₃ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₃ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_covered₂ F hF
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_Fbit
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_Fbit333
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_Fbit111
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_Fbit111222
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_FbitMono

/-- **Theorem B** (weighted form) for every covered family. -/
theorem teoremaB_covered₃ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₃ F)
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
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₃ F hF))
    γ ω₁ hγ hω₁

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₃
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₃
