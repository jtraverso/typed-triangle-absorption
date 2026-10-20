/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnA
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnB
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnC
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnD
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnE
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFnF
public import PartitionedTriangleAbsorption.BlowupB.AristotleIntegration

@[expose] public section

/-!
# The fourteen connected trivial-lattice families without common neighbour classes, closed

For each census family `NCk` (`PaddedNoCommon/Families.lean`) with base `F0 ⊆ NCk` (same allowed
pairs):

* `UniversalCert NCk` from the walk-routed universal absorber of the base
  (`universalCert_of_overBase`, `PaddedNoCommon/UniversalFamilies.lean`), which only needs the
  class graph to have walks of length four between any two classes (`Walk4`), NOT common
  neighbour classes;
* `CompleteInverseCert NCk` from the ternary inverse of the base
  (`completeInverseCert_of_ternary`, `PaddedNoCommon/Inverse*.lean`);
* `KeevashPaddedSpec NCk` by `keevashPaddedSpec_of_certs`.

`CoveredFamily₄` adds all relabellings of the fourteen families to `CoveredFamily₃`.
-/

namespace PaddedNoCommon

open PartitionedTriangleAbsorption PaddedGeneral

/-- Both certificates for `NC1` (base `FnA`). -/
theorem certs_NC1 : UniversalCert NC1 ∧ CompleteInverseCert NC1 :=
  ⟨universalCert_of_overBase overBase_NC1 (lattice_FnA 168).1 universalCert_FnA,
    completeInverseCert_of_ternary overBase_NC1.sub overBase_NC1.allowed ternaryInverse_FnA⟩

theorem keevashPaddedSpec_NC1 : PaddedInputs.KeevashPaddedSpec NC1 :=
  keevashPaddedSpec_of_certs NC1 overBase_NC1.facts certs_NC1.1 certs_NC1.2

/-- Both certificates for `NC2` (base `FnB`). -/
theorem certs_NC2 : UniversalCert NC2 ∧ CompleteInverseCert NC2 :=
  ⟨universalCert_of_overBase overBase_NC2 (lattice_FnB 168).1 universalCert_FnB,
    completeInverseCert_of_ternary overBase_NC2.sub overBase_NC2.allowed ternaryInverse_FnB⟩

theorem keevashPaddedSpec_NC2 : PaddedInputs.KeevashPaddedSpec NC2 :=
  keevashPaddedSpec_of_certs NC2 overBase_NC2.facts certs_NC2.1 certs_NC2.2

/-- Both certificates for `NC3` (base `FnC`). -/
theorem certs_NC3 : UniversalCert NC3 ∧ CompleteInverseCert NC3 :=
  ⟨universalCert_of_overBase overBase_NC3 (lattice_FnC 168).1 universalCert_FnC,
    completeInverseCert_of_ternary overBase_NC3.sub overBase_NC3.allowed ternaryInverse_FnC⟩

theorem keevashPaddedSpec_NC3 : PaddedInputs.KeevashPaddedSpec NC3 :=
  keevashPaddedSpec_of_certs NC3 overBase_NC3.facts certs_NC3.1 certs_NC3.2

/-- Both certificates for `NC4` (base `FnD`). -/
theorem certs_NC4 : UniversalCert NC4 ∧ CompleteInverseCert NC4 :=
  ⟨universalCert_of_overBase overBase_NC4 (lattice_FnD 168).1 universalCert_FnD,
    completeInverseCert_of_ternary overBase_NC4.sub overBase_NC4.allowed ternaryInverse_FnD⟩

theorem keevashPaddedSpec_NC4 : PaddedInputs.KeevashPaddedSpec NC4 :=
  keevashPaddedSpec_of_certs NC4 overBase_NC4.facts certs_NC4.1 certs_NC4.2

/-- Both certificates for `NC5` (base `FnB`). -/
theorem certs_NC5 : UniversalCert NC5 ∧ CompleteInverseCert NC5 :=
  ⟨universalCert_of_overBase overBase_NC5 (lattice_FnB 168).1 universalCert_FnB,
    completeInverseCert_of_ternary overBase_NC5.sub overBase_NC5.allowed ternaryInverse_FnB⟩

theorem keevashPaddedSpec_NC5 : PaddedInputs.KeevashPaddedSpec NC5 :=
  keevashPaddedSpec_of_certs NC5 overBase_NC5.facts certs_NC5.1 certs_NC5.2

/-- Both certificates for `NC6` (base `FnE`). -/
theorem certs_NC6 : UniversalCert NC6 ∧ CompleteInverseCert NC6 :=
  ⟨universalCert_of_overBase overBase_NC6 (lattice_FnE 168).1 universalCert_FnE,
    completeInverseCert_of_ternary overBase_NC6.sub overBase_NC6.allowed ternaryInverse_FnE⟩

theorem keevashPaddedSpec_NC6 : PaddedInputs.KeevashPaddedSpec NC6 :=
  keevashPaddedSpec_of_certs NC6 overBase_NC6.facts certs_NC6.1 certs_NC6.2

/-- Both certificates for `NC7` (base `FnD`). -/
theorem certs_NC7 : UniversalCert NC7 ∧ CompleteInverseCert NC7 :=
  ⟨universalCert_of_overBase overBase_NC7 (lattice_FnD 168).1 universalCert_FnD,
    completeInverseCert_of_ternary overBase_NC7.sub overBase_NC7.allowed ternaryInverse_FnD⟩

theorem keevashPaddedSpec_NC7 : PaddedInputs.KeevashPaddedSpec NC7 :=
  keevashPaddedSpec_of_certs NC7 overBase_NC7.facts certs_NC7.1 certs_NC7.2

/-- Both certificates for `NC8` (base `FnD`). -/
theorem certs_NC8 : UniversalCert NC8 ∧ CompleteInverseCert NC8 :=
  ⟨universalCert_of_overBase overBase_NC8 (lattice_FnD 168).1 universalCert_FnD,
    completeInverseCert_of_ternary overBase_NC8.sub overBase_NC8.allowed ternaryInverse_FnD⟩

theorem keevashPaddedSpec_NC8 : PaddedInputs.KeevashPaddedSpec NC8 :=
  keevashPaddedSpec_of_certs NC8 overBase_NC8.facts certs_NC8.1 certs_NC8.2

/-- Both certificates for `NC9` (base `FnC`). -/
theorem certs_NC9 : UniversalCert NC9 ∧ CompleteInverseCert NC9 :=
  ⟨universalCert_of_overBase overBase_NC9 (lattice_FnC 168).1 universalCert_FnC,
    completeInverseCert_of_ternary overBase_NC9.sub overBase_NC9.allowed ternaryInverse_FnC⟩

theorem keevashPaddedSpec_NC9 : PaddedInputs.KeevashPaddedSpec NC9 :=
  keevashPaddedSpec_of_certs NC9 overBase_NC9.facts certs_NC9.1 certs_NC9.2

/-- Both certificates for `NC10` (base `FnF`). -/
theorem certs_NC10 : UniversalCert NC10 ∧ CompleteInverseCert NC10 :=
  ⟨universalCert_of_overBase overBase_NC10 (lattice_FnF 168).1 universalCert_FnF,
    completeInverseCert_of_ternary overBase_NC10.sub overBase_NC10.allowed ternaryInverse_FnF⟩

theorem keevashPaddedSpec_NC10 : PaddedInputs.KeevashPaddedSpec NC10 :=
  keevashPaddedSpec_of_certs NC10 overBase_NC10.facts certs_NC10.1 certs_NC10.2

/-- Both certificates for `NC11` (base `FnE`). -/
theorem certs_NC11 : UniversalCert NC11 ∧ CompleteInverseCert NC11 :=
  ⟨universalCert_of_overBase overBase_NC11 (lattice_FnE 168).1 universalCert_FnE,
    completeInverseCert_of_ternary overBase_NC11.sub overBase_NC11.allowed ternaryInverse_FnE⟩

theorem keevashPaddedSpec_NC11 : PaddedInputs.KeevashPaddedSpec NC11 :=
  keevashPaddedSpec_of_certs NC11 overBase_NC11.facts certs_NC11.1 certs_NC11.2

/-- Both certificates for `NC12` (base `FnD`). -/
theorem certs_NC12 : UniversalCert NC12 ∧ CompleteInverseCert NC12 :=
  ⟨universalCert_of_overBase overBase_NC12 (lattice_FnD 168).1 universalCert_FnD,
    completeInverseCert_of_ternary overBase_NC12.sub overBase_NC12.allowed ternaryInverse_FnD⟩

theorem keevashPaddedSpec_NC12 : PaddedInputs.KeevashPaddedSpec NC12 :=
  keevashPaddedSpec_of_certs NC12 overBase_NC12.facts certs_NC12.1 certs_NC12.2

/-- Both certificates for `NC13` (base `FnF`). -/
theorem certs_NC13 : UniversalCert NC13 ∧ CompleteInverseCert NC13 :=
  ⟨universalCert_of_overBase overBase_NC13 (lattice_FnF 168).1 universalCert_FnF,
    completeInverseCert_of_ternary overBase_NC13.sub overBase_NC13.allowed ternaryInverse_FnF⟩

theorem keevashPaddedSpec_NC13 : PaddedInputs.KeevashPaddedSpec NC13 :=
  keevashPaddedSpec_of_certs NC13 overBase_NC13.facts certs_NC13.1 certs_NC13.2

/-- Both certificates for `NC14` (base `FnD`). -/
theorem certs_NC14 : UniversalCert NC14 ∧ CompleteInverseCert NC14 :=
  ⟨universalCert_of_overBase overBase_NC14 (lattice_FnD 168).1 universalCert_FnD,
    completeInverseCert_of_ternary overBase_NC14.sub overBase_NC14.allowed ternaryInverse_FnD⟩

theorem keevashPaddedSpec_NC14 : PaddedInputs.KeevashPaddedSpec NC14 :=
  keevashPaddedSpec_of_certs NC14 overBase_NC14.facts certs_NC14.1 certs_NC14.2

end PaddedNoCommon

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedNoCommon

/-- Relabellings of the 24 base families: `CoveredFamily₃` plus the fourteen census families
`NC1`, …, `NC14` (connected class graph, trivial lattice, no common neighbour classes). -/
def CoveredFamily₄ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₃ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ NC1 ∨
    F = permFam σ NC2 ∨
    F = permFam σ NC3 ∨
    F = permFam σ NC4 ∨
    F = permFam σ NC5 ∨
    F = permFam σ NC6 ∨
    F = permFam σ NC7 ∨
    F = permFam σ NC8 ∨
    F = permFam σ NC9 ∨
    F = permFam σ NC10 ∨
    F = permFam σ NC11 ∨
    F = permFam σ NC12 ∨
    F = permFam σ NC13 ∨
    F = permFam σ NC14

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₄ F) := by
  unfold CoveredFamily₄; infer_instance

theorem keevashPaddedSpec_of_covered₄ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₄ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_covered₃ F hF

  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC1
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC2
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC3
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC4
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC5
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC6
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC7
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC8
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC9
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC10
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC11
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC12
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC13
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_NC14

/-- The proved fragment of `TeoremaBTarget.TargetFour`, extended by the fourteen families. -/
theorem targetFour_on_covered₄ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₄ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₄ F hF

/-- The proved fragment of `TeoremaBTarget.TargetFourCerts` on the fourteen representatives. -/
theorem targetFourCerts_on_noCommon :
    ∀ F ∈ ([NC1, NC2, NC3, NC4, NC5, NC6, NC7, NC8, NC9, NC10, NC11, NC12, NC13, NC14] :
      List (Finset (Multiset (Fin 4)))),
      PaddedGeneral.UniversalCert F ∧ PaddedGeneral.CompleteInverseCert F := by
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certs_NC1
  · exact certs_NC2
  · exact certs_NC3
  · exact certs_NC4
  · exact certs_NC5
  · exact certs_NC6
  · exact certs_NC7
  · exact certs_NC8
  · exact certs_NC9
  · exact certs_NC10
  · exact certs_NC11
  · exact certs_NC12
  · exact certs_NC13
  · exact certs_NC14

/-- **Theorem B** (weighted form) for every family in `CoveredFamily₄`. -/
theorem teoremaB_covered₄ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₄ F)
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
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₄ F hF))
    γ ω₁ hγ hω₁

/-- Sanity: the two census examples are covered (decidably). -/
example : CoveredFamily₄ NC1 := by decide
example : CoveredFamily₄ NC6 := by decide

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedNoCommon.keevashPaddedSpec_NC1
#print axioms PaddedNoCommon.keevashPaddedSpec_NC2
#print axioms PaddedNoCommon.keevashPaddedSpec_NC3
#print axioms PaddedNoCommon.keevashPaddedSpec_NC4
#print axioms PaddedNoCommon.keevashPaddedSpec_NC5
#print axioms PaddedNoCommon.keevashPaddedSpec_NC6
#print axioms PaddedNoCommon.keevashPaddedSpec_NC7
#print axioms PaddedNoCommon.keevashPaddedSpec_NC8
#print axioms PaddedNoCommon.keevashPaddedSpec_NC9
#print axioms PaddedNoCommon.keevashPaddedSpec_NC10
#print axioms PaddedNoCommon.keevashPaddedSpec_NC11
#print axioms PaddedNoCommon.keevashPaddedSpec_NC12
#print axioms PaddedNoCommon.keevashPaddedSpec_NC13
#print axioms PaddedNoCommon.keevashPaddedSpec_NC14
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₄
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_covered₄
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFourCerts_on_noCommon
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₄
