/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights

@[expose] public section

/-! Identify exactly which catalogue arcs are replaced. Input arcs absent
from the catalogue cannot occur in a residual partition using that catalogue. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReserveSupport

open Finset

variable {A : Type} [DecidableEq A]

theorem reserve_eq (lib : Finset (Finset (A × A))) (R I : Finset (A × A))
    (hsupport : ∀ P ∈ lib, P ⊆ R ∪ I)
    (hcover : R ⊆ CatalogueWeights.arcs lib) (hdis : Disjoint R I) :
    CatalogueWeights.arcs lib \ ((CatalogueWeights.arcs lib).filter (fun e => e ∈ I)) = R := by
  ext e
  constructor
  · intro he
    obtain ⟨hea, hen⟩ := mem_sdiff.mp he
    have hei : e ∉ I := fun hi => hen (mem_filter.mpr ⟨hea, hi⟩)
    obtain ⟨P, hP, heP⟩ := mem_biUnion.mp hea
    exact (mem_union.mp (hsupport P hP heP)).resolve_right hei
  · intro he
    refine mem_sdiff.mpr ⟨hcover he, ?_⟩
    intro hkeep
    exact disjoint_left.mp hdis he (mem_filter.mp hkeep).2

theorem input_subset (lib Q : Finset (Finset (A × A)))
    (R I S : Finset (A × A)) (hQ : Q ⊆ lib) (hS : S ⊆ I)
    (hpart : Q.biUnion id = R ∪ S) :
    S ⊆ (CatalogueWeights.arcs lib).filter (fun e => e ∈ I) := by
  intro e he
  have heQ : e ∈ Q.biUnion id := by rw [hpart]; exact mem_union_right _ he
  obtain ⟨P, hP, heP⟩ := mem_biUnion.mp heQ
  exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨P, hQ hP, heP⟩, hS he⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReserveSupport

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReserveSupport.reserve_eq
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReserveSupport.input_subset
