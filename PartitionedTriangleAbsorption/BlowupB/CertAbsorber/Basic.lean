/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import PartitionedTriangleAbsorption.PairMoveSelectionStage85

/-! # Certificate absorbers: generic tools

* `isDecomp_of_slots`: a decomposition read off from "slots".  Every edge of the target
  carries a name (a slot), the naming map is injective, and each triangle consumes three
  slots; disjointness of the slot triples gives physical edge-disjointness.
* `exists_fiber_matching`: a fibrewise injection between two finite families when every
  fibre of the first is not larger than the corresponding fibre of the second.  This is the
  "assignment of occurrences" of the certificate (copies, not combined coefficients).
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption

variable {t : ℕ}

/-- **Decomposition from slots.** -/
theorem isDecomp_of_slots {V : Type*} [DecidableEq V] {ι σ : Type*} [DecidableEq σ]
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : Finset ι) (tri : ι → Finset V)
    (sl : ι → Finset σ) (ed : σ → Sym2 V) (hed : Function.Injective ed)
    (htyped : ∀ j ∈ J, IsTypedTri p F (tri j))
    (hedges : ∀ j ∈ J, triEdges (tri j) = (sl j).image ed)
    (hdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (sl j) (sl j')) :
    IsDecomp p F ((J.biUnion sl).image ed) (J.image tri) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hs
    exact htyped j hj
  · intro s hs s' hs' hne
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hs
    obtain ⟨j', hj', rfl⟩ := mem_image.mp hs'
    have hjj : j ≠ j' := fun h => hne (h ▸ rfl)
    change Disjoint (triEdges (tri j)) (triEdges (tri j'))
    rw [hedges j hj, hedges j' hj']
    exact (Finset.disjoint_image hed).mpr (hdisj j hj j' hj' hjj)
  · rw [biUnion_image, image_biUnion]
    exact biUnion_congr rfl (fun j hj => hedges j hj)

/-- Transport of a dependent embedding along an equality of fibres. -/
private lemma emb_val_congr {α β γ : Type*} (f : α → γ) (g : β → γ)
    (e : ∀ c, {a // f a = c} ↪ {b // g b = c}) {c c' : γ} (hc : c = c') (x : α)
    (hx : f x = c) (hx' : f x = c') : (e c ⟨x, hx⟩).1 = (e c' ⟨x, hx'⟩).1 := by
  subst hc; rfl

/-- **Fibrewise matching.** -/
theorem exists_fiber_matching {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ)
    (h : ∀ c, Fintype.card {a // f a = c} ≤ Fintype.card {b // g b = c}) :
    ∃ μ : α → β, Function.Injective μ ∧ ∀ a, g (μ a) = f a := by
  classical
  have e : ∀ c, {a // f a = c} ↪ {b // g b = c} := fun c =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (h c))
  refine ⟨fun a => (e (f a) ⟨a, rfl⟩).1, ?_, fun a => (e (f a) ⟨a, rfl⟩).2⟩
  intro a a' haa
  have hf : f a = f a' := by
    have h1 := (e (f a) ⟨a, rfl⟩).2
    have h2 := (e (f a') ⟨a', rfl⟩).2
    simp only at haa
    rw [← h1, ← h2, haa]
  have h3 : (e (f a) ⟨a', hf.symm⟩).1 = (e (f a') ⟨a', rfl⟩).1 :=
    emb_val_congr f g e hf a' hf.symm rfl
  have h4 : e (f a) ⟨a, rfl⟩ = e (f a) ⟨a', hf.symm⟩ := Subtype.ext (haa.trans h3.symm)
  exact congrArg Subtype.val ((e (f a)).injective h4)

end PaperII.CertAbsorber
