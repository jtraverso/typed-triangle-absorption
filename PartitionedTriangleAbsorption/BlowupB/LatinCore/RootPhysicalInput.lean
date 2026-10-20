/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueBudget

@[expose] public section

/-! Prescribed port anchors retain the original input arcs exactly, even
though different split ports may share their physical root. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalInput

open Finset Cycles

set_option synthInstance.maxSize 1024

variable {P E U V : Type} [DecidableEq P] [DecidableEq E]
  [DecidableEq U] [DecidableEq V]

omit [DecidableEq P] [DecidableEq E] [DecidableEq U] in
theorem image_lifted_input (S : Finset (P × P)) (root : P → V)
    (f : RootPaths.Vert P E ⊕ U → V)
    (hpin : ∀ p, f (Sum.inl (Sum.inl p)) = root p) :
    (((S.map (liftArc P (E × Fin 2))).map (liftArc (RootPaths.Vert P E) U)).image
      (arcImage f)) = S.image (arcImage root) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
    obtain ⟨e, he, rfl⟩ := mem_map.mp hb'
    refine mem_image.mpr ⟨e, he, ?_⟩
    change (root e.1, root e.2) =
      (f (Sum.inl (Sum.inl e.1)), f (Sum.inl (Sum.inl e.2)))
    rw [hpin, hpin]
  · intro ha
    obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    refine mem_image.mpr ⟨liftArc (RootPaths.Vert P E) U (liftArc P (E × Fin 2) e),
      mem_map.mpr ⟨liftArc P (E × Fin 2) e, mem_map.mpr ⟨e, he, rfl⟩, rfl⟩, ?_⟩
    change (f (Sum.inl (Sum.inl e.1)), f (Sum.inl (Sum.inl e.2))) = (root e.1, root e.2)
    rw [hpin, hpin]

omit [DecidableEq P] [DecidableEq E] [DecidableEq U] [DecidableEq V] in
theorem injective_lifted_input (S : Finset (P × P)) (root : P → V)
    (f : RootPaths.Vert P E ⊕ U → V)
    (hpin : ∀ p, f (Sum.inl (Sum.inl p)) = root p)
    (hroot : Set.InjOn (arcImage root) (S : Set (P × P))) :
    Set.InjOn (arcImage f)
      (((S.map (liftArc P (E × Fin 2))).map (liftArc (RootPaths.Vert P E) U)) :
        Set ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))) := by
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
  obtain ⟨e, he, rfl⟩ := mem_map.mp ha'
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hb'
  have heq : arcImage root e = arcImage root q := by
    change (f (Sum.inl (Sum.inl e.1)), f (Sum.inl (Sum.inl e.2))) =
      (f (Sum.inl (Sum.inl q.1)), f (Sum.inl (Sum.inl q.2))) at hab
    simpa only [arcImage, hpin] using hab
  have heq' := hroot he hq heq
  subst q
  rfl

theorem original_input_image [Fintype V] (X L : Finset (V × V)) (hL : L ⊆ X)
    (σ : RootChannels.Perms (SplitPorts.root X))
    (f : RootCatalogueBudget.Vert X σ ⊕ U → V)
    (hpin : ∀ p, f (Sum.inl (Sum.inl p)) = SplitPorts.root X p) :
    (((RootCatalogueBudget.input X L σ).map
      (liftArc (RootCatalogueBudget.Vert X σ) U)).image (arcImage f)) = L := by
  unfold RootCatalogueBudget.input
  rw [image_lifted_input _ _ _ hpin]
  exact SplitPorts.root_image X L hL

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalInput

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalInput.original_input_image
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalInput.injective_lifted_input
