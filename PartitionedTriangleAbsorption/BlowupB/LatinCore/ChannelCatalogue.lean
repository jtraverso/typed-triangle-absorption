/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.HubShortener

@[expose] public section

/-! The fixed extra catalogue consists of the actual private channel paths.
Its total load is the degree of their union, not the number of channels.
Balance is deliberately not claimed before identifying equal physical roots. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue

open Finset Cycles
-- Nested catalogues need a larger structural instance search, not a different equality.
set_option synthInstance.maxSize 1024

variable {P E : Type} [DecidableEq P] [Fintype E] [DecidableEq E]

def pieces (src dst : E → P) : Finset (Finset (RootPaths.Vert P E × RootPaths.Vert P E)) :=
  univ.image (RootPaths.pathArcs src dst)

theorem path_disjoint (src dst : E → P) {e f : E} (hne : e ≠ f) :
    Disjoint (RootPaths.pathArcs src dst e) (RootPaths.pathArcs src dst f) := by
  rw [disjoint_left]
  intro a ha hb
  simp only [RootPaths.pathArcs, mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with h | h | h <;> simp_all

theorem card_path (src dst : E → P) (e : E) :
    (RootPaths.pathArcs src dst e).card = 3 := by
  simp [RootPaths.pathArcs]

theorem size (src dst : E → P) : (pieces src dst).card ≤ Fintype.card E :=
  card_image_le.trans (by simp)

theorem piece_size (src dst : E → P) {Q} (hQ : Q ∈ pieces src dst) : Q.card = 3 := by
  obtain ⟨e, -, rfl⟩ := mem_image.mp hQ
  exact card_path src dst e

theorem load_le (src dst : E → P) (v : RootPaths.Vert P E) :
    catalogLoad (pieces src dst) v ≤ deg (RootPaths.arcs src dst) v := by
  unfold catalogLoad pieces
  calc _ ≤ ∑ e : E, deg (RootPaths.pathArcs src dst e) v :=
      sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = deg (RootPaths.arcs src dst) v :=
      (Hub.deg_biUnion univ (RootPaths.pathArcs src dst)
        (fun e _ f _ hne => path_disjoint src dst hne) v).symm

theorem augmented_load (src dst : E → P)
    (lib : Finset (Finset (RootPaths.Vert P E × RootPaths.Vert P E)))
    (v : RootPaths.Vert P E) :
    catalogLoad (lib ∪ pieces src dst) v ≤
      catalogLoad lib v + deg (RootPaths.arcs src dst) v :=
  (CatalogueAugment.load_union_le lib (pieces src dst) v).trans
    (Nat.add_le_add_left (load_le src dst v) _)

/-- Add the real channel paths in the SAME extension as the mesoscopic
catalogue, charging only their degree at each old vertex. -/
theorem extended_load (src dst : E → P) (U : Type) [DecidableEq U]
    (lib : Finset (Finset ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))))
    (v : RootPaths.Vert P E) :
    catalogLoad (lib ∪ CatalogueLift.lift U (pieces src dst)) (Sum.inl v) ≤
      catalogLoad lib (Sum.inl v) + deg (RootPaths.arcs src dst) v :=
  (CatalogueLiftAugment.old_load lib (pieces src dst) v).trans
    (Nat.add_le_add_left (load_le src dst v) _)

theorem extended_new_load (src dst : E → P) (U : Type) [DecidableEq U]
    (lib : Finset (Finset ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))))
    (u : U) :
    catalogLoad (lib ∪ CatalogueLift.lift U (pieces src dst)) (Sum.inr u) ≤
      catalogLoad lib (Sum.inr u) :=
  CatalogueLiftAugment.new_load lib (pieces src dst) u

theorem extended_mass (src dst : E → P) (U : Type) [DecidableEq U]
    (lib : Finset (Finset ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))))
    (K : ℕ) (hlib : ∀ Q ∈ lib, Q.card ≤ K) :
    ∑ e ∈ CatalogueWeights.arcs (lib ∪ CatalogueLift.lift U (pieces src dst)),
      CatalogueWeights.weight (lib ∪ CatalogueLift.lift U (pieces src dst)) e ≤
        K * lib.card + 3 * Fintype.card E := by
  exact (CatalogueLiftAugment.mass lib (pieces src dst) K 3 hlib
    (fun _ hQ => (piece_size src dst hQ).le)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (size src dst)) _)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue.load_le
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue.augmented_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue.extended_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue.extended_mass
