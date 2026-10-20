/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment

@[expose] public section

/-! Charge the actual extra catalogue after lifting it into the mesoscopic
extension. Both loads and mass concern one union, not unrelated witnesses. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment

open Finset Cycles

variable {V U : Type} [DecidableEq V] [DecidableEq U]

theorem old_load (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U))))
    (extra : Finset (Finset (V × V))) (v : V) :
    catalogLoad (lib ∪ CatalogueLift.lift U extra) (Sum.inl v) ≤
      catalogLoad lib (Sum.inl v) + catalogLoad extra v :=
  (CatalogueAugment.load_union_le _ _ _).trans
    (Nat.add_le_add_left (CatalogueLift.old_load U extra v) _)

theorem new_load (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U))))
    (extra : Finset (Finset (V × V))) (u : U) :
    catalogLoad (lib ∪ CatalogueLift.lift U extra) (Sum.inr u) ≤
      catalogLoad lib (Sum.inr u) := by
  simpa only [CatalogueLift.new_load, Nat.add_zero] using
    CatalogueAugment.load_union_le lib (CatalogueLift.lift U extra) (Sum.inr u)

theorem mass (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U))))
    (extra : Finset (Finset (V × V))) (K H : ℕ)
    (hlib : ∀ Q ∈ lib, Q.card ≤ K) (hextra : ∀ Q ∈ extra, Q.card ≤ H) :
    ∑ e ∈ CatalogueWeights.arcs (lib ∪ CatalogueLift.lift U extra),
      CatalogueWeights.weight (lib ∪ CatalogueLift.lift U extra) e ≤
        K * lib.card + H * extra.card := by
  exact (CatalogueAugment.mass_union_le lib (CatalogueLift.lift U extra) K H hlib
    (fun _ hQ => CatalogueLift.piece_size U extra H hextra hQ)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left H (CatalogueLift.size U extra)) _)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment.old_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment.new_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment.mass
