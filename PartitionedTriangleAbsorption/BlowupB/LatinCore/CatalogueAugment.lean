/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights

@[expose] public section

/-! Add the fixed pieces for unused routing channels to the SAME catalogue.
Deduplication by union can only reduce weights, mass and pinned load. These
identities do not assume that unused-channel pieces are abstractly balanced. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment

open Finset Cycles

variable {V : Type} [DecidableEq V]

theorem arcs_union (lib extra : Finset (Finset (V × V))) :
    CatalogueWeights.arcs (lib ∪ extra) =
      CatalogueWeights.arcs lib ∪ CatalogueWeights.arcs extra := by
  exact union_biUnion

theorem weight_union_le (lib extra : Finset (Finset (V × V))) (e : V × V) :
    CatalogueWeights.weight (lib ∪ extra) e ≤
      CatalogueWeights.weight lib e + CatalogueWeights.weight extra e := by
  unfold CatalogueWeights.weight
  rw [filter_union]
  exact card_union_le _ _

theorem load_union_le (lib extra : Finset (Finset (V × V))) (v : V) :
    catalogLoad (lib ∪ extra) v ≤ catalogLoad lib v + catalogLoad extra v := by
  unfold catalogLoad
  have h := sum_union_inter (s₁ := lib) (s₂ := extra) (f := fun P => deg P v)
  omega

theorem mass_union_le (lib extra : Finset (Finset (V × V))) (K H : ℕ)
    (hlib : ∀ P ∈ lib, P.card ≤ K) (hextra : ∀ P ∈ extra, P.card ≤ H) :
    ∑ e ∈ CatalogueWeights.arcs (lib ∪ extra),
      CatalogueWeights.weight (lib ∪ extra) e ≤ K * lib.card + H * extra.card := by
  rw [CatalogueWeights.total]
  have hu := sum_union_inter (s₁ := lib) (s₂ := extra) (f := fun P => P.card)
  have hl : (∑ P ∈ lib, P.card) ≤ K * lib.card := by
    calc _ ≤ ∑ _P ∈ lib, K := sum_le_sum hlib
      _ = _ := by simp [mul_comm]
  have he : (∑ P ∈ extra, P.card) ≤ H * extra.card := by
    calc _ ≤ ∑ _P ∈ extra, H := sum_le_sum hextra
      _ = _ := by simp [mul_comm]
  omega

theorem pinned_load (lib extra : Finset (Finset (V × V))) (v : V) (d : ℕ)
    (hlib : catalogLoad lib v ≤ 73 * d) (hextra : catalogLoad extra v ≤ 16) :
    catalogLoad (lib ∪ extra) v ≤ 73 * d + 16 := by
  exact (load_union_le lib extra v).trans (Nat.add_le_add hlib hextra)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment.mass_union_le
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAugment.pinned_load
