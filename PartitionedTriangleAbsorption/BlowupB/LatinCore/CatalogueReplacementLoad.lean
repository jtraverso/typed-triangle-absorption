/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights

@[expose] public section

/-! The weights of the fixed catalogue pay for its actual replaced pieces.
Deduplicating pieces and identifying vertices can only lower this upper bound.
No disjointness or existence of a physical replacement is asserted here. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReplacementLoad

open Finset Cycles

variable {V W : Type} [DecidableEq V] [DecidableEq W]

theorem weighted_sum (lib : Finset (Finset (V × V))) (f : (V × V) → ℕ) :
    (∑ P ∈ lib, ∑ e ∈ P, f e) =
      ∑ e ∈ CatalogueWeights.arcs lib, CatalogueWeights.weight lib e * f e := by
  have hfilter : ∀ P ∈ lib,
      (CatalogueWeights.arcs lib).filter (fun e => e ∈ P) = P := by
    intro P hP
    ext e
    exact ⟨fun h => (mem_filter.mp h).2,
      fun h => mem_filter.mpr ⟨mem_biUnion.mpr ⟨P, hP, h⟩, h⟩⟩
  calc
    _ = ∑ P ∈ lib, ∑ e ∈ CatalogueWeights.arcs lib, if e ∈ P then f e else 0 := by
      apply sum_congr rfl
      intro P hP
      rw [← sum_filter, hfilter P hP]
    _ = ∑ e ∈ CatalogueWeights.arcs lib, ∑ P ∈ lib, if e ∈ P then f e else 0 :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro e _
      rw [← sum_filter]
      simp [CatalogueWeights.weight]

omit [DecidableEq V] in
theorem degree_replace_le (P : Finset (V × V))
    (path : (V × V) → Finset (W × W)) (w : W) :
    deg (P.biUnion path) w ≤ ∑ e ∈ P, deg (path e) w := by
  unfold deg inDeg outDeg
  rw [filter_biUnion, filter_biUnion, sum_add_distrib]
  exact Nat.add_le_add card_biUnion_le card_biUnion_le

theorem catalogue_load_le (lib : Finset (Finset (V × V)))
    (path : (V × V) → Finset (W × W)) (w : W) :
    catalogLoad (lib.image (fun P => P.biUnion path)) w ≤
      ∑ e ∈ CatalogueWeights.arcs lib, CatalogueWeights.weight lib e * deg (path e) w := by
  unfold catalogLoad
  calc
    _ ≤ ∑ P ∈ lib, deg (P.biUnion path) w :=
      sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ ≤ ∑ P ∈ lib, ∑ e ∈ P, deg (path e) w :=
      sum_le_sum (fun P _ => degree_replace_le P path w)
    _ = _ := weighted_sum lib (fun e => deg (path e) w)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReplacementLoad

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReplacementLoad.weighted_sum
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReplacementLoad.catalogue_load_le
