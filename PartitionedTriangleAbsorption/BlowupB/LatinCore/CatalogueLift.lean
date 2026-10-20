/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Filling

@[expose] public section

/-! Lift the fixed unused-channel catalogue into the SAME vertex extension
as the mesoscopic catalogue. Old loads do not increase, and the new vertices
receive zero load from these pieces. No balance or physical embedding is assumed. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift

open Finset Cycles

variable {V : Type} [DecidableEq V]

def lift (U : Type) [DecidableEq U] (lib : Finset (Finset (V × V))) :
    Finset (Finset ((V ⊕ U) × (V ⊕ U))) :=
  lib.image (fun Q => Q.map (liftArc V U))

theorem size (U : Type) [DecidableEq U] (lib : Finset (Finset (V × V))) :
    (lift U lib).card ≤ lib.card := card_image_le

theorem piece_size (U : Type) [DecidableEq U] (lib : Finset (Finset (V × V)))
    (K : ℕ) (hK : ∀ Q ∈ lib, Q.card ≤ K) {Q} (hQ : Q ∈ lift U lib) :
    Q.card ≤ K := by
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hQ
  simpa only [card_map] using hK P hP

theorem old_load (U : Type) [DecidableEq U] (lib : Finset (Finset (V × V))) (v : V) :
    catalogLoad (lift U lib) (Sum.inl v) ≤ catalogLoad lib v := by
  unfold catalogLoad lift
  calc
    _ ≤ ∑ Q ∈ lib, deg (Q.map (liftArc V U)) (Sum.inl v) :=
      sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = _ := by
      apply sum_congr rfl
      intro Q _
      simp only [deg, inDeg_map_liftArc, outDeg_map_liftArc, Sum.elim_inl]

theorem new_load (U : Type) [DecidableEq U] (lib : Finset (Finset (V × V))) (u : U) :
    catalogLoad (lift U lib) (Sum.inr u) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold catalogLoad lift
  calc
    _ ≤ ∑ Q ∈ lib, deg (Q.map (liftArc V U)) (Sum.inr u) :=
      sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = 0 := by
      simp only [deg, inDeg_map_liftArc, outDeg_map_liftArc, Sum.elim_inr,
        Nat.add_zero, sum_const_zero]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift.old_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift.new_load
