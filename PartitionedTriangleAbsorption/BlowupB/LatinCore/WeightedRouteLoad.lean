/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathLoad

@[expose] public section

/-! The endpoint-precharged ledger controls the full weighted load of the
same family of physical paths, including a retained input contribution.
This is a load transfer, not an existence assertion for the embedding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRouteLoad

open Finset AntiEdgeSelection PaddedNoCommon WeightedEdgeLedger

variable {V I : Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem family_load_le (G : SimpleGraph V) (E : Finset I)
    (u v x y z : I → V) (weight : I → ℝ) (base initial : V → ℝ)
    (huv : ∀ e ∈ E, u e ≠ v e)
    (hp : ∀ e ∈ E, IsPath4 G (u e) (x e) (y e) (z e) (v e))
    (hpre : ∀ r, base r +
      (∑ e ∈ E, endpointCharge (weight e) (u e) (v e) r) ≤ initial r)
    (r : V) :
    base r + (∑ e ∈ E, weight e *
      (incidentLoad (pathEdges (u e) (x e) (y e) (z e) (v e)) r : ℝ)) ≤
      initial r + ∑ e ∈ E, interiorCharge (weight e) (x e) (y e) (z e) r := by
  have heq := sum_congr rfl (fun e he =>
    WeightedPathLoad.weighted_path_load (huv e he) (hp e he) (weight e) r)
  rw [heq, sum_add_distrib, ← add_assoc]
  exact add_le_add (hpre r) le_rfl

theorem family_load_cap (G : SimpleGraph V) (E : Finset I)
    (u v x y z : I → V) (weight : I → ℝ) (base initial : V → ℝ)
    (huv : ∀ e ∈ E, u e ≠ v e)
    (hp : ∀ e ∈ E, IsPath4 G (u e) (x e) (y e) (z e) (v e))
    (hpre : ∀ r, base r +
      (∑ e ∈ E, endpointCharge (weight e) (u e) (v e) r) ≤ initial r)
    (cap : ℝ) (hcap : ∀ r, initial r +
      (∑ e ∈ E, interiorCharge (weight e) (x e) (y e) (z e) r) ≤ cap) :
    ∀ r, base r + (∑ e ∈ E, weight e *
      (incidentLoad (pathEdges (u e) (x e) (y e) (z e) (v e)) r : ℝ)) ≤ cap := by
  intro r
  exact (family_load_le G E u v x y z weight base initial huv hp hpre r).trans (hcap r)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRouteLoad

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRouteLoad.family_load_le
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRouteLoad.family_load_cap
