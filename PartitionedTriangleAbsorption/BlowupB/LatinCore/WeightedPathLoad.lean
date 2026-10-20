/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger

@[expose] public section

/-! Catalogue multiplicity multiplies the entire path load. This exact identity
complements the unweighted used-edge bound in WeightedEdgeLedger. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathLoad

open Finset AntiEdgeSelection PaddedNoCommon WeightedEdgeLedger

variable {V : Type} [Fintype V] [DecidableEq V]

theorem weighted_path_load {G : SimpleGraph V} {u x y z v : V}
    (huv : u ≠ v) (hp : IsPath4 G u x y z v) (weight : ℝ) (r : V) :
    weight * (incidentLoad (pathEdges u x y z v) r : ℝ) =
      endpointCharge weight u v r + interiorCharge weight x y z r := by
  have hh := pathEdges_incidentLoad huv hp r
  have heq : (incidentLoad (pathEdges u x y z v) r : ℝ) =
      (incidentLoad {s(u,v)} r : ℝ) +
        2 * (if r = x ∨ r = y ∨ r = z then 1 else 0 : ℝ) := by
    exact_mod_cast hh
  have hsingle : (incidentLoad {s(u,v)} r : ℝ) =
      (if r = u ∨ r = v then 1 else 0 : ℝ) := by
    rw [incidentLoad_eq_sum, sum_singleton]
    by_cases hr : r = u ∨ r = v <;> simp [Sym2.mem_iff, hr]
  rw [heq, hsingle]
  unfold endpointCharge interiorCharge
  split_ifs <;> ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathLoad

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathLoad.weighted_path_load
