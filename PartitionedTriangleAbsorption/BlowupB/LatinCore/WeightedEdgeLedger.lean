/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Paths

@[expose] public section

/-! The used-edge degree is paid by ALL precharged endpoints plus the current
interior load. Paths are indexed: different arcs may have the same physical
endpoints. No injectivity of the anchor map is needed for this bound. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger

open Finset AntiEdgeSelection PaddedNoCommon

variable {V I : Type} [Fintype V] [DecidableEq V] [DecidableEq I]

def endpointCharge (w : ℝ) (u v r : V) : ℝ := if r = u ∨ r = v then w else 0

def interiorCharge (w : ℝ) (x y z r : V) : ℝ :=
  if r = x ∨ r = y ∨ r = z then 2 * w else 0

theorem path_load_le {G : SimpleGraph V} {u x y z v : V}
    (huv : u ≠ v) (hp : IsPath4 G u x y z v) (w : ℝ) (hw : 1 ≤ w) (r : V) :
    (incidentLoad (pathEdges u x y z v) r : ℝ) ≤
      endpointCharge w u v r + interiorCharge w x y z r := by
  have hh := pathEdges_incidentLoad huv hp r
  have heq : (incidentLoad (pathEdges u x y z v) r : ℝ) =
      (incidentLoad {s(u,v)} r : ℝ) +
        2 * (if r = x ∨ r = y ∨ r = z then 1 else 0 : ℝ) := by exact_mod_cast hh
  have hsingle : (incidentLoad {s(u,v)} r : ℝ) =
      (if r = u ∨ r = v then 1 else 0 : ℝ) := by
    rw [incidentLoad_eq_sum, sum_singleton]
    by_cases hr : r = u ∨ r = v <;> simp [Sym2.mem_iff, hr]
  rw [heq, hsingle]
  unfold endpointCharge interiorCharge
  split_ifs <;> linarith

theorem used_load_le (G : SimpleGraph V) (X : Finset (Sym2 V))
    (E S : Finset I) (hSE : S ⊆ E) (u v x y z : I → V) (weight : I → ℝ)
    (hweight : ∀ e ∈ E, 1 ≤ weight e)
    (huv : ∀ e ∈ S, u e ≠ v e)
    (hpath : ∀ e ∈ S, IsPath4 G (u e) (x e) (y e) (z e) (v e))
    (initial : V → ℝ) (hpre : ∀ r,
      (∑ e ∈ E, endpointCharge (weight e) (u e) (v e) r) ≤ initial r)
    (d : ℝ) (hX : DegBounded X d) (r : V) :
    (incidentLoad (X ∪ S.biUnion (fun e => pathEdges (u e) (x e) (y e) (z e) (v e))) r : ℝ) ≤
      d + initial r + ∑ e ∈ S, interiorCharge (weight e) (x e) (y e) (z e) r := by
  classical
  let P := fun e => pathEdges (u e) (x e) (y e) (z e) (v e)
  have hU : incidentLoad (X ∪ S.biUnion P) r ≤
      incidentLoad X r + incidentLoad (S.biUnion P) r := by
    unfold incidentLoad
    rw [filter_union]
    exact card_union_le _ _
  have hB : incidentLoad (S.biUnion P) r ≤ ∑ e ∈ S, incidentLoad (P e) r := by
    unfold incidentLoad
    rw [filter_biUnion]
    exact card_biUnion_le
  have hU' : (incidentLoad (X ∪ S.biUnion P) r : ℝ) ≤
      (incidentLoad X r : ℝ) + incidentLoad (S.biUnion P) r := by exact_mod_cast hU
  have hB' : (incidentLoad (S.biUnion P) r : ℝ) ≤
      ∑ e ∈ S, (incidentLoad (P e) r : ℝ) := by exact_mod_cast hB
  have hsum := sum_le_sum (s := S) fun e he =>
    path_load_le (huv e he) (hpath e he) (weight e) (hweight e (hSE he)) r
  rw [sum_add_distrib] at hsum
  have hep : (∑ e ∈ S, endpointCharge (weight e) (u e) (v e) r) ≤ initial r := by
    apply le_trans ?_ (hpre r)
    apply sum_le_sum_of_subset_of_nonneg hSE
    intro e he _
    unfold endpointCharge
    split_ifs <;> linarith [hweight e he]
  have hx := hX r
  change (incidentLoad X r : ℝ) ≤ d at hx
  change (incidentLoad (X ∪ S.biUnion P) r : ℝ) ≤ _
  change (∑ e ∈ S, (incidentLoad (P e) r : ℝ)) ≤ _ at hsum
  linarith

/-- Uniform cap needed by the next guarded path choice. Future endpoints
are already included in initial, so no uncharged endpoint loss is hidden. -/
theorem degree_bound (G : SimpleGraph V) (X : Finset (Sym2 V))
    (E S : Finset I) (hSE : S ⊆ E) (u v x y z : I → V) (weight : I → ℝ)
    (hweight : ∀ e ∈ E, 1 ≤ weight e) (huv : ∀ e ∈ S, u e ≠ v e)
    (hpath : ∀ e ∈ S, IsPath4 G (u e) (x e) (y e) (z e) (v e))
    (initial : V → ℝ) (hpre : ∀ r,
      (∑ e ∈ E, endpointCharge (weight e) (u e) (v e) r) ≤ initial r)
    (d T W : ℝ) (hX : DegBounded X d)
    (hcap : ∀ r, initial r + ∑ e ∈ S,
      interiorCharge (weight e) (x e) (y e) (z e) r ≤ T + 2 * W) :
    DegBounded (X ∪ S.biUnion (fun e => pathEdges (u e) (x e) (y e) (z e) (v e)))
      (d + T + 2 * W) := by
  intro r
  have hh := used_load_le G X E S hSE u v x y z weight hweight huv hpath initial hpre d hX r
  have hc := hcap r
  change (incidentLoad (X ∪ S.biUnion
    (fun e => pathEdges (u e) (x e) (y e) (z e) (v e))) r : ℝ) ≤ d + T + 2 * W
  linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger.degree_bound
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger.degree_bound
