/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger

@[expose] public section

/-! Endpoint charges are paid by the actual degrees of the fixed catalogue
under an arbitrary anchor map. Vertex identifications are allowed. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge

open Finset Cycles WeightedEdgeLedger

variable {A V : Type} [Fintype A] [DecidableEq A] [DecidableEq V]

theorem endpoint_fibre (lib : Finset (Finset (A × A))) (f : A → V)
    (endpoint : A × A → A) (r : V) :
    (∑ e ∈ CatalogueWeights.arcs lib,
      if f (endpoint e) = r then CatalogueWeights.weight lib e else 0) =
    ∑ v, if f v = r then (∑ e ∈ CatalogueWeights.arcs lib,
      if endpoint e = v then CatalogueWeights.weight lib e else 0) else 0 := by
  have hexpand : ∀ e, (if f (endpoint e) = r then CatalogueWeights.weight lib e else 0) =
      ∑ v : A, if f v = r then
        (if endpoint e = v then CatalogueWeights.weight lib e else 0) else 0 := by
    intro e
    have heq : ∀ v, (if f v = r then
        (if endpoint e = v then CatalogueWeights.weight lib e else 0) else 0) =
        if v = endpoint e then
          (if f (endpoint e) = r then CatalogueWeights.weight lib e else 0) else 0 := by
      intro v
      by_cases hv : v = endpoint e
      · simp [hv]
      · simp [hv, Ne.symm hv]
    simp_rw [heq]
    simp
  simp_rw [hexpand]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : f v = r <;> simp [hv]

theorem endpoints (lib : Finset (Finset (A × A))) (f : A → V) (r : V) :
    (∑ e ∈ CatalogueWeights.arcs lib,
      ((if f e.2 = r then CatalogueWeights.weight lib e else 0) +
        (if f e.1 = r then CatalogueWeights.weight lib e else 0))) =
    ∑ v, if f v = r then catalogLoad lib v else 0 := by
  rw [sum_add_distrib, endpoint_fibre lib f Prod.snd,
    endpoint_fibre lib f Prod.fst, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases hv : f v = r
  · simp only [hv, ite_true]
    exact CatalogueWeights.incident lib v
  · simp [hv]

theorem total_degree (lib : Finset (Finset (A × A))) :
    ∑ v, catalogLoad lib v = 2 * ∑ e ∈ CatalogueWeights.arcs lib,
      CatalogueWeights.weight lib e := by
  have h := endpoints lib (fun _ => ()) ()
  simp only [ite_true] at h
  rw [sum_add_distrib] at h
  omega

/-- The complete endpoint precharge of the routed arcs is bounded by the
degree load of the same catalogue at its chosen physical anchors. -/
theorem endpoint_load_le (lib : Finset (Finset (A × A))) (f : A → V) (r : V) :
    (∑ e ∈ CatalogueWeights.arcs lib,
      endpointCharge (CatalogueWeights.weight lib e : ℝ) (f e.1) (f e.2) r) ≤
    ∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0 := by
  have heq : (∑ e ∈ CatalogueWeights.arcs lib,
      ((if f e.2 = r then (CatalogueWeights.weight lib e : ℝ) else 0) +
        (if f e.1 = r then (CatalogueWeights.weight lib e : ℝ) else 0))) =
      ∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0 := by
    exact_mod_cast endpoints lib f r
  rw [← heq]
  apply sum_le_sum
  intro e _
  unfold endpointCharge
  split_ifs <;> simp_all [eq_comm]

theorem retained_endpoint_load_le (lib : Finset (Finset (A × A)))
    (I : Finset (A × A)) (hI : I ⊆ CatalogueWeights.arcs lib) (f : A → V) (r : V) :
    (∑ e ∈ I, endpointCharge (CatalogueWeights.weight lib e : ℝ) (f e.1) (f e.2) r) +
      (∑ e ∈ CatalogueWeights.arcs lib \ I,
        endpointCharge (CatalogueWeights.weight lib e : ℝ) (f e.1) (f e.2) r) ≤
      ∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0 := by
  rw [add_comm, sum_sdiff hI]
  exact endpoint_load_le lib f r

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge.endpoint_load_le
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge.total_degree
