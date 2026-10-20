/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReplacementLoad
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.CycOrient
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger

@[expose] public section

/-! The computed weighted path load controls the actual image catalogue,
including its retained singleton input arcs. Deduplication only lowers load. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalCatalogueLoad

open Finset Cycles AntiEdgeSelection PaddedNoCommon WeightedEdgeLedger PhysicalReplacement

variable {A V : Type} [DecidableEq A] [Fintype V] [DecidableEq V]

theorem load_le (lib : Finset (Finset (A × A))) (I : Finset (A × A))
    (hI : I ⊆ CatalogueWeights.arcs lib) (f : A → V) (x y z : (A × A) → V)
    (c : V → ZMod 3)
    (hcyc : ∀ e ∈ CatalogueWeights.arcs lib, IsCyc c (PhysicalReplacement.block I f x y z e))
    (cap : ℝ) (hcap : ∀ r,
      (∑ e ∈ I, endpointCharge (CatalogueWeights.weight lib e : ℝ) (f e.1) (f e.2) r) +
        (∑ e ∈ CatalogueWeights.arcs lib \ I, (CatalogueWeights.weight lib e : ℝ) *
          (incidentLoad (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) r : ℝ)) ≤ cap) :
    ∀ r, (catalogLoad (lib.image (fun P => P.biUnion (PhysicalReplacement.block I f x y z))) r : ℝ) ≤ cap := by
  intro r
  have hi : ∀ e ∈ I, (CatalogueWeights.weight lib e : ℝ) * (deg (PhysicalReplacement.block I f x y z e) r : ℝ) =
      endpointCharge (CatalogueWeights.weight lib e : ℝ) (f e.1) (f e.2) r := by
    intro e he
    have hd := Bridge.incidentLoad_symImageBy (hcyc e (hI he)) r
    have hs : Bridge.symImage (PhysicalReplacement.block I f x y z e) = {s(f e.1,f e.2)} := by
      simp [Bridge.symImage, PhysicalReplacement.block, he]
    rw [hs] at hd
    have hsingle : (incidentLoad ({s(f e.1,f e.2)} : Finset (Sym2 V)) r : ℝ) =
        if r = f e.1 ∨ r = f e.2 then 1 else 0 := by
      rw [incidentLoad_eq_sum, sum_singleton]
      simp [Sym2.mem_iff]
    rw [← hd, hsingle]
    unfold endpointCharge
    split_ifs <;> ring
  have he : ∀ e ∈ CatalogueWeights.arcs lib \ I,
      (CatalogueWeights.weight lib e : ℝ) * (deg (PhysicalReplacement.block I f x y z e) r : ℝ) =
      (CatalogueWeights.weight lib e : ℝ) *
        (incidentLoad (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) r : ℝ) := by
    intro e he
    have hd := Bridge.incidentLoad_symImageBy (hcyc e (mem_sdiff.mp he).1) r
    have hs : Bridge.symImage (PhysicalReplacement.block I f x y z e) =
        pathEdges (f e.1) (x e) (y e) (z e) (f e.2) := by
      simpa only [PhysicalReplacement.block, (mem_sdiff.mp he).2, ite_false,
        Bridge.symImage, PhysicalPathArcs.forget] using
        PhysicalPathArcs.symImage_eq (f e.1) (x e) (y e) (z e) (f e.2)
    rw [hs] at hd
    rw [hd]
  have hsum : (∑ e ∈ CatalogueWeights.arcs lib,
      (CatalogueWeights.weight lib e : ℝ) * (deg (PhysicalReplacement.block I f x y z e) r : ℝ)) ≤ cap := by
    rw [← sum_sdiff hI, sum_congr rfl he, sum_congr rfl hi, add_comm]
    exact hcap r
  have hnat := CatalogueReplacementLoad.catalogue_load_le lib (PhysicalReplacement.block I f x y z) r
  have hreal : (catalogLoad (lib.image (fun P => P.biUnion (PhysicalReplacement.block I f x y z))) r : ℝ) ≤
      ∑ e ∈ CatalogueWeights.arcs lib,
        (CatalogueWeights.weight lib e : ℝ) * (deg (PhysicalReplacement.block I f x y z e) r : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hsum

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalCatalogueLoad

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalCatalogueLoad.load_le
