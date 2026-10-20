/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.Tri
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RefinerAbsorber

@[expose] public section

/-! Native three-label absorber consumer. This does not assert the still-open
physical refiner producer, and introduces no fourth palette class. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge

theorem triUniversalCert_of_triRefiner (h : TriRefiner) :
    ∃ L, RefinerAbsorber.UniversalFamilyCert F_tri L := by
  have hcard : ∀ τ ∈ F_tri, Multiset.card τ = 3 := by
    unfold F_tri
    decide
  exact RefinerAbsorber.universalCert_of_balancedRefiner F_tri hcard h

theorem triUniversalCert_of_physicalCycRefiner3 (h : PhysicalCycRefiner3) :
    ∃ L, RefinerAbsorber.UniversalFamilyCert F_tri L :=
  triUniversalCert_of_triRefiner (triRefiner_of_physicalCycRefiner3 h)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge
