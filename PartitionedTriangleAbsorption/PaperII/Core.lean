/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.ThreeStepFamily
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer
public import PartitionedTriangleAbsorption.BlowupB.TeoremaBBalanced
public import PartitionedTriangleAbsorption.BlowupB.LemmaSC.OnePart

@[expose] public section

/-! General construction theorems of Paper II. No finite family census or
Nash-Williams application adapter is imported by this entry point. -/

#print axioms PaddedGeneral.RealInverse.keevashTypedSpec_of_threeStepLinks
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer.physicalCycRefiner3
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_of_keevash
#print axioms PartitionedTriangleAbsorption.BlowupB.LemmaSC.absorber_onePart
