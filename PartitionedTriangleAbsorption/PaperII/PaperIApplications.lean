/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.RoutedPaper
public import PartitionedTriangleAbsorption.BlowupB.KeevashPermApplications
public import PartitionedTriangleAbsorption.F0OrderedTheorem
public import PartitionedTriangleAbsorption.PaperII.FourColourApplication
public import PartitionedTriangleAbsorption.BlowupB.LemmaSC.OnePart

@[expose] public section

/-! Paper II's application corollaries used by Paper I. This entry point does
not import the full finite-family census or the proof of Nash-Williams. -/

#print axioms PaddedGeneral.RealInverse.idealized_F12
#print axioms PartitionedTriangleAbsorption.BlowupB.F0Direct.theorem146_ordered
#print axioms NashWilliams18.PaperII.margin_four_colour_decomposition
#print axioms PartitionedTriangleAbsorption.BlowupB.LemmaSC.absorber_onePart
