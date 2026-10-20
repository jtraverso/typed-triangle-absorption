/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaB765
public import PartitionedTriangleAbsorption.BlowupB.Census.Audit
public import PartitionedTriangleAbsorption.BlowupB.Census.Universal

@[expose] public section

/-! Finite-family certificates, including the seventeen conserved families.
The finite census proves coverage and uniqueness under actual permutations.
Its bridge to Closed765 and typed-specification transport give the theorem
for every admissible four-label family, without a catalogue-membership premise. -/

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.all_family_certificates
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.all_typed_specs
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_of_closed765
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representativeMasks_card
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.census_complete
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representative_closed765
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.keevashTypedSpec_of_admissible
