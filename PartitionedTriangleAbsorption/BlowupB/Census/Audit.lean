/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Representatives

@[expose] public section

/-! Audit of the proved finite-domain reduction. This does not assert that
the numerical representative list is exhaustive or orbit-inequivalent. -/

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.tri_exhaustive
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.decode_encode
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.encode_decode
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.family_in_one_of_26
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.family_card_le_twelve
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.familyMask_injective
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representativeMasks_card
