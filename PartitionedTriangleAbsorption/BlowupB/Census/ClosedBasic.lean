/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaB765
public import PartitionedTriangleAbsorption.BlowupB.Census.Action

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem identity_perm_family (F : Finset (Multiset (Fin 4))) :
    F = permFam (1 : Equiv.Perm (Fin 4)) F := by
  ext τ
  simp [permFam]

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.identity_perm_family
