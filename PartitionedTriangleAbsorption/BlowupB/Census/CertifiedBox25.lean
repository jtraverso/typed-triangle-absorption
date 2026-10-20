/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Certificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

def certificate25_root : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 3) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 12)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate25_root_checked :
    certificate25_root.verify [5, 6, 8, 14] ∅ = true := rfl

theorem covered_25 : ∀ C ∈ (box 25).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [5, 6, 8, 14] ∅ certificate25_root
    certificate25_root_checked C
  have hs : C ⊆ ([5, 6, 8, 14] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_25
