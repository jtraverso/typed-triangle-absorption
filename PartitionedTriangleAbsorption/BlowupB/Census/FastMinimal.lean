/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.FastCertificate
public import PartitionedTriangleAbsorption.BlowupB.Census.Uniqueness

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

/-- The fast list action proves exactly the original representative predicate. -/
theorem goodRepresentative_of_list (xs : List (Fin 20)) (m : ℕ)
    (ha : Admissible xs.toFinset) (hm : familyMask xs.toFinset = m)
    (hl : ∀ i : Fin 24, m ≤ listActionMask i xs) : GoodRepresentative m := by
  have hd : decodeMask m = xs.toFinset := by rw [← hm, decodeMask_familyMask]
  unfold GoodRepresentative
  rw [hd]
  refine ⟨ha, hm, ?_⟩
  intro i
  rw [← listActionMask_correct, hm]
  exact hl i

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.goodRepresentative_of_list
