/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Coverage
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalAll

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

/-- Exact classification: every admissible family has one and only one key
in the list of 765 representatives, under actual permutations of labels. -/
theorem census_complete (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) :
    ∃! m : ℕ, m ∈ representativeMasks ∧ ∃ s : Equiv.Perm (Fin 4),
      decode (decodeMask m) = F.image (Multiset.map s) := by
  obtain ⟨m, hm, s, hs⟩ := family_has_representative F hcard hused hforbidden
  refine ⟨m, ⟨hm, s, hs⟩, ?_⟩
  rintro n ⟨hn, t, ht⟩
  have he : decode (decodeMask n) =
      (decode (decodeMask m)).image (Multiset.map (s.symm.trans t)) := by
    rw [hs]
    simpa [Finset.image_image, Multiset.map_map, Function.comp_def] using ht
  exact (representative_unique m n hm hn (s.symm.trans t) he).symm

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.census_complete
