/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedAll
public import PartitionedTriangleAbsorption.BlowupB.Census.TypedRelabelling

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

open PartitionedTriangleAbsorption.TypedTransformer

theorem relabel_familyFacts (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F)
    (s : Equiv.Perm (Fin 4)) : PaddedGeneral.FamilyFacts (F.image (Multiset.map s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨σ, hσ, hστ⟩ := Finset.mem_image.mp hτ
    rw [← hστ, Multiset.card_map]
    exact hcard σ hσ
  · intro i j k ht
    refine ⟨⟨j, ?_⟩, ⟨i, ?_⟩⟩
    · exact (link_swap _ i j k).mp ht
    · exact (link_swap _ j i k).mp ((link_root_swap _ i j k).mp ht)
  · intro a
    obtain ⟨b, hb⟩ := hforbidden (s.symm a)
    refine ⟨s b, ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨τ, hτ, he⟩ := Finset.mem_image.mp hz
    have he' : τ = ({s.symm a, b, s.symm z} : Multiset (Fin 4)) := by
      simpa [Multiset.map_map] using congrArg (Multiset.map s.symm) he
    exact hb ⟨s.symm z, he' ▸ hτ⟩

/-- No census-membership premise: the original labelled family has the typed
decomposition specification, not merely an existentially renamed family. -/
theorem keevashTypedSpec_of_admissible (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) : KeevashTypedSpec F := by
  obtain ⟨s, hs⟩ := admissible_has_closed765_relabelling F hcard hused hforbidden
  have hspec := keevashTypedSpec_of_closed765 (F.image (Multiset.map s))
    (relabel_familyFacts F hcard hforbidden s) hs
  have hback : permFam s.symm (F.image (Multiset.map s)) = F := by
    rw [permFam_eq_image]
    exact relabel_inverse F s
  simpa only [hback] using keevashTypedSpec_relabel s.symm hspec

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.relabel_familyFacts
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.keevashTypedSpec_of_admissible
