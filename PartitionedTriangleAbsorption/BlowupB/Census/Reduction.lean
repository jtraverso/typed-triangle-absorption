/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Boxes

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus
open Finset

theorem admissible_encode (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) :
    Admissible (encode F) := by
  constructor
  · intro a
    obtain ⟨τ,hτ,ha⟩ := hused a
    obtain ⟨i,hi⟩ := tri_exhaustive (hcard τ hτ)
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi ▸ hτ⟩, hi ▸ ha⟩
  · intro a
    obtain ⟨b,hb⟩ := hforbidden a
    exact ⟨b, fun h => hb ((allowed_encode_iff F a b).mp h)⟩

/-- Complete finite-domain reduction for arbitrary mathematical families,
not only for families already listed by the census generator. -/
theorem family_in_one_of_26 (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) :
    ∃ b : Fin 26, encode F ∈ (box b).powerset ∧ decode (encode F) = F := by
  obtain ⟨b,hb⟩ := admissible_subset_one_of_26 (encode F)
    (admissible_encode F hcard hused hforbidden)
  exact ⟨b,hb,decode_encode F hcard⟩

theorem family_card_le_twelve (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) : F.card ≤ 12 := by
  obtain ⟨b,hb,hdecode⟩ := family_in_one_of_26 F hcard hused hforbidden
  have hc : F.card = (encode F).card := by
    have h := congrArg Finset.card hdecode
    simpa only [decode, card_image_of_injective _ tri_injective] using h.symm
  rw [hc]
  exact (card_le_card (mem_powerset.mp hb)).trans (box_card_le b)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.family_in_one_of_26
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.family_card_le_twelve
