/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox00
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox01
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox02
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox03
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox04
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox05
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox06
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox07
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox08
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox09
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox10
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox11
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox12
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox13
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox14
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox15
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox16
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox17
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox18
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox19
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox20
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox21
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox22
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox23
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox24
public import PartitionedTriangleAbsorption.BlowupB.Census.CertifiedBox25

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem all_boxes_covered (b : Fin 26) : ∀ C ∈ (box b).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  fin_cases b
  · exact covered_00
  · exact covered_01
  · exact covered_02
  · exact covered_03
  · exact covered_04
  · exact covered_05
  · exact covered_06
  · exact covered_07
  · exact covered_08
  · exact covered_09
  · exact covered_10
  · exact covered_11
  · exact covered_12
  · exact covered_13
  · exact covered_14
  · exact covered_15
  · exact covered_16
  · exact covered_17
  · exact covered_18
  · exact covered_19
  · exact covered_20
  · exact covered_21
  · exact covered_22
  · exact covered_23
  · exact covered_24
  · exact covered_25

/-- Exhaustion of the full admissible universe by the candidate list,
with an actual permutation of the labels, not merely a numerical match. -/
theorem family_has_representative (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) :
    ∃ m ∈ representativeMasks, ∃ s : Equiv.Perm (Fin 4),
      decode (decodeMask m) = F.image (Multiset.map s) := by
  obtain ⟨b,hb,hd⟩ := family_in_one_of_26 F hcard hused hforbidden
  have hu := (admissible_encode F hcard hused hforbidden).1
  obtain ⟨i, hi⟩ := all_boxes_covered b (encode F) hb hu
  have hm := repMem_sound (familyMask (actCode i (encode F))) hi
  refine ⟨familyMask (actCode i (encode F)), hm, sigma i, ?_⟩
  rw [decodeMask_familyMask, decode_actCode, hd]

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.family_has_representative
