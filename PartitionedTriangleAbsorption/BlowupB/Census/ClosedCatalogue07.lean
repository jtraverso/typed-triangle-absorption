/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks07

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_07_0 :
    Closed765 (decode (actCode 3 (decodeMask 10760))) := by
  have he : decode (actCode 3 (decodeMask 10760)) =
      PaddedComponents.KQ3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ3)))⟩))))

theorem closed_07_1 :
    Closed765 (decode (actCode 12 (decodeMask 10761))) := by
  have he : decode (actCode 12 (decodeMask 10761)) =
      PaddedComponents.KQ6 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ6))))))⟩))))

theorem closed_07_2 :
    Closed765 (decode (actCode 3 (decodeMask 10762))) := by
  have he : decode (actCode 3 (decodeMask 10762)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR028 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR028)⟩)))))))))))

theorem closed_07_3 :
    Closed765 (decode (actCode 3 (decodeMask 10763))) := by
  have he : decode (actCode 3 (decodeMask 10763)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR029 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR029))⟩)))))))))))

theorem closed_07_4 :
    Closed765 (decode (actCode 3 (decodeMask 10777))) := by
  have he : decode (actCode 3 (decodeMask 10777)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR030 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR030)))⟩)))))))))))

theorem closed_07_5 :
    Closed765 (decode (actCode 1 (decodeMask 10778))) := by
  have he : decode (actCode 1 (decodeMask 10778)) =
      PaddedCharge.FnoC := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, identity_perm_family PaddedCharge.FnoC⟩)))))))))))))))))

theorem closed_07_6 :
    Closed765 (decode (actCode 1 (decodeMask 10779))) := by
  have he : decode (actCode 1 (decodeMask 10779)) =
      PaddedNoCommon.NC4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC4))))⟩))))))))))))))))))

theorem closed_07_7 :
    Closed765 (decode (actCode 12 (decodeMask 10896))) := by
  have he : decode (actCode 12 (decodeMask 10896)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC038 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨347, by decide +kernel⟩)))

theorem closed_07_8 :
    Closed765 (decode (actCode 12 (decodeMask 10928))) := by
  have he : decode (actCode 12 (decodeMask 10928)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL238 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨238, by decide +kernel⟩)))

theorem closed_07_9 :
    Closed765 (decode (actCode 12 (decodeMask 11400))) := by
  have he : decode (actCode 12 (decodeMask 11400)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL090 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨90, by decide +kernel⟩)))

theorem closed_07_10 :
    Closed765 (decode (actCode 12 (decodeMask 11401))) := by
  have he : decode (actCode 12 (decodeMask 11401)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR031 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR031)))⟩)))))))))))

theorem closed_07_11 :
    Closed765 (decode (actCode 12 (decodeMask 11404))) := by
  have he : decode (actCode 12 (decodeMask 11404)) =
      PaddedNoCommon.KT3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedNoCommon.KT3))⟩))))))))))))))))

theorem closed_07_12 :
    Closed765 (decode (actCode 4 (decodeMask 11405))) := by
  have he : decode (actCode 4 (decodeMask 11405)) =
      PaddedNoCommon.NC5 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC5)))))⟩))))))))))))))))))

theorem closed_07_13 :
    Closed765 (decode (actCode 12 (decodeMask 11780))) := by
  have he : decode (actCode 12 (decodeMask 11780)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL093 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨93, by decide +kernel⟩)))

theorem closed_07_14 :
    Closed765 (decode (actCode 12 (decodeMask 11781))) := by
  have he : decode (actCode 12 (decodeMask 11781)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL209 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨209, by decide +kernel⟩)))

theorem closed_07_15 :
    Closed765 (decode (actCode 3 (decodeMask 11785))) := by
  have he : decode (actCode 3 (decodeMask 11785)) =
      PaddedComponents.FB3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.FB3)))⟩))))))))))))))))

theorem closed_07_16 :
    Closed765 (decode (actCode 3 (decodeMask 11787))) := by
  have he : decode (actCode 3 (decodeMask 11787)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR032 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR032)⟩))))))))))))

theorem closed_07_17 :
    Closed765 (decode (actCode 12 (decodeMask 11788))) := by
  have he : decode (actCode 12 (decodeMask 11788)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR033 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR033))⟩))))))))))))

theorem closed_07_18 :
    Closed765 (decode (actCode 5 (decodeMask 11789))) := by
  have he : decode (actCode 5 (decodeMask 11789)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR034 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR034)))⟩))))))))))))

theorem closed_07_19 :
    Closed765 (decode (actCode 1 (decodeMask 11803))) := by
  have he : decode (actCode 1 (decodeMask 11803)) =
      PaddedNoCommon.NC7 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC7)))))))⟩))))))))))))))))))

theorem closed_07_20 :
    Closed765 (decode (actCode 12 (decodeMask 11904))) := by
  have he : decode (actCode 12 (decodeMask 11904)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL091 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨91, by decide +kernel⟩)))

theorem closed_07_21 :
    Closed765 (decode (actCode 12 (decodeMask 11905))) := by
  have he : decode (actCode 12 (decodeMask 11905)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL207 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨207, by decide +kernel⟩)))

theorem closed_07_22 :
    Closed765 (decode (actCode 12 (decodeMask 11908))) := by
  have he : decode (actCode 12 (decodeMask 11908)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL206 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨206, by decide +kernel⟩)))

theorem closed_07_23 :
    Closed765 (decode (actCode 4 (decodeMask 11909))) := by
  have he : decode (actCode 4 (decodeMask 11909)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL277 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨277, by decide +kernel⟩)))

theorem closed_07_24 :
    Closed765 (decode (actCode 12 (decodeMask 11912))) := by
  have he : decode (actCode 12 (decodeMask 11912)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR035 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR035)))⟩))))))))))))

theorem closed_07_25 :
    Closed765 (decode (actCode 5 (decodeMask 11913))) := by
  have he : decode (actCode 5 (decodeMask 11913)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR036 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR036)⟩)))))))))))))

theorem closed_07_26 :
    Closed765 (decode (actCode 12 (decodeMask 11916))) := by
  have he : decode (actCode 12 (decodeMask 11916)) =
      PaddedNoCommon.NC6 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC6))))))⟩))))))))))))))))))

theorem closed_07_27 :
    Closed765 (decode (actCode 4 (decodeMask 11917))) := by
  have he : decode (actCode 4 (decodeMask 11917)) =
      PaddedNoCommon.NC8 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC8))))))))⟩))))))))))))))))))

theorem closed_07_28 :
    Closed765 (decode (actCode 12 (decodeMask 11920))) := by
  have he : decode (actCode 12 (decodeMask 11920)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL155 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨155, by decide +kernel⟩)))

theorem closed_07_29 :
    Closed765 (decode (actCode 12 (decodeMask 11936))) := by
  have he : decode (actCode 12 (decodeMask 11936)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL184 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨184, by decide +kernel⟩)))

theorem closed_07_30 :
    Closed765 (decode (actCode 12 (decodeMask 11952))) := by
  have he : decode (actCode 12 (decodeMask 11952)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL240 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨240, by decide +kernel⟩)))

theorem closed_07_31 :
    Closed765 (decode (actCode 5 (decodeMask 12425))) := by
  have he : decode (actCode 5 (decodeMask 12425)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL122 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨122, by decide +kernel⟩)))

theorem checkedMasks07_closed (m : ℕ) (hm : m ∈ checkedMasks07) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks07, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_0
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_1
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_2
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_3
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_4
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_07_5
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_07_6
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_7
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_8
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_9
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_10
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_11
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_07_12
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_13
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_14
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_15
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_07_16
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_17
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_07_18
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_07_19
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_20
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_21
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_07_23
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_24
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_07_25
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_26
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_07_27
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_28
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_29
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_07_30
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_07_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks07_closed
