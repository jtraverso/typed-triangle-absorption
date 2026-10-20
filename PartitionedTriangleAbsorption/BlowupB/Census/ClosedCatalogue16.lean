/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks16

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_16_0 :
    Closed765 (decode (actCode 7 (decodeMask 71194))) := by
  have he : decode (actCode 7 (decodeMask 71194)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR111 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR111)))⟩)))))))))))))))))))))))))))))))

theorem closed_16_1 :
    Closed765 (decode (actCode 1 (decodeMask 71195))) := by
  have he : decode (actCode 1 (decodeMask 71195)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR112 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR112)⟩))))))))))))))))))))))))))))))))

theorem closed_16_2 :
    Closed765 (decode (actCode 13 (decodeMask 71233))) := by
  have he : decode (actCode 13 (decodeMask 71233)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR113 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR113))⟩))))))))))))))))))))))))))))))))

theorem closed_16_3 :
    Closed765 (decode (actCode 1 (decodeMask 71235))) := by
  have he : decode (actCode 1 (decodeMask 71235)) =
      PaddedComponents.KCT4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KCT4))))⟩))))))))))

theorem closed_16_4 :
    Closed765 (decode (actCode 3 (decodeMask 71241))) := by
  have he : decode (actCode 3 (decodeMask 71241)) =
      PaddedComponents.KCT5 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KCT5)))))⟩))))))))))

theorem closed_16_5 :
    Closed765 (decode (actCode 13 (decodeMask 71242))) := by
  have he : decode (actCode 13 (decodeMask 71242)) =
      PaddedComponents.KTH3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KTH3)))))))⟩)))))

theorem closed_16_6 :
    Closed765 (decode (actCode 3 (decodeMask 71243))) := by
  have he : decode (actCode 3 (decodeMask 71243)) =
      PaddedComponents.FM22 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM22, (by exact List.get_mem PaddedComponents.monoList ⟨21, by decide +kernel⟩), identity_perm_family PaddedComponents.FM22⟩)))))))))))))))

theorem closed_16_7 :
    Closed765 (decode (actCode 7 (decodeMask 71249))) := by
  have he : decode (actCode 7 (decodeMask 71249)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR114 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR114)))⟩))))))))))))))))))))))))))))))))

theorem closed_16_8 :
    Closed765 (decode (actCode 7 (decodeMask 71251))) := by
  have he : decode (actCode 7 (decodeMask 71251)) =
      PaddedComponents.KM5 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (identity_perm_family PaddedComponents.KM5))))⟩))))))))))))

theorem closed_16_9 :
    Closed765 (decode (actCode 7 (decodeMask 71256))) := by
  have he : decode (actCode 7 (decodeMask 71256)) =
      PaddedComponents.FM17 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM17, (by exact List.get_mem PaddedComponents.monoList ⟨16, by decide +kernel⟩), identity_perm_family PaddedComponents.FM17⟩)))))))))))))))

theorem closed_16_10 :
    Closed765 (decode (actCode 7 (decodeMask 71257))) := by
  have he : decode (actCode 7 (decodeMask 71257)) =
      PaddedComponents.FM23 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM23, (by exact List.get_mem PaddedComponents.monoList ⟨22, by decide +kernel⟩), identity_perm_family PaddedComponents.FM23⟩)))))))))))))))

theorem closed_16_11 :
    Closed765 (decode (actCode 7 (decodeMask 71258))) := by
  have he : decode (actCode 7 (decodeMask 71258)) =
      PaddedComponents.FM24 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM24, (by exact List.get_mem PaddedComponents.monoList ⟨23, by decide +kernel⟩), identity_perm_family PaddedComponents.FM24⟩)))))))))))))))

theorem closed_16_12 :
    Closed765 (decode (actCode 1 (decodeMask 71259))) := by
  have he : decode (actCode 1 (decodeMask 71259)) =
      PaddedComponents.FM30 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM30, (by exact List.get_mem PaddedComponents.monoList ⟨29, by decide +kernel⟩), identity_perm_family PaddedComponents.FM30⟩)))))))))))))))

theorem closed_16_13 :
    Closed765 (decode (actCode 10 (decodeMask 71297))) := by
  have he : decode (actCode 10 (decodeMask 71297)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL236 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨236, by decide +kernel⟩)))

theorem closed_16_14 :
    Closed765 (decode (actCode 10 (decodeMask 71300))) := by
  have he : decode (actCode 10 (decodeMask 71300)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL211 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨211, by decide +kernel⟩)))

theorem closed_16_15 :
    Closed765 (decode (actCode 4 (decodeMask 71301))) := by
  have he : decode (actCode 4 (decodeMask 71301)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL274 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨274, by decide +kernel⟩)))

theorem closed_16_16 :
    Closed765 (decode (actCode 10 (decodeMask 71304))) := by
  have he : decode (actCode 10 (decodeMask 71304)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR115 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR115)))⟩))))))))))))))))))))))))))))))))

theorem closed_16_17 :
    Closed765 (decode (actCode 5 (decodeMask 71305))) := by
  have he : decode (actCode 5 (decodeMask 71305)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR116 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR116)⟩)))))))))))))))))))))))))))))))))

theorem closed_16_18 :
    Closed765 (decode (actCode 10 (decodeMask 71308))) := by
  have he : decode (actCode 10 (decodeMask 71308)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR117 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR117))⟩)))))))))))))))))))))))))))))))))

theorem closed_16_19 :
    Closed765 (decode (actCode 4 (decodeMask 71309))) := by
  have he : decode (actCode 4 (decodeMask 71309)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR118 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR118)))⟩)))))))))))))))))))))))))))))))))

theorem closed_16_20 :
    Closed765 (decode (actCode 13 (decodeMask 71312))) := by
  have he : decode (actCode 13 (decodeMask 71312)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL177 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨177, by decide +kernel⟩)))

theorem closed_16_21 :
    Closed765 (decode (actCode 13 (decodeMask 71376))) := by
  have he : decode (actCode 13 (decodeMask 71376)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR119 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR119)))⟩)))))))))))))))))))))))))))))))))

theorem closed_16_22 :
    Closed765 (decode (actCode 4 (decodeMask 71693))) := by
  have he : decode (actCode 4 (decodeMask 71693)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL175 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨175, by decide +kernel⟩)))

theorem closed_16_23 :
    Closed765 (decode (actCode 8 (decodeMask 71817))) := by
  have he : decode (actCode 8 (decodeMask 71817)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL220 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨220, by decide +kernel⟩)))

theorem closed_16_24 :
    Closed765 (decode (actCode 4 (decodeMask 71821))) := by
  have he : decode (actCode 4 (decodeMask 71821)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL250 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨250, by decide +kernel⟩)))

theorem closed_16_25 :
    Closed765 (decode (actCode 20 (decodeMask 72193))) := by
  have he : decode (actCode 20 (decodeMask 72193)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL149 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨149, by decide +kernel⟩)))

theorem closed_16_26 :
    Closed765 (decode (actCode 4 (decodeMask 72197))) := by
  have he : decode (actCode 4 (decodeMask 72197)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL226 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨226, by decide +kernel⟩)))

theorem closed_16_27 :
    Closed765 (decode (actCode 3 (decodeMask 72201))) := by
  have he : decode (actCode 3 (decodeMask 72201)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL210 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨210, by decide +kernel⟩)))

theorem closed_16_28 :
    Closed765 (decode (actCode 5 (decodeMask 72205))) := by
  have he : decode (actCode 5 (decodeMask 72205)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL257 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨257, by decide +kernel⟩)))

theorem closed_16_29 :
    Closed765 (decode (actCode 8 (decodeMask 72321))) := by
  have he : decode (actCode 8 (decodeMask 72321)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL225 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨225, by decide +kernel⟩)))

theorem closed_16_30 :
    Closed765 (decode (actCode 8 (decodeMask 72325))) := by
  have he : decode (actCode 8 (decodeMask 72325)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL271 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨271, by decide +kernel⟩)))

theorem closed_16_31 :
    Closed765 (decode (actCode 5 (decodeMask 72329))) := by
  have he : decode (actCode 5 (decodeMask 72329)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL281 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨281, by decide +kernel⟩)))

theorem checkedMasks16_closed (m : ℕ) (hm : m ∈ checkedMasks16) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_0
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_16_1
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_16_2
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_16_3
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_16_4
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_16_5
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_16_6
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_7
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_8
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_9
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_10
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_16_11
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_16_12
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_16_13
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_16_14
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_16_15
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_16_16
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_16_17
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_16_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_16_19
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_16_20
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_16_21
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_16_22
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_16_23
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_16_24
  · refine ⟨sigma 20, ?_⟩
    rw [← decode_actCode]
    exact closed_16_25
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_16_26
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_16_27
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_16_28
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_16_29
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_16_30
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_16_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks16_closed
