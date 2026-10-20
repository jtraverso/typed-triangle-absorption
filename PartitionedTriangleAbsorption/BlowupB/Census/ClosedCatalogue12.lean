/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks12

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_12_0 :
    Closed765 (decode (actCode 10 (decodeMask 67264))) := by
  have he : decode (actCode 10 (decodeMask 67264)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL136 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨136, by decide +kernel⟩)))

theorem closed_12_1 :
    Closed765 (decode (actCode 7 (decodeMask 67280))) := by
  have he : decode (actCode 7 (decodeMask 67280)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL217 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨217, by decide +kernel⟩)))

theorem closed_12_2 :
    Closed765 (decode (actCode 12 (decodeMask 68616))) := by
  have he : decode (actCode 12 (decodeMask 68616)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL029 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨29, by decide +kernel⟩)))

theorem closed_12_3 :
    Closed765 (decode (actCode 12 (decodeMask 68617))) := by
  have he : decode (actCode 12 (decodeMask 68617)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR060 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR060)⟩)))))))))))))))))))

theorem closed_12_4 :
    Closed765 (decode (actCode 12 (decodeMask 68618))) := by
  have he : decode (actCode 12 (decodeMask 68618)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL111 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨111, by decide +kernel⟩)))

theorem closed_12_5 :
    Closed765 (decode (actCode 1 (decodeMask 68619))) := by
  have he : decode (actCode 1 (decodeMask 68619)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR061 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR061))⟩)))))))))))))))))))

theorem closed_12_6 :
    Closed765 (decode (actCode 12 (decodeMask 68620))) := by
  have he : decode (actCode 12 (decodeMask 68620)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL127 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨127, by decide +kernel⟩)))

theorem closed_12_7 :
    Closed765 (decode (actCode 4 (decodeMask 68621))) := by
  have he : decode (actCode 4 (decodeMask 68621)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR062 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR062)))⟩)))))))))))))))))))

theorem closed_12_8 :
    Closed765 (decode (actCode 12 (decodeMask 68632))) := by
  have he : decode (actCode 12 (decodeMask 68632)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL073 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨73, by decide +kernel⟩)))

theorem closed_12_9 :
    Closed765 (decode (actCode 6 (decodeMask 68633))) := by
  have he : decode (actCode 6 (decodeMask 68633)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR063 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR063)))⟩)))))))))))))))))))

theorem closed_12_10 :
    Closed765 (decode (actCode 6 (decodeMask 68634))) := by
  have he : decode (actCode 6 (decodeMask 68634)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR064 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR064)⟩))))))))))))))))))))

theorem closed_12_11 :
    Closed765 (decode (actCode 6 (decodeMask 68635))) := by
  have he : decode (actCode 6 (decodeMask 68635)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR065 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR065))⟩))))))))))))))))))))

theorem closed_12_12 :
    Closed765 (decode (actCode 8 (decodeMask 68744))) := by
  have he : decode (actCode 8 (decodeMask 68744)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL115 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨115, by decide +kernel⟩)))

theorem closed_12_13 :
    Closed765 (decode (actCode 8 (decodeMask 68745))) := by
  have he : decode (actCode 8 (decodeMask 68745)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR066 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR066)))⟩))))))))))))))))))))

theorem closed_12_14 :
    Closed765 (decode (actCode 8 (decodeMask 68748))) := by
  have he : decode (actCode 8 (decodeMask 68748)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR067 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR067)))⟩))))))))))))))))))))

theorem closed_12_15 :
    Closed765 (decode (actCode 4 (decodeMask 68749))) := by
  have he : decode (actCode 4 (decodeMask 68749)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR068 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR068)⟩)))))))))))))))))))))

theorem closed_12_16 :
    Closed765 (decode (actCode 12 (decodeMask 69121))) := by
  have he : decode (actCode 12 (decodeMask 69121)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL130 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨130, by decide +kernel⟩)))

theorem closed_12_17 :
    Closed765 (decode (actCode 12 (decodeMask 69122))) := by
  have he : decode (actCode 12 (decodeMask 69122)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL112 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨112, by decide +kernel⟩)))

theorem closed_12_18 :
    Closed765 (decode (actCode 1 (decodeMask 69123))) := by
  have he : decode (actCode 1 (decodeMask 69123)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL222 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨222, by decide +kernel⟩)))

theorem closed_12_19 :
    Closed765 (decode (actCode 12 (decodeMask 69124))) := by
  have he : decode (actCode 12 (decodeMask 69124)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL128 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨128, by decide +kernel⟩)))

theorem closed_12_20 :
    Closed765 (decode (actCode 4 (decodeMask 69125))) := by
  have he : decode (actCode 4 (decodeMask 69125)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL227 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨227, by decide +kernel⟩)))

theorem closed_12_21 :
    Closed765 (decode (actCode 12 (decodeMask 69128))) := by
  have he : decode (actCode 12 (decodeMask 69128)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR069 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR069))⟩)))))))))))))))))))))

theorem closed_12_22 :
    Closed765 (decode (actCode 3 (decodeMask 69129))) := by
  have he : decode (actCode 3 (decodeMask 69129)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR070 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR070)))⟩)))))))))))))))))))))

theorem closed_12_23 :
    Closed765 (decode (actCode 12 (decodeMask 69130))) := by
  have he : decode (actCode 12 (decodeMask 69130)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR071 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR071)))⟩)))))))))))))))))))))

theorem closed_12_24 :
    Closed765 (decode (actCode 3 (decodeMask 69131))) := by
  have he : decode (actCode 3 (decodeMask 69131)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR072 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR072)⟩))))))))))))))))))))))

theorem closed_12_25 :
    Closed765 (decode (actCode 12 (decodeMask 69132))) := by
  have he : decode (actCode 12 (decodeMask 69132)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR073 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR073))⟩))))))))))))))))))))))

theorem closed_12_26 :
    Closed765 (decode (actCode 5 (decodeMask 69133))) := by
  have he : decode (actCode 5 (decodeMask 69133)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR074 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR074)))⟩))))))))))))))))))))))

theorem closed_12_27 :
    Closed765 (decode (actCode 12 (decodeMask 69136))) := by
  have he : decode (actCode 12 (decodeMask 69136)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL074 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨74, by decide +kernel⟩)))

theorem closed_12_28 :
    Closed765 (decode (actCode 6 (decodeMask 69137))) := by
  have he : decode (actCode 6 (decodeMask 69137)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL173 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨173, by decide +kernel⟩)))

theorem closed_12_29 :
    Closed765 (decode (actCode 6 (decodeMask 69138))) := by
  have he : decode (actCode 6 (decodeMask 69138)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL159 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨159, by decide +kernel⟩)))

theorem closed_12_30 :
    Closed765 (decode (actCode 6 (decodeMask 69139))) := by
  have he : decode (actCode 6 (decodeMask 69139)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL248 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨248, by decide +kernel⟩)))

theorem closed_12_31 :
    Closed765 (decode (actCode 12 (decodeMask 69144))) := by
  have he : decode (actCode 12 (decodeMask 69144)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR075 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR075)))⟩))))))))))))))))))))))

theorem checkedMasks12_closed (m : ℕ) (hm : m ∈ checkedMasks12) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks12, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_12_0
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_12_1
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_2
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_3
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_4
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_12_5
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_6
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_12_7
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_8
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_9
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_10
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_11
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_12_12
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_12_13
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_12_14
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_12_15
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_16
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_17
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_12_18
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_19
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_12_20
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_21
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_12_22
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_23
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_12_24
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_25
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_12_26
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_27
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_28
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_29
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_12_30
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_12_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks12_closed
