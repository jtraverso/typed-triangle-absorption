/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks15

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_15_0 :
    Closed765 (decode (actCode 1 (decodeMask 70747))) := by
  have he : decode (actCode 1 (decodeMask 70747)) =
      PaddedComponents.FM21 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM21, (by exact List.get_mem PaddedComponents.monoList ⟨20, by decide +kernel⟩), identity_perm_family PaddedComponents.FM21⟩)))))))))))))))

theorem closed_15_1 :
    Closed765 (decode (actCode 2 (decodeMask 70789))) := by
  have he : decode (actCode 2 (decodeMask 70789)) =
      PaddedComponents.FB4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.FB4))))⟩))))))))))))))))

theorem closed_15_2 :
    Closed765 (decode (actCode 2 (decodeMask 70791))) := by
  have he : decode (actCode 2 (decodeMask 70791)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR093 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR093))⟩)))))))))))))))))))))))))))

theorem closed_15_3 :
    Closed765 (decode (actCode 10 (decodeMask 70792))) := by
  have he : decode (actCode 10 (decodeMask 70792)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL134 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨134, by decide +kernel⟩)))

theorem closed_15_4 :
    Closed765 (decode (actCode 5 (decodeMask 70793))) := by
  have he : decode (actCode 5 (decodeMask 70793)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR094 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR094)))⟩)))))))))))))))))))))))))))

theorem closed_15_5 :
    Closed765 (decode (actCode 10 (decodeMask 70796))) := by
  have he : decode (actCode 10 (decodeMask 70796)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR095 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR095)))⟩)))))))))))))))))))))))))))

theorem closed_15_6 :
    Closed765 (decode (actCode 4 (decodeMask 70797))) := by
  have he : decode (actCode 4 (decodeMask 70797)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR096 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR096)⟩))))))))))))))))))))))))))))

theorem closed_15_7 :
    Closed765 (decode (actCode 7 (decodeMask 70805))) := by
  have he : decode (actCode 7 (decodeMask 70805)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR097 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR097))⟩))))))))))))))))))))))))))))

theorem closed_15_8 :
    Closed765 (decode (actCode 0 (decodeMask 70807))) := by
  have he : decode (actCode 0 (decodeMask 70807)) =
      PaddedNoCommon.NC9 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC9)))))))))⟩))))))))))))))))))

theorem closed_15_9 :
    Closed765 (decode (actCode 13 (decodeMask 70913))) := by
  have he : decode (actCode 13 (decodeMask 70913)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case15.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨15, rfl⟩

theorem closed_15_10 :
    Closed765 (decode (actCode 4 (decodeMask 70917))) := by
  have he : decode (actCode 4 (decodeMask 70917)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL216 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨216, by decide +kernel⟩)))

theorem closed_15_11 :
    Closed765 (decode (actCode 5 (decodeMask 70921))) := by
  have he : decode (actCode 5 (decodeMask 70921)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL218 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨218, by decide +kernel⟩)))

theorem closed_15_12 :
    Closed765 (decode (actCode 13 (decodeMask 70924))) := by
  have he : decode (actCode 13 (decodeMask 70924)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR098 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR098)))⟩))))))))))))))))))))))))))))

theorem closed_15_13 :
    Closed765 (decode (actCode 4 (decodeMask 70925))) := by
  have he : decode (actCode 4 (decodeMask 70925)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR099 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR099)))⟩))))))))))))))))))))))))))))

theorem closed_15_14 :
    Closed765 (decode (actCode 4 (decodeMask 71045))) := by
  have he : decode (actCode 4 (decodeMask 71045)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL268 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨268, by decide +kernel⟩)))

theorem closed_15_15 :
    Closed765 (decode (actCode 10 (decodeMask 71048))) := by
  have he : decode (actCode 10 (decodeMask 71048)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR100 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR100)⟩)))))))))))))))))))))))))))))

theorem closed_15_16 :
    Closed765 (decode (actCode 5 (decodeMask 71049))) := by
  have he : decode (actCode 5 (decodeMask 71049)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR101 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR101))⟩)))))))))))))))))))))))))))))

theorem closed_15_17 :
    Closed765 (decode (actCode 10 (decodeMask 71052))) := by
  have he : decode (actCode 10 (decodeMask 71052)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR102 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR102)))⟩)))))))))))))))))))))))))))))

theorem closed_15_18 :
    Closed765 (decode (actCode 4 (decodeMask 71053))) := by
  have he : decode (actCode 4 (decodeMask 71053)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR103 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR103)))⟩)))))))))))))))))))))))))))))

theorem closed_15_19 :
    Closed765 (decode (actCode 13 (decodeMask 71169))) := by
  have he : decode (actCode 13 (decodeMask 71169)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL132 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨132, by decide +kernel⟩)))

theorem closed_15_20 :
    Closed765 (decode (actCode 1 (decodeMask 71171))) := by
  have he : decode (actCode 1 (decodeMask 71171)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL219 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨219, by decide +kernel⟩)))

theorem closed_15_21 :
    Closed765 (decode (actCode 13 (decodeMask 71172))) := by
  have he : decode (actCode 13 (decodeMask 71172)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL133 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨133, by decide +kernel⟩)))

theorem closed_15_22 :
    Closed765 (decode (actCode 4 (decodeMask 71173))) := by
  have he : decode (actCode 4 (decodeMask 71173)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL229 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨229, by decide +kernel⟩)))

theorem closed_15_23 :
    Closed765 (decode (actCode 3 (decodeMask 71177))) := by
  have he : decode (actCode 3 (decodeMask 71177)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR104 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR104)⟩))))))))))))))))))))))))))))))

theorem closed_15_24 :
    Closed765 (decode (actCode 13 (decodeMask 71178))) := by
  have he : decode (actCode 13 (decodeMask 71178)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR105 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR105))⟩))))))))))))))))))))))))))))))

theorem closed_15_25 :
    Closed765 (decode (actCode 3 (decodeMask 71179))) := by
  have he : decode (actCode 3 (decodeMask 71179)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR106 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR106)))⟩))))))))))))))))))))))))))))))

theorem closed_15_26 :
    Closed765 (decode (actCode 13 (decodeMask 71180))) := by
  have he : decode (actCode 13 (decodeMask 71180)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR107 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR107)))⟩))))))))))))))))))))))))))))))

theorem closed_15_27 :
    Closed765 (decode (actCode 5 (decodeMask 71181))) := by
  have he : decode (actCode 5 (decodeMask 71181)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR108 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR108)⟩)))))))))))))))))))))))))))))))

theorem closed_15_28 :
    Closed765 (decode (actCode 7 (decodeMask 71185))) := by
  have he : decode (actCode 7 (decodeMask 71185)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL172 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨172, by decide +kernel⟩)))

theorem closed_15_29 :
    Closed765 (decode (actCode 7 (decodeMask 71187))) := by
  have he : decode (actCode 7 (decodeMask 71187)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL247 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨247, by decide +kernel⟩)))

theorem closed_15_30 :
    Closed765 (decode (actCode 7 (decodeMask 71192))) := by
  have he : decode (actCode 7 (decodeMask 71192)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR109 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR109))⟩)))))))))))))))))))))))))))))))

theorem closed_15_31 :
    Closed765 (decode (actCode 7 (decodeMask 71193))) := by
  have he : decode (actCode 7 (decodeMask 71193)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR110 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR110)))⟩)))))))))))))))))))))))))))))))

theorem checkedMasks15_closed (m : ℕ) (hm : m ∈ checkedMasks15) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks15, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_15_0
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_15_1
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_15_2
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_15_3
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_15_4
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_15_5
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_6
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_15_7
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_15_8
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_9
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_10
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_15_11
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_13
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_14
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_15_15
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_15_16
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_15_17
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_18
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_15_20
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_21
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_15_22
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_15_23
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_15_25
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_15_26
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_15_27
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_15_28
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_15_29
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_15_30
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_15_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks15_closed
