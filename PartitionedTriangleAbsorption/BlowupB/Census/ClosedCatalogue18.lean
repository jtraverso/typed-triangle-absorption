/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks18

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_18_0 :
    Closed765 (decode (actCode 12 (decodeMask 77456))) := by
  have he : decode (actCode 12 (decodeMask 77456)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL245 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨245, by decide +kernel⟩)))

theorem closed_18_1 :
    Closed765 (decode (actCode 12 (decodeMask 77488))) := by
  have he : decode (actCode 12 (decodeMask 77488)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL286 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨286, by decide +kernel⟩)))

theorem closed_18_2 :
    Closed765 (decode (actCode 8 (decodeMask 77965))) := by
  have he : decode (actCode 8 (decodeMask 77965)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL246 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨246, by decide +kernel⟩)))

theorem closed_18_3 :
    Closed765 (decode (actCode 4 (decodeMask 78341))) := by
  have he : decode (actCode 4 (decodeMask 78341)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL221 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨221, by decide +kernel⟩)))

theorem closed_18_4 :
    Closed765 (decode (actCode 5 (decodeMask 78349))) := by
  have he : decode (actCode 5 (decodeMask 78349)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL256 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨256, by decide +kernel⟩)))

theorem closed_18_5 :
    Closed765 (decode (actCode 8 (decodeMask 78469))) := by
  have he : decode (actCode 8 (decodeMask 78469)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL249 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨249, by decide +kernel⟩)))

theorem closed_18_6 :
    Closed765 (decode (actCode 4 (decodeMask 78477))) := by
  have he : decode (actCode 4 (decodeMask 78477)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL287 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨287, by decide +kernel⟩)))

theorem closed_18_7 :
    Closed765 (decode (actCode 8 (decodeMask 78985))) := by
  have he : decode (actCode 8 (decodeMask 78985)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR135 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR135)))⟩)))))))))))))))))))))))))))))))))))))

theorem closed_18_8 :
    Closed765 (decode (actCode 8 (decodeMask 78988))) := by
  have he : decode (actCode 8 (decodeMask 78988)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR136 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR136)⟩))))))))))))))))))))))))))))))))))))))

theorem closed_18_9 :
    Closed765 (decode (actCode 8 (decodeMask 78989))) := by
  have he : decode (actCode 8 (decodeMask 78989)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR137 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR137))⟩))))))))))))))))))))))))))))))))))))))

theorem closed_18_10 :
    Closed765 (decode (actCode 19 (decodeMask 79361))) := by
  have he : decode (actCode 19 (decodeMask 79361)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL230 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨230, by decide +kernel⟩)))

theorem closed_18_11 :
    Closed765 (decode (actCode 14 (decodeMask 79365))) := by
  have he : decode (actCode 14 (decodeMask 79365)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL283 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨283, by decide +kernel⟩)))

theorem closed_18_12 :
    Closed765 (decode (actCode 3 (decodeMask 79369))) := by
  have he : decode (actCode 3 (decodeMask 79369)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR138 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR138)))⟩))))))))))))))))))))))))))))))))))))))

theorem closed_18_13 :
    Closed765 (decode (actCode 14 (decodeMask 79372))) := by
  have he : decode (actCode 14 (decodeMask 79372)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR139 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR139)))⟩))))))))))))))))))))))))))))))))))))))

theorem closed_18_14 :
    Closed765 (decode (actCode 5 (decodeMask 79373))) := by
  have he : decode (actCode 5 (decodeMask 79373)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR140 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR140)⟩)))))))))))))))))))))))))))))))))))))))

theorem closed_18_15 :
    Closed765 (decode (actCode 14 (decodeMask 79489))) := by
  have he : decode (actCode 14 (decodeMask 79489)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL261 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨261, by decide +kernel⟩)))

theorem closed_18_16 :
    Closed765 (decode (actCode 8 (decodeMask 79493))) := by
  have he : decode (actCode 8 (decodeMask 79493)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL292 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨292, by decide +kernel⟩)))

theorem closed_18_17 :
    Closed765 (decode (actCode 8 (decodeMask 79497))) := by
  have he : decode (actCode 8 (decodeMask 79497)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR141 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR141))⟩)))))))))))))))))))))))))))))))))))))))

theorem closed_18_18 :
    Closed765 (decode (actCode 8 (decodeMask 79500))) := by
  have he : decode (actCode 8 (decodeMask 79500)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR142 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR142)))⟩)))))))))))))))))))))))))))))))))))))))

theorem closed_18_19 :
    Closed765 (decode (actCode 4 (decodeMask 79501))) := by
  have he : decode (actCode 4 (decodeMask 79501)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR143 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR143)))⟩)))))))))))))))))))))))))))))))))))))))

theorem closed_18_20 :
    Closed765 (decode (actCode 8 (decodeMask 80013))) := by
  have he : decode (actCode 8 (decodeMask 80013)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR510 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR510)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_18_21 :
    Closed765 (decode (actCode 20 (decodeMask 80385))) := by
  have he : decode (actCode 20 (decodeMask 80385)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL208 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨208, by decide +kernel⟩)))

theorem closed_18_22 :
    Closed765 (decode (actCode 14 (decodeMask 80389))) := by
  have he : decode (actCode 14 (decodeMask 80389)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL278 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨278, by decide +kernel⟩)))

theorem closed_18_23 :
    Closed765 (decode (actCode 20 (decodeMask 80393))) := by
  have he : decode (actCode 20 (decodeMask 80393)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR144 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR144)⟩))))))))))))))))))))))))))))))))))))))))

theorem closed_18_24 :
    Closed765 (decode (actCode 5 (decodeMask 80397))) := by
  have he : decode (actCode 5 (decodeMask 80397)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR145 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR145))⟩))))))))))))))))))))))))))))))))))))))))

theorem closed_18_25 :
    Closed765 (decode (actCode 14 (decodeMask 80513))) := by
  have he : decode (actCode 14 (decodeMask 80513)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL254 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨254, by decide +kernel⟩)))

theorem closed_18_26 :
    Closed765 (decode (actCode 8 (decodeMask 80517))) := by
  have he : decode (actCode 8 (decodeMask 80517)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL289 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨289, by decide +kernel⟩)))

theorem closed_18_27 :
    Closed765 (decode (actCode 14 (decodeMask 80521))) := by
  have he : decode (actCode 14 (decodeMask 80521)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR146 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR146)))⟩))))))))))))))))))))))))))))))))))))))))

theorem closed_18_28 :
    Closed765 (decode (actCode 8 (decodeMask 80525))) := by
  have he : decode (actCode 8 (decodeMask 80525)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR511 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR511)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_18_29 :
    Closed765 (decode (actCode 8 (decodeMask 81037))) := by
  have he : decode (actCode 8 (decodeMask 81037)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR512 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR512)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_18_30 :
    Closed765 (decode (actCode 18 (decodeMask 81409))) := by
  have he : decode (actCode 18 (decodeMask 81409)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL252 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨252, by decide +kernel⟩)))

theorem closed_18_31 :
    Closed765 (decode (actCode 18 (decodeMask 81413))) := by
  have he : decode (actCode 18 (decodeMask 81413)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL294 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨294, by decide +kernel⟩)))

theorem checkedMasks18_closed (m : ℕ) (hm : m ∈ checkedMasks18) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks18, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_18_0
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_18_1
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_2
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_18_3
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_18_4
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_5
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_18_6
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_7
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_8
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_9
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_18_10
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_11
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_18_12
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_13
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_18_14
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_15
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_16
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_17
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_18_19
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_20
  · refine ⟨sigma 20, ?_⟩
    rw [← decode_actCode]
    exact closed_18_21
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_22
  · refine ⟨sigma 20, ?_⟩
    rw [← decode_actCode]
    exact closed_18_23
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_18_24
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_25
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_26
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_18_27
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_28
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_18_29
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_18_30
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_18_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks18_closed
