/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks21

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_21_0 :
    Closed765 (decode (actCode 13 (decodeMask 104080))) := by
  have he : decode (actCode 13 (decodeMask 104080)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR180 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR180)⟩)))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_1 :
    Closed765 (decode (actCode 13 (decodeMask 104144))) := by
  have he : decode (actCode 13 (decodeMask 104144)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR181 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR181))⟩)))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_2 :
    Closed765 (decode (actCode 5 (decodeMask 104973))) := by
  have he : decode (actCode 5 (decodeMask 104973)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR515 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR515)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_3 :
    Closed765 (decode (actCode 4 (decodeMask 105093))) := by
  have he : decode (actCode 4 (decodeMask 105093)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR182 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR182)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_4 :
    Closed765 (decode (actCode 4 (decodeMask 105101))) := by
  have he : decode (actCode 4 (decodeMask 105101)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR516 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR516)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_5 :
    Closed765 (decode (actCode 5 (decodeMask 105997))) := by
  have he : decode (actCode 5 (decodeMask 105997)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR517 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR517))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_6 :
    Closed765 (decode (actCode 19 (decodeMask 106113))) := by
  have he : decode (actCode 19 (decodeMask 106113)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR183 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR183)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_7 :
    Closed765 (decode (actCode 19 (decodeMask 106117))) := by
  have he : decode (actCode 19 (decodeMask 106117)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR184 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR184)⟩))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_8 :
    Closed765 (decode (actCode 19 (decodeMask 106121))) := by
  have he : decode (actCode 19 (decodeMask 106121)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR239 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR239)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_9 :
    Closed765 (decode (actCode 19 (decodeMask 106124))) := by
  have he : decode (actCode 19 (decodeMask 106124)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR518 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR518)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_10 :
    Closed765 (decode (actCode 4 (decodeMask 106125))) := by
  have he : decode (actCode 4 (decodeMask 106125)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR519 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR519)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_11 :
    Closed765 (decode (actCode 8 (decodeMask 108161))) := by
  have he : decode (actCode 8 (decodeMask 108161)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL263 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨263, by decide +kernel⟩)))

theorem closed_21_12 :
    Closed765 (decode (actCode 8 (decodeMask 108165))) := by
  have he : decode (actCode 8 (decodeMask 108165)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL293 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨293, by decide +kernel⟩)))

theorem closed_21_13 :
    Closed765 (decode (actCode 8 (decodeMask 108169))) := by
  have he : decode (actCode 8 (decodeMask 108169)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR185 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR185))⟩))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_14 :
    Closed765 (decode (actCode 4 (decodeMask 108173))) := by
  have he : decode (actCode 4 (decodeMask 108173)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR520 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR520)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_15 :
    Closed765 (decode (actCode 8 (decodeMask 110213))) := by
  have he : decode (actCode 8 (decodeMask 110213)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL300 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨300, by decide +kernel⟩)))

theorem closed_21_16 :
    Closed765 (decode (actCode 14 (decodeMask 110217))) := by
  have he : decode (actCode 14 (decodeMask 110217)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR186 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR186)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_17 :
    Closed765 (decode (actCode 8 (decodeMask 110221))) := by
  have he : decode (actCode 8 (decodeMask 110221)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR521 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR521))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_18 :
    Closed765 (decode (actCode 8 (decodeMask 112265))) := by
  have he : decode (actCode 8 (decodeMask 112265)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR187 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR187)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_19 :
    Closed765 (decode (actCode 4 (decodeMask 112269))) := by
  have he : decode (actCode 4 (decodeMask 112269)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR522 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR522)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_20 :
    Closed765 (decode (actCode 4 (decodeMask 113293))) := by
  have he : decode (actCode 4 (decodeMask 113293)) =
      PaddedFbit.Fbit111 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedFbit.Fbit111)))⟩)))))))))))))))))))

theorem closed_21_21 :
    Closed765 (decode (actCode 8 (decodeMask 114317))) := by
  have he : decode (actCode 8 (decodeMask 114317)) =
      PaddedFbit.Fbit111222 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedFbit.Fbit111222))))⟩)))))))))))))))))))

theorem closed_21_22 :
    Closed765 (decode (actCode 3 (decodeMask 201737))) := by
  have he : decode (actCode 3 (decodeMask 201737)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR188 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR188)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_23 :
    Closed765 (decode (actCode 1 (decodeMask 201739))) := by
  have he : decode (actCode 1 (decodeMask 201739)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR189 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR189))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_24 :
    Closed765 (decode (actCode 1 (decodeMask 201755))) := by
  have he : decode (actCode 1 (decodeMask 201755)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR190 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR190)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_25 :
    Closed765 (decode (actCode 3 (decodeMask 201801))) := by
  have he : decode (actCode 3 (decodeMask 201801)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR191 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR191)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_26 :
    Closed765 (decode (actCode 1 (decodeMask 201803))) := by
  have he : decode (actCode 1 (decodeMask 201803)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR192 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR192)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_27 :
    Closed765 (decode (actCode 1 (decodeMask 201819))) := by
  have he : decode (actCode 1 (decodeMask 201819)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR193 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR193))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_28 :
    Closed765 (decode (actCode 0 (decodeMask 590849))) := by
  have he : decode (actCode 0 (decodeMask 590849)) =
      PaddedComponents.KE1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KE1)⟩))))))

theorem closed_21_29 :
    Closed765 (decode (actCode 0 (decodeMask 590851))) := by
  have he : decode (actCode 0 (decodeMask 590851)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR194 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR194)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_30 :
    Closed765 (decode (actCode 0 (decodeMask 590855))) := by
  have he : decode (actCode 0 (decodeMask 590855)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR195 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR195)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_21_31 :
    Closed765 (decode (actCode 0 (decodeMask 590867))) := by
  have he : decode (actCode 0 (decodeMask 590867)) =
      PaddedComponents.KE4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PaddedComponents.KE4)))⟩))))))

theorem checkedMasks21_closed (m : ℕ) (hm : m ∈ checkedMasks21) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks21, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_21_0
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_21_1
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_21_2
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_3
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_4
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_21_5
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_21_6
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_21_7
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_21_8
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_21_9
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_10
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_11
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_12
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_13
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_14
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_15
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_21_16
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_17
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_19
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_21_20
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_21_21
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_21_22
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_21_23
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_21_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_21_25
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_21_26
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_21_27
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_21_28
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_21_29
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_21_30
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_21_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks21_closed
