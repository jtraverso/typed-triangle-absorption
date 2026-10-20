/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks19

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_19_0 :
    Closed765 (decode (actCode 18 (decodeMask 81417))) := by
  have he : decode (actCode 18 (decodeMask 81417)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR147 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR147)))⟩))))))))))))))))))))))))))))))))))))))))

theorem closed_19_1 :
    Closed765 (decode (actCode 18 (decodeMask 81420))) := by
  have he : decode (actCode 18 (decodeMask 81420)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR148 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR148)⟩)))))))))))))))))))))))))))))))))))))))))

theorem closed_19_2 :
    Closed765 (decode (actCode 18 (decodeMask 81421))) := by
  have he : decode (actCode 18 (decodeMask 81421)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR149 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR149))⟩)))))))))))))))))))))))))))))))))))))))))

theorem closed_19_3 :
    Closed765 (decode (actCode 14 (decodeMask 81537))) := by
  have he : decode (actCode 14 (decodeMask 81537)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL291 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨291, by decide +kernel⟩)))

theorem closed_19_4 :
    Closed765 (decode (actCode 14 (decodeMask 81541))) := by
  have he : decode (actCode 14 (decodeMask 81541)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL299 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨299, by decide +kernel⟩)))

theorem closed_19_5 :
    Closed765 (decode (actCode 14 (decodeMask 81544))) := by
  have he : decode (actCode 14 (decodeMask 81544)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR150 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR150)))⟩)))))))))))))))))))))))))))))))))))))))))

theorem closed_19_6 :
    Closed765 (decode (actCode 14 (decodeMask 81545))) := by
  have he : decode (actCode 14 (decodeMask 81545)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR151 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR151)))⟩)))))))))))))))))))))))))))))))))))))))))

theorem closed_19_7 :
    Closed765 (decode (actCode 14 (decodeMask 81548))) := by
  have he : decode (actCode 14 (decodeMask 81548)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR513 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR513))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_8 :
    Closed765 (decode (actCode 8 (decodeMask 81549))) := by
  have he : decode (actCode 8 (decodeMask 81549)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR514 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR514)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_9 :
    Closed765 (decode (actCode 3 (decodeMask 99841))) := by
  have he : decode (actCode 3 (decodeMask 99841)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL148 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨148, by decide +kernel⟩)))

theorem closed_19_10 :
    Closed765 (decode (actCode 1 (decodeMask 99843))) := by
  have he : decode (actCode 1 (decodeMask 99843)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL223 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨223, by decide +kernel⟩)))

theorem closed_19_11 :
    Closed765 (decode (actCode 4 (decodeMask 99845))) := by
  have he : decode (actCode 4 (decodeMask 99845)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL228 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨228, by decide +kernel⟩)))

theorem closed_19_12 :
    Closed765 (decode (actCode 3 (decodeMask 99849))) := by
  have he : decode (actCode 3 (decodeMask 99849)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR152 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR152)⟩))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_13 :
    Closed765 (decode (actCode 7 (decodeMask 99850))) := by
  have he : decode (actCode 7 (decodeMask 99850)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR153 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR153))⟩))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_14 :
    Closed765 (decode (actCode 3 (decodeMask 99851))) := by
  have he : decode (actCode 3 (decodeMask 99851)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR154 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR154)))⟩))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_15 :
    Closed765 (decode (actCode 10 (decodeMask 99852))) := by
  have he : decode (actCode 10 (decodeMask 99852)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR155 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR155)))⟩))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_16 :
    Closed765 (decode (actCode 5 (decodeMask 99853))) := by
  have he : decode (actCode 5 (decodeMask 99853)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR156 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR156)⟩)))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_17 :
    Closed765 (decode (actCode 1 (decodeMask 99859))) := by
  have he : decode (actCode 1 (decodeMask 99859)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL269 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨269, by decide +kernel⟩)))

theorem closed_19_18 :
    Closed765 (decode (actCode 3 (decodeMask 99865))) := by
  have he : decode (actCode 3 (decodeMask 99865)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR157 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR157))⟩)))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_19 :
    Closed765 (decode (actCode 7 (decodeMask 99866))) := by
  have he : decode (actCode 7 (decodeMask 99866)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR158 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR158)))⟩)))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_20 :
    Closed765 (decode (actCode 1 (decodeMask 99867))) := by
  have he : decode (actCode 1 (decodeMask 99867)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR159 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR159)))⟩)))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_21 :
    Closed765 (decode (actCode 3 (decodeMask 99905))) := by
  have he : decode (actCode 3 (decodeMask 99905)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR160 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR160)⟩))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_22 :
    Closed765 (decode (actCode 1 (decodeMask 99907))) := by
  have he : decode (actCode 1 (decodeMask 99907)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR161 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR161))⟩))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_23 :
    Closed765 (decode (actCode 3 (decodeMask 99913))) := by
  have he : decode (actCode 3 (decodeMask 99913)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR162 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR162)))⟩))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_24 :
    Closed765 (decode (actCode 7 (decodeMask 99914))) := by
  have he : decode (actCode 7 (decodeMask 99914)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR163 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR163)))⟩))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_25 :
    Closed765 (decode (actCode 3 (decodeMask 99915))) := by
  have he : decode (actCode 3 (decodeMask 99915)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR164 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR164)⟩)))))))))))))))))))))))))))))))))))))))))))))

theorem closed_19_26 :
    Closed765 (decode (actCode 1 (decodeMask 99923))) := by
  have he : decode (actCode 1 (decodeMask 99923)) =
      PaddedComponents.KTH4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (identity_perm_family PaddedComponents.KTH4)))))))⟩)))))

theorem closed_19_27 :
    Closed765 (decode (actCode 3 (decodeMask 99929))) := by
  have he : decode (actCode 3 (decodeMask 99929)) =
      PaddedComponents.FM25 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM25, (by exact List.get_mem PaddedComponents.monoList ⟨24, by decide +kernel⟩), identity_perm_family PaddedComponents.FM25⟩)))))))))))))))

theorem closed_19_28 :
    Closed765 (decode (actCode 7 (decodeMask 99930))) := by
  have he : decode (actCode 7 (decodeMask 99930)) =
      PaddedComponents.FM26 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM26, (by exact List.get_mem PaddedComponents.monoList ⟨25, by decide +kernel⟩), identity_perm_family PaddedComponents.FM26⟩)))))))))))))))

theorem closed_19_29 :
    Closed765 (decode (actCode 1 (decodeMask 99931))) := by
  have he : decode (actCode 1 (decodeMask 99931)) =
      PaddedComponents.FM31 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM31, (by exact List.get_mem PaddedComponents.monoList ⟨30, by decide +kernel⟩), identity_perm_family PaddedComponents.FM31⟩)))))))))))))))

theorem closed_19_30 :
    Closed765 (decode (actCode 10 (decodeMask 99969))) := by
  have he : decode (actCode 10 (decodeMask 99969)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL235 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨235, by decide +kernel⟩)))

theorem closed_19_31 :
    Closed765 (decode (actCode 4 (decodeMask 99973))) := by
  have he : decode (actCode 4 (decodeMask 99973)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL273 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨273, by decide +kernel⟩)))

theorem checkedMasks19_closed (m : ℕ) (hm : m ∈ checkedMasks19) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks19, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_19_0
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_19_1
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_19_2
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_19_3
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_19_4
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_19_5
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_19_6
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_19_7
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_19_8
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_9
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_10
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_19_11
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_12
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_19_13
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_14
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_19_15
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_19_16
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_17
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_18
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_19_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_20
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_21
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_22
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_23
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_19_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_25
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_26
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_19_27
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_19_28
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_19_29
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_19_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_19_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks19_closed
