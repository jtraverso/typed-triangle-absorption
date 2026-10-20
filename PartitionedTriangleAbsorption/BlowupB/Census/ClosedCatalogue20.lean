/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks20

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_20_0 :
    Closed765 (decode (actCode 5 (decodeMask 99977))) := by
  have he : decode (actCode 5 (decodeMask 99977)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR165 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR165))⟩)))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_1 :
    Closed765 (decode (actCode 10 (decodeMask 99980))) := by
  have he : decode (actCode 10 (decodeMask 99980)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR166 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR166)))⟩)))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_2 :
    Closed765 (decode (actCode 4 (decodeMask 99981))) := by
  have he : decode (actCode 4 (decodeMask 99981)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR167 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR167)))⟩)))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_3 :
    Closed765 (decode (actCode 7 (decodeMask 99984))) := by
  have he : decode (actCode 7 (decodeMask 99984)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL233 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨233, by decide +kernel⟩)))

theorem closed_20_4 :
    Closed765 (decode (actCode 7 (decodeMask 100048))) := by
  have he : decode (actCode 7 (decodeMask 100048)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR168 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR168)⟩))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_5 :
    Closed765 (decode (actCode 4 (decodeMask 101893))) := by
  have he : decode (actCode 4 (decodeMask 101893)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL285 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨285, by decide +kernel⟩)))

theorem closed_20_6 :
    Closed765 (decode (actCode 3 (decodeMask 101897))) := by
  have he : decode (actCode 3 (decodeMask 101897)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR169 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR169))⟩))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_7 :
    Closed765 (decode (actCode 18 (decodeMask 101900))) := by
  have he : decode (actCode 18 (decodeMask 101900)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR170 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR170)))⟩))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_8 :
    Closed765 (decode (actCode 5 (decodeMask 101901))) := by
  have he : decode (actCode 5 (decodeMask 101901)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR171 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR171)))⟩))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_9 :
    Closed765 (decode (actCode 18 (decodeMask 102017))) := by
  have he : decode (actCode 18 (decodeMask 102017)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL284 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨284, by decide +kernel⟩)))

theorem closed_20_10 :
    Closed765 (decode (actCode 8 (decodeMask 102021))) := by
  have he : decode (actCode 8 (decodeMask 102021)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL297 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨297, by decide +kernel⟩)))

theorem closed_20_11 :
    Closed765 (decode (actCode 5 (decodeMask 102025))) := by
  have he : decode (actCode 5 (decodeMask 102025)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR172 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR172)⟩)))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_12 :
    Closed765 (decode (actCode 8 (decodeMask 102028))) := by
  have he : decode (actCode 8 (decodeMask 102028)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR173 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR173))⟩)))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_13 :
    Closed765 (decode (actCode 4 (decodeMask 102029))) := by
  have he : decode (actCode 4 (decodeMask 102029)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR174 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR174)))⟩)))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_14 :
    Closed765 (decode (actCode 1 (decodeMask 102938))) := by
  have he : decode (actCode 1 (decodeMask 102938)) =
      PaddedComponents.KQ10 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ10))))))))))⟩))))

theorem closed_20_15 :
    Closed765 (decode (actCode 1 (decodeMask 102939))) := by
  have he : decode (actCode 1 (decodeMask 102939)) =
      PaddedComponents.KTB1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KTB1))⟩)))))

theorem closed_20_16 :
    Closed765 (decode (actCode 8 (decodeMask 103002))) := by
  have he : decode (actCode 8 (decodeMask 103002)) =
      PaddedComponents.FM27 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM27, (by exact List.get_mem PaddedComponents.monoList ⟨26, by decide +kernel⟩), identity_perm_family PaddedComponents.FM27⟩)))))))))))))))

theorem closed_20_17 :
    Closed765 (decode (actCode 1 (decodeMask 103003))) := by
  have he : decode (actCode 1 (decodeMask 103003)) =
      PaddedComponents.FM32 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM32, (by exact List.get_mem PaddedComponents.monoList ⟨31, by decide +kernel⟩), identity_perm_family PaddedComponents.FM32⟩)))))))))))))))

theorem closed_20_18 :
    Closed765 (decode (actCode 8 (decodeMask 103056))) := by
  have he : decode (actCode 8 (decodeMask 103056)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR175 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR175)))⟩)))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_19 :
    Closed765 (decode (actCode 8 (decodeMask 103120))) := by
  have he : decode (actCode 8 (decodeMask 103120)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR176 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR176)⟩))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_20 :
    Closed765 (decode (actCode 3 (decodeMask 103945))) := by
  have he : decode (actCode 3 (decodeMask 103945)) =
      PaddedComponents.FM18 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM18, (by exact List.get_mem PaddedComponents.monoList ⟨17, by decide +kernel⟩), identity_perm_family PaddedComponents.FM18⟩)))))))))))))))

theorem closed_20_21 :
    Closed765 (decode (actCode 3 (decodeMask 103947))) := by
  have he : decode (actCode 3 (decodeMask 103947)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR237 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR237)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_22 :
    Closed765 (decode (actCode 5 (decodeMask 103949))) := by
  have he : decode (actCode 5 (decodeMask 103949)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR238 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR238))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_23 :
    Closed765 (decode (actCode 1 (decodeMask 103963))) := by
  have he : decode (actCode 1 (decodeMask 103963)) =
      PaddedComponents.KTB2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KTB2)))⟩)))))

theorem closed_20_24 :
    Closed765 (decode (actCode 3 (decodeMask 104009))) := by
  have he : decode (actCode 3 (decodeMask 104009)) =
      PaddedComponents.FM28 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM28, (by exact List.get_mem PaddedComponents.monoList ⟨27, by decide +kernel⟩), identity_perm_family PaddedComponents.FM28⟩)))))))))))))))

theorem closed_20_25 :
    Closed765 (decode (actCode 3 (decodeMask 104011))) := by
  have he : decode (actCode 3 (decodeMask 104011)) =
      PaddedComponents.FM33 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM33, (by exact List.get_mem PaddedComponents.monoList ⟨32, by decide +kernel⟩), identity_perm_family PaddedComponents.FM33⟩)))))))))))))))

theorem closed_20_26 :
    Closed765 (decode (actCode 1 (decodeMask 104027))) := by
  have he : decode (actCode 1 (decodeMask 104027)) =
      PaddedComponents.FM37 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM37, (by exact List.get_mem PaddedComponents.monoList ⟨36, by decide +kernel⟩), identity_perm_family PaddedComponents.FM37⟩)))))))))))))))

theorem closed_20_27 :
    Closed765 (decode (actCode 13 (decodeMask 104065))) := by
  have he : decode (actCode 13 (decodeMask 104065)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR177 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR177))⟩))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_28 :
    Closed765 (decode (actCode 4 (decodeMask 104069))) := by
  have he : decode (actCode 4 (decodeMask 104069)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR178 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR178)))⟩))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_29 :
    Closed765 (decode (actCode 5 (decodeMask 104073))) := by
  have he : decode (actCode 5 (decodeMask 104073)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR179 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR179)))⟩))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_20_30 :
    Closed765 (decode (actCode 10 (decodeMask 104076))) := by
  have he : decode (actCode 10 (decodeMask 104076)) =
      PaddedNoCommon.NC11 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC11)))))))))))⟩))))))))))))))))))

theorem closed_20_31 :
    Closed765 (decode (actCode 4 (decodeMask 104077))) := by
  have he : decode (actCode 4 (decodeMask 104077)) =
      PaddedNoCommon.NC13 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC13)))))))))))))⟩))))))))))))))))))

theorem checkedMasks20_closed (m : ℕ) (hm : m ∈ checkedMasks20) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks20, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_20_0
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_20_1
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_20_2
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_20_3
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_20_4
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_20_5
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_20_6
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_20_7
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_20_8
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_20_9
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_20_10
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_20_11
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_20_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_20_13
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_20_14
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_20_15
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_20_16
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_20_17
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_20_18
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_20_19
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_20_20
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_20_21
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_20_22
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_20_23
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_20_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_20_25
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_20_26
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_20_27
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_20_28
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_20_29
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_20_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_20_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks20_closed
