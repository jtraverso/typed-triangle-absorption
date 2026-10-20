/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks22

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_22_0 :
    Closed765 (decode (actCode 2 (decodeMask 590869))) := by
  have he : decode (actCode 2 (decodeMask 590869)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR196 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR196)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_1 :
    Closed765 (decode (actCode 0 (decodeMask 590871))) := by
  have he : decode (actCode 0 (decodeMask 590871)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR197 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR197))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_2 :
    Closed765 (decode (actCode 0 (decodeMask 590881))) := by
  have he : decode (actCode 0 (decodeMask 590881)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case16.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨16, rfl⟩

theorem closed_22_3 :
    Closed765 (decode (actCode 0 (decodeMask 590883))) := by
  have he : decode (actCode 0 (decodeMask 590883)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL215 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨215, by decide +kernel⟩)))

theorem closed_22_4 :
    Closed765 (decode (actCode 0 (decodeMask 590887))) := by
  have he : decode (actCode 0 (decodeMask 590887)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR198 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR198)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_5 :
    Closed765 (decode (actCode 0 (decodeMask 590899))) := by
  have he : decode (actCode 0 (decodeMask 590899)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL267 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨267, by decide +kernel⟩)))

theorem closed_22_6 :
    Closed765 (decode (actCode 2 (decodeMask 590901))) := by
  have he : decode (actCode 2 (decodeMask 590901)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR199 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR199)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_7 :
    Closed765 (decode (actCode 0 (decodeMask 590903))) := by
  have he : decode (actCode 0 (decodeMask 590903)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR200 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR200)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_8 :
    Closed765 (decode (actCode 6 (decodeMask 590993))) := by
  have he : decode (actCode 6 (decodeMask 590993)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR201 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR201))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_9 :
    Closed765 (decode (actCode 0 (decodeMask 590995))) := by
  have he : decode (actCode 0 (decodeMask 590995)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR202 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR202)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_10 :
    Closed765 (decode (actCode 0 (decodeMask 590999))) := by
  have he : decode (actCode 0 (decodeMask 590999)) =
      PaddedComponents.FM29 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM29, (by exact List.get_mem PaddedComponents.monoList ⟨28, by decide +kernel⟩), identity_perm_family PaddedComponents.FM29⟩)))))))))))))))

theorem closed_22_11 :
    Closed765 (decode (actCode 6 (decodeMask 591025))) := by
  have he : decode (actCode 6 (decodeMask 591025)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR203 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR203)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_12 :
    Closed765 (decode (actCode 0 (decodeMask 591027))) := by
  have he : decode (actCode 0 (decodeMask 591027)) =
      PaddedComponents.KCT6 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (identity_perm_family PaddedComponents.KCT6)))))⟩))))))))))

theorem closed_22_13 :
    Closed765 (decode (actCode 0 (decodeMask 591031))) := by
  have he : decode (actCode 0 (decodeMask 591031)) =
      PaddedComponents.FM34 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM34, (by exact List.get_mem PaddedComponents.monoList ⟨33, by decide +kernel⟩), identity_perm_family PaddedComponents.FM34⟩)))))))))))))))

theorem closed_22_14 :
    Closed765 (decode (actCode 0 (decodeMask 592903))) := by
  have he : decode (actCode 0 (decodeMask 592903)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR204 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR204)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_15 :
    Closed765 (decode (actCode 3 (decodeMask 592905))) := by
  have he : decode (actCode 3 (decodeMask 592905)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR205 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR205))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_16 :
    Closed765 (decode (actCode 1 (decodeMask 592907))) := by
  have he : decode (actCode 1 (decodeMask 592907)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR206 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR206)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_17 :
    Closed765 (decode (actCode 4 (decodeMask 592909))) := by
  have he : decode (actCode 4 (decodeMask 592909)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR207 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR207)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_18 :
    Closed765 (decode (actCode 0 (decodeMask 592919))) := by
  have he : decode (actCode 0 (decodeMask 592919)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR208 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR208)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_19 :
    Closed765 (decode (actCode 1 (decodeMask 592923))) := by
  have he : decode (actCode 1 (decodeMask 592923)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR209 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR209))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_20 :
    Closed765 (decode (actCode 0 (decodeMask 592935))) := by
  have he : decode (actCode 0 (decodeMask 592935)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR210 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR210)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_21 :
    Closed765 (decode (actCode 0 (decodeMask 592951))) := by
  have he : decode (actCode 0 (decodeMask 592951)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR211 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR211)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_22 :
    Closed765 (decode (actCode 0 (decodeMask 593027))) := by
  have he : decode (actCode 0 (decodeMask 593027)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR212 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR212)⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_23 :
    Closed765 (decode (actCode 2 (decodeMask 593031))) := by
  have he : decode (actCode 2 (decodeMask 593031)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR213 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR213))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_24 :
    Closed765 (decode (actCode 8 (decodeMask 593033))) := by
  have he : decode (actCode 8 (decodeMask 593033)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR214 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR214)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_25 :
    Closed765 (decode (actCode 4 (decodeMask 593037))) := by
  have he : decode (actCode 4 (decodeMask 593037)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR215 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR215)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_26 :
    Closed765 (decode (actCode 6 (decodeMask 593045))) := by
  have he : decode (actCode 6 (decodeMask 593045)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR216 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR216)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_27 :
    Closed765 (decode (actCode 0 (decodeMask 593047))) := by
  have he : decode (actCode 0 (decodeMask 593047)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR240 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR240)))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_22_28 :
    Closed765 (decode (actCode 0 (decodeMask 593059))) := by
  have he : decode (actCode 0 (decodeMask 593059)) =
      PaddedComponents.KTA1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KTA1)⟩)))))

theorem closed_22_29 :
    Closed765 (decode (actCode 2 (decodeMask 593063))) := by
  have he : decode (actCode 2 (decodeMask 593063)) =
      PaddedComponents.FM35 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM35, (by exact List.get_mem PaddedComponents.monoList ⟨34, by decide +kernel⟩), identity_perm_family PaddedComponents.FM35⟩)))))))))))))))

theorem closed_22_30 :
    Closed765 (decode (actCode 6 (decodeMask 593077))) := by
  have he : decode (actCode 6 (decodeMask 593077)) =
      PaddedComponents.FM36 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM36, (by exact List.get_mem PaddedComponents.monoList ⟨35, by decide +kernel⟩), identity_perm_family PaddedComponents.FM36⟩)))))))))))))))

theorem closed_22_31 :
    Closed765 (decode (actCode 0 (decodeMask 593079))) := by
  have he : decode (actCode 0 (decodeMask 593079)) =
      PaddedComponents.FM38 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM38, (by exact List.get_mem PaddedComponents.monoList ⟨37, by decide +kernel⟩), identity_perm_family PaddedComponents.FM38⟩)))))))))))))))

theorem checkedMasks22_closed (m : ℕ) (hm : m ∈ checkedMasks22) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks22, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_22_0
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_1
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_2
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_3
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_4
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_5
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_22_6
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_7
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_22_8
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_9
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_10
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_22_11
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_12
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_13
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_14
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_22_15
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_22_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_22_17
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_18
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_22_19
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_20
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_21
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_22
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_22_23
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_22_24
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_22_25
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_22_26
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_27
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_28
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_22_29
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_22_30
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_22_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks22_closed
