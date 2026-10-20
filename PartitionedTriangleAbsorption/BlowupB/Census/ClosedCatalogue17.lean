/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks17

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_17_0 :
    Closed765 (decode (actCode 4 (decodeMask 72333))) := by
  have he : decode (actCode 4 (decodeMask 72333)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL290 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨290, by decide +kernel⟩)))

theorem closed_17_1 :
    Closed765 (decode (actCode 4 (decodeMask 72717))) := by
  have he : decode (actCode 4 (decodeMask 72717)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR120 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR120)⟩))))))))))))))))))))))))))))))))))

theorem closed_17_2 :
    Closed765 (decode (actCode 18 (decodeMask 72840))) := by
  have he : decode (actCode 18 (decodeMask 72840)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL171 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨171, by decide +kernel⟩)))

theorem closed_17_3 :
    Closed765 (decode (actCode 18 (decodeMask 72841))) := by
  have he : decode (actCode 18 (decodeMask 72841)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR121 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR121))⟩))))))))))))))))))))))))))))))))))

theorem closed_17_4 :
    Closed765 (decode (actCode 18 (decodeMask 72844))) := by
  have he : decode (actCode 18 (decodeMask 72844)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR122 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR122)))⟩))))))))))))))))))))))))))))))))))

theorem closed_17_5 :
    Closed765 (decode (actCode 4 (decodeMask 72845))) := by
  have he : decode (actCode 4 (decodeMask 72845)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR123 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR123)))⟩))))))))))))))))))))))))))))))))))

theorem closed_17_6 :
    Closed765 (decode (actCode 18 (decodeMask 73217))) := by
  have he : decode (actCode 18 (decodeMask 73217)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL176 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨176, by decide +kernel⟩)))

theorem closed_17_7 :
    Closed765 (decode (actCode 18 (decodeMask 73220))) := by
  have he : decode (actCode 18 (decodeMask 73220)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL174 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨174, by decide +kernel⟩)))

theorem closed_17_8 :
    Closed765 (decode (actCode 18 (decodeMask 73221))) := by
  have he : decode (actCode 18 (decodeMask 73221)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL264 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨264, by decide +kernel⟩)))

theorem closed_17_9 :
    Closed765 (decode (actCode 18 (decodeMask 73225))) := by
  have he : decode (actCode 18 (decodeMask 73225)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR124 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR124)⟩)))))))))))))))))))))))))))))))))))

theorem closed_17_10 :
    Closed765 (decode (actCode 18 (decodeMask 73228))) := by
  have he : decode (actCode 18 (decodeMask 73228)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR125 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR125))⟩)))))))))))))))))))))))))))))))))))

theorem closed_17_11 :
    Closed765 (decode (actCode 5 (decodeMask 73229))) := by
  have he : decode (actCode 5 (decodeMask 73229)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR126 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR126)))⟩)))))))))))))))))))))))))))))))))))

theorem closed_17_12 :
    Closed765 (decode (actCode 18 (decodeMask 73344))) := by
  have he : decode (actCode 18 (decodeMask 73344)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL170 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨170, by decide +kernel⟩)))

theorem closed_17_13 :
    Closed765 (decode (actCode 18 (decodeMask 73345))) := by
  have he : decode (actCode 18 (decodeMask 73345)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL262 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨262, by decide +kernel⟩)))

theorem closed_17_14 :
    Closed765 (decode (actCode 18 (decodeMask 73348))) := by
  have he : decode (actCode 18 (decodeMask 73348)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL260 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨260, by decide +kernel⟩)))

theorem closed_17_15 :
    Closed765 (decode (actCode 18 (decodeMask 73349))) := by
  have he : decode (actCode 18 (decodeMask 73349)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL296 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨296, by decide +kernel⟩)))

theorem closed_17_16 :
    Closed765 (decode (actCode 18 (decodeMask 73352))) := by
  have he : decode (actCode 18 (decodeMask 73352)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR127 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR127)))⟩)))))))))))))))))))))))))))))))))))

theorem closed_17_17 :
    Closed765 (decode (actCode 18 (decodeMask 73353))) := by
  have he : decode (actCode 18 (decodeMask 73353)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR128 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR128)⟩))))))))))))))))))))))))))))))))))))

theorem closed_17_18 :
    Closed765 (decode (actCode 18 (decodeMask 73356))) := by
  have he : decode (actCode 18 (decodeMask 73356)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR129 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR129))⟩))))))))))))))))))))))))))))))))))))

theorem closed_17_19 :
    Closed765 (decode (actCode 4 (decodeMask 73357))) := by
  have he : decode (actCode 4 (decodeMask 73357)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR130 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR130)))⟩))))))))))))))))))))))))))))))))))))

theorem closed_17_20 :
    Closed765 (decode (actCode 12 (decodeMask 77313))) := by
  have he : decode (actCode 12 (decodeMask 77313)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL205 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨205, by decide +kernel⟩)))

theorem closed_17_21 :
    Closed765 (decode (actCode 12 (decodeMask 77315))) := by
  have he : decode (actCode 12 (decodeMask 77315)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL272 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨272, by decide +kernel⟩)))

theorem closed_17_22 :
    Closed765 (decode (actCode 3 (decodeMask 77320))) := by
  have he : decode (actCode 3 (decodeMask 77320)) =
      PaddedComponents.KQ9 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ9)))))))))⟩))))

theorem closed_17_23 :
    Closed765 (decode (actCode 12 (decodeMask 77321))) := by
  have he : decode (actCode 12 (decodeMask 77321)) =
      PaddedComponents.FB5 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.FB5)))))⟩))))))))))))))))

theorem closed_17_24 :
    Closed765 (decode (actCode 12 (decodeMask 77322))) := by
  have he : decode (actCode 12 (decodeMask 77322)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR131 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR131)))⟩))))))))))))))))))))))))))))))))))))

theorem closed_17_25 :
    Closed765 (decode (actCode 3 (decodeMask 77323))) := by
  have he : decode (actCode 3 (decodeMask 77323)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR132 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR132)⟩)))))))))))))))))))))))))))))))))))))

theorem closed_17_26 :
    Closed765 (decode (actCode 12 (decodeMask 77329))) := by
  have he : decode (actCode 12 (decodeMask 77329)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL251 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨251, by decide +kernel⟩)))

theorem closed_17_27 :
    Closed765 (decode (actCode 6 (decodeMask 77331))) := by
  have he : decode (actCode 6 (decodeMask 77331)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL288 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨288, by decide +kernel⟩)))

theorem closed_17_28 :
    Closed765 (decode (actCode 12 (decodeMask 77336))) := by
  have he : decode (actCode 12 (decodeMask 77336)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR133 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR133))⟩)))))))))))))))))))))))))))))))))))))

theorem closed_17_29 :
    Closed765 (decode (actCode 12 (decodeMask 77337))) := by
  have he : decode (actCode 12 (decodeMask 77337)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR134 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR134)))⟩)))))))))))))))))))))))))))))))))))))

theorem closed_17_30 :
    Closed765 (decode (actCode 12 (decodeMask 77338))) := by
  have he : decode (actCode 12 (decodeMask 77338)) =
      PaddedNoCommon.NC10 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC10))))))))))⟩))))))))))))))))))

theorem closed_17_31 :
    Closed765 (decode (actCode 6 (decodeMask 77339))) := by
  have he : decode (actCode 6 (decodeMask 77339)) =
      PaddedNoCommon.NC12 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC12))))))))))))⟩))))))))))))))))))

theorem checkedMasks17_closed (m : ℕ) (hm : m ∈ checkedMasks17) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks17, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_17_0
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_17_1
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_2
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_3
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_4
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_17_5
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_6
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_7
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_8
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_9
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_10
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_17_11
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_12
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_13
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_14
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_15
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_16
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_17
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_17_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_17_19
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_20
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_21
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_17_22
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_23
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_17_25
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_26
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_17_27
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_28
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_29
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_17_30
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_17_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks17_closed
