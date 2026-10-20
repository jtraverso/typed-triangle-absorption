/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks00

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_00_0 :
    Closed765 (decode (actCode 0 (decodeMask 96))) := by
  have he : decode (actCode 0 (decodeMask 96)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case00.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨0, rfl⟩

theorem closed_00_1 :
    Closed765 (decode (actCode 8 (decodeMask 192))) := by
  have he : decode (actCode 8 (decodeMask 192)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case01.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨1, rfl⟩

theorem closed_00_2 :
    Closed765 (decode (actCode 7 (decodeMask 208))) := by
  have he : decode (actCode 7 (decodeMask 208)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL011 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨11, by decide +kernel⟩)))

theorem closed_00_3 :
    Closed765 (decode (actCode 8 (decodeMask 224))) := by
  have he : decode (actCode 8 (decodeMask 224)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL010 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨10, by decide +kernel⟩)))

theorem closed_00_4 :
    Closed765 (decode (actCode 0 (decodeMask 352))) := by
  have he : decode (actCode 0 (decodeMask 352)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL016 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨16, by decide +kernel⟩)))

theorem closed_00_5 :
    Closed765 (decode (actCode 7 (decodeMask 464))) := by
  have he : decode (actCode 7 (decodeMask 464)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL065 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨65, by decide +kernel⟩)))

theorem closed_00_6 :
    Closed765 (decode (actCode 6 (decodeMask 656))) := by
  have he : decode (actCode 6 (decodeMask 656)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL015 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨15, by decide +kernel⟩)))

theorem closed_00_7 :
    Closed765 (decode (actCode 6 (decodeMask 688))) := by
  have he : decode (actCode 6 (decodeMask 688)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL064 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨64, by decide +kernel⟩)))

theorem closed_00_8 :
    Closed765 (decode (actCode 6 (decodeMask 1036))) := by
  have he : decode (actCode 6 (decodeMask 1036)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL004 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨4, by decide +kernel⟩)))

theorem closed_00_9 :
    Closed765 (decode (actCode 4 (decodeMask 1037))) := by
  have he : decode (actCode 4 (decodeMask 1037)) =
      PaddedComponents.FM01 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM01, (by exact List.get_mem PaddedComponents.monoList ⟨0, by decide +kernel⟩), identity_perm_family PaddedComponents.FM01⟩)))))))))))))))

theorem closed_00_10 :
    Closed765 (decode (actCode 7 (decodeMask 1160))) := by
  have he : decode (actCode 7 (decodeMask 1160)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL006 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨6, by decide +kernel⟩)))

theorem closed_00_11 :
    Closed765 (decode (actCode 5 (decodeMask 1161))) := by
  have he : decode (actCode 5 (decodeMask 1161)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL028 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨28, by decide +kernel⟩)))

theorem closed_00_12 :
    Closed765 (decode (actCode 4 (decodeMask 1164))) := by
  have he : decode (actCode 4 (decodeMask 1164)) =
      PaddedComponents.KCC1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KCC1)⟩)))))))))))

theorem closed_00_13 :
    Closed765 (decode (actCode 4 (decodeMask 1165))) := by
  have he : decode (actCode 4 (decodeMask 1165)) =
      PaddedComponents.FM02 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM02, (by exact List.get_mem PaddedComponents.monoList ⟨1, by decide +kernel⟩), identity_perm_family PaddedComponents.FM02⟩)))))))))))))))

theorem closed_00_14 :
    Closed765 (decode (actCode 7 (decodeMask 1216))) := by
  have he : decode (actCode 7 (decodeMask 1216)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case02.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨2, rfl⟩

theorem closed_00_15 :
    Closed765 (decode (actCode 7 (decodeMask 1232))) := by
  have he : decode (actCode 7 (decodeMask 1232)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL021 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨21, by decide +kernel⟩)))

theorem closed_00_16 :
    Closed765 (decode (actCode 6 (decodeMask 1280))) := by
  have he : decode (actCode 6 (decodeMask 1280)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case03.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨3, rfl⟩

theorem closed_00_17 :
    Closed765 (decode (actCode 4 (decodeMask 1281))) := by
  have he : decode (actCode 4 (decodeMask 1281)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case04.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨4, rfl⟩

theorem closed_00_18 :
    Closed765 (decode (actCode 6 (decodeMask 1284))) := by
  have he : decode (actCode 6 (decodeMask 1284)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL005 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨5, by decide +kernel⟩)))

theorem closed_00_19 :
    Closed765 (decode (actCode 4 (decodeMask 1285))) := by
  have he : decode (actCode 4 (decodeMask 1285)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL023 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨23, by decide +kernel⟩)))

theorem closed_00_20 :
    Closed765 (decode (actCode 4 (decodeMask 1292))) := by
  have he : decode (actCode 4 (decodeMask 1292)) =
      PaddedComponents.KQ1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KQ1)⟩))))

theorem closed_00_21 :
    Closed765 (decode (actCode 4 (decodeMask 1293))) := by
  have he : decode (actCode 4 (decodeMask 1293)) =
      PaddedComponents.FM03 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM03, (by exact List.get_mem PaddedComponents.monoList ⟨2, by decide +kernel⟩), identity_perm_family PaddedComponents.FM03⟩)))))))))))))))

theorem closed_00_22 :
    Closed765 (decode (actCode 6 (decodeMask 1296))) := by
  have he : decode (actCode 6 (decodeMask 1296)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case05.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨5, rfl⟩

theorem closed_00_23 :
    Closed765 (decode (actCode 6 (decodeMask 1312))) := by
  have he : decode (actCode 6 (decodeMask 1312)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case06.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨6, rfl⟩

theorem closed_00_24 :
    Closed765 (decode (actCode 6 (decodeMask 1328))) := by
  have he : decode (actCode 6 (decodeMask 1328)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL020 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨20, by decide +kernel⟩)))

theorem closed_00_25 :
    Closed765 (decode (actCode 4 (decodeMask 1409))) := by
  have he : decode (actCode 4 (decodeMask 1409)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL041 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨41, by decide +kernel⟩)))

theorem closed_00_26 :
    Closed765 (decode (actCode 6 (decodeMask 1412))) := by
  have he : decode (actCode 6 (decodeMask 1412)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC000 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨337, by decide +kernel⟩)))

theorem closed_00_27 :
    Closed765 (decode (actCode 4 (decodeMask 1413))) := by
  have he : decode (actCode 4 (decodeMask 1413)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL083 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨83, by decide +kernel⟩)))

theorem closed_00_28 :
    Closed765 (decode (actCode 7 (decodeMask 1416))) := by
  have he : decode (actCode 7 (decodeMask 1416)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC001 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨338, by decide +kernel⟩)))

theorem closed_00_29 :
    Closed765 (decode (actCode 5 (decodeMask 1417))) := by
  have he : decode (actCode 5 (decodeMask 1417)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL097 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨97, by decide +kernel⟩)))

theorem closed_00_30 :
    Closed765 (decode (actCode 4 (decodeMask 1420))) := by
  have he : decode (actCode 4 (decodeMask 1420)) =
      PaddedComponents.KQ4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ4))))⟩))))

theorem closed_00_31 :
    Closed765 (decode (actCode 4 (decodeMask 1421))) := by
  have he : decode (actCode 4 (decodeMask 1421)) =
      PaddedComponents.FM04 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM04, (by exact List.get_mem PaddedComponents.monoList ⟨3, by decide +kernel⟩), identity_perm_family PaddedComponents.FM04⟩)))))))))))))))

theorem checkedMasks00_closed (m : ℕ) (hm : m ∈ checkedMasks00) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks00, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_00_0
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_00_1
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_2
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_00_3
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_00_4
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_5
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_6
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_7
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_9
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_10
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_00_11
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_13
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_14
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_15
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_17
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_19
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_20
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_21
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_22
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_23
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_24
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_25
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_00_26
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_27
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_00_28
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_00_29
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_00_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks00_closed
