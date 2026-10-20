/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks01

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_01_0 :
    Closed765 (decode (actCode 6 (decodeMask 1424))) := by
  have he : decode (actCode 6 (decodeMask 1424)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL033 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨33, by decide +kernel⟩)))

theorem closed_01_1 :
    Closed765 (decode (actCode 7 (decodeMask 1472))) := by
  have he : decode (actCode 7 (decodeMask 1472)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL055 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨55, by decide +kernel⟩)))

theorem closed_01_2 :
    Closed765 (decode (actCode 7 (decodeMask 1488))) := by
  have he : decode (actCode 7 (decodeMask 1488)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL102 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨102, by decide +kernel⟩)))

theorem closed_01_3 :
    Closed765 (decode (actCode 12 (decodeMask 1664))) := by
  have he : decode (actCode 12 (decodeMask 1664)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL007 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨7, by decide +kernel⟩)))

theorem closed_01_4 :
    Closed765 (decode (actCode 4 (decodeMask 1665))) := by
  have he : decode (actCode 4 (decodeMask 1665)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL044 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨44, by decide +kernel⟩)))

theorem closed_01_5 :
    Closed765 (decode (actCode 6 (decodeMask 1668))) := by
  have he : decode (actCode 6 (decodeMask 1668)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC002 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨301, by decide +kernel⟩)))

theorem closed_01_6 :
    Closed765 (decode (actCode 4 (decodeMask 1669))) := by
  have he : decode (actCode 4 (decodeMask 1669)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL088 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨88, by decide +kernel⟩)))

theorem closed_01_7 :
    Closed765 (decode (actCode 4 (decodeMask 1676))) := by
  have he : decode (actCode 4 (decodeMask 1676)) =
      PaddedComponents.KQ5 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ5)))))⟩))))

theorem closed_01_8 :
    Closed765 (decode (actCode 4 (decodeMask 1677))) := by
  have he : decode (actCode 4 (decodeMask 1677)) =
      PaddedComponents.FM05 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM05, (by exact List.get_mem PaddedComponents.monoList ⟨4, by decide +kernel⟩), identity_perm_family PaddedComponents.FM05⟩)))))))))))))))

theorem closed_01_9 :
    Closed765 (decode (actCode 6 (decodeMask 1680))) := by
  have he : decode (actCode 6 (decodeMask 1680)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL034 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨34, by decide +kernel⟩)))

theorem closed_01_10 :
    Closed765 (decode (actCode 12 (decodeMask 1696))) := by
  have he : decode (actCode 12 (decodeMask 1696)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL053 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨53, by decide +kernel⟩)))

theorem closed_01_11 :
    Closed765 (decode (actCode 6 (decodeMask 1712))) := by
  have he : decode (actCode 6 (decodeMask 1712)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL100 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨100, by decide +kernel⟩)))

theorem closed_01_12 :
    Closed765 (decode (actCode 12 (decodeMask 1920))) := by
  have he : decode (actCode 12 (decodeMask 1920)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL057 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨57, by decide +kernel⟩)))

theorem closed_01_13 :
    Closed765 (decode (actCode 4 (decodeMask 1921))) := by
  have he : decode (actCode 4 (decodeMask 1921)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL141 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨141, by decide +kernel⟩)))

theorem closed_01_14 :
    Closed765 (decode (actCode 6 (decodeMask 1924))) := by
  have he : decode (actCode 6 (decodeMask 1924)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC003 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨339, by decide +kernel⟩)))

theorem closed_01_15 :
    Closed765 (decode (actCode 4 (decodeMask 1925))) := by
  have he : decode (actCode 4 (decodeMask 1925)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL181 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨181, by decide +kernel⟩)))

theorem closed_01_16 :
    Closed765 (decode (actCode 4 (decodeMask 1932))) := by
  have he : decode (actCode 4 (decodeMask 1932)) =
      PaddedComponents.KQ7 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ7)))))))⟩))))

theorem closed_01_17 :
    Closed765 (decode (actCode 4 (decodeMask 1933))) := by
  have he : decode (actCode 4 (decodeMask 1933)) =
      PaddedComponents.FM10 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM10, (by exact List.get_mem PaddedComponents.monoList ⟨9, by decide +kernel⟩), identity_perm_family PaddedComponents.FM10⟩)))))))))))))))

theorem closed_01_18 :
    Closed765 (decode (actCode 6 (decodeMask 1936))) := by
  have he : decode (actCode 6 (decodeMask 1936)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL135 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨135, by decide +kernel⟩)))

theorem closed_01_19 :
    Closed765 (decode (actCode 3 (decodeMask 2056))) := by
  have he : decode (actCode 3 (decodeMask 2056)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL000 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨0, by decide +kernel⟩)))

theorem closed_01_20 :
    Closed765 (decode (actCode 3 (decodeMask 2057))) := by
  have he : decode (actCode 3 (decodeMask 2057)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL001 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨1, by decide +kernel⟩)))

theorem closed_01_21 :
    Closed765 (decode (actCode 1 (decodeMask 2058))) := by
  have he : decode (actCode 1 (decodeMask 2058)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL008 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨8, by decide +kernel⟩)))

theorem closed_01_22 :
    Closed765 (decode (actCode 1 (decodeMask 2059))) := by
  have he : decode (actCode 1 (decodeMask 2059)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL017 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨17, by decide +kernel⟩)))

theorem closed_01_23 :
    Closed765 (decode (actCode 4 (decodeMask 2060))) := by
  have he : decode (actCode 4 (decodeMask 2060)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL009 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨9, by decide +kernel⟩)))

theorem closed_01_24 :
    Closed765 (decode (actCode 4 (decodeMask 2061))) := by
  have he : decode (actCode 4 (decodeMask 2061)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL018 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨18, by decide +kernel⟩)))

theorem closed_01_25 :
    Closed765 (decode (actCode 3 (decodeMask 2073))) := by
  have he : decode (actCode 3 (decodeMask 2073)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL026 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨26, by decide +kernel⟩)))

theorem closed_01_26 :
    Closed765 (decode (actCode 1 (decodeMask 2074))) := by
  have he : decode (actCode 1 (decodeMask 2074)) =
      PaddedCharge.KCa := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedCharge.KCa)⟩)))))))))))))

theorem closed_01_27 :
    Closed765 (decode (actCode 1 (decodeMask 2075))) := by
  have he : decode (actCode 1 (decodeMask 2075)) =
      PaddedNoCommon.KT1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (⟨1, identity_perm_family PaddedNoCommon.KT1⟩)))))))))))))))))

theorem closed_01_28 :
    Closed765 (decode (actCode 8 (decodeMask 2184))) := by
  have he : decode (actCode 8 (decodeMask 2184)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL013 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨13, by decide +kernel⟩)))

theorem closed_01_29 :
    Closed765 (decode (actCode 5 (decodeMask 2185))) := by
  have he : decode (actCode 5 (decodeMask 2185)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL027 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨27, by decide +kernel⟩)))

theorem closed_01_30 :
    Closed765 (decode (actCode 4 (decodeMask 2188))) := by
  have he : decode (actCode 4 (decodeMask 2188)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC004 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨302, by decide +kernel⟩)))

theorem closed_01_31 :
    Closed765 (decode (actCode 4 (decodeMask 2189))) := by
  have he : decode (actCode 4 (decodeMask 2189)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL067 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨67, by decide +kernel⟩)))

theorem checkedMasks01_closed (m : ℕ) (hm : m ∈ checkedMasks01) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks01, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_0
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_01_1
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_01_2
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_01_3
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_4
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_5
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_6
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_7
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_8
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_9
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_01_10
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_11
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_01_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_13
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_14
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_15
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_17
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_01_18
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_01_19
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_01_20
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_01_21
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_01_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_23
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_01_25
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_01_26
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_01_27
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_01_28
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_01_29
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_01_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks01_closed
