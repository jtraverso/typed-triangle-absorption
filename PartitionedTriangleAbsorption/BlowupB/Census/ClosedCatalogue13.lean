/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks13

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_13_0 :
    Closed765 (decode (actCode 6 (decodeMask 69145))) := by
  have he : decode (actCode 6 (decodeMask 69145)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR076 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR076)⟩)))))))))))))))))))))))

theorem closed_13_1 :
    Closed765 (decode (actCode 6 (decodeMask 69146))) := by
  have he : decode (actCode 6 (decodeMask 69146)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR077 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR077))⟩)))))))))))))))))))))))

theorem closed_13_2 :
    Closed765 (decode (actCode 1 (decodeMask 69147))) := by
  have he : decode (actCode 1 (decodeMask 69147)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR078 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR078)))⟩)))))))))))))))))))))))

theorem closed_13_3 :
    Closed765 (decode (actCode 12 (decodeMask 69152))) := by
  have he : decode (actCode 12 (decodeMask 69152)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL098 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨98, by decide +kernel⟩)))

theorem closed_13_4 :
    Closed765 (decode (actCode 12 (decodeMask 69168))) := by
  have he : decode (actCode 12 (decodeMask 69168)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL164 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨164, by decide +kernel⟩)))

theorem closed_13_5 :
    Closed765 (decode (actCode 8 (decodeMask 69248))) := by
  have he : decode (actCode 8 (decodeMask 69248)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL121 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨121, by decide +kernel⟩)))

theorem closed_13_6 :
    Closed765 (decode (actCode 8 (decodeMask 69249))) := by
  have he : decode (actCode 8 (decodeMask 69249)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL224 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨224, by decide +kernel⟩)))

theorem closed_13_7 :
    Closed765 (decode (actCode 8 (decodeMask 69252))) := by
  have he : decode (actCode 8 (decodeMask 69252)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL198 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨198, by decide +kernel⟩)))

theorem closed_13_8 :
    Closed765 (decode (actCode 8 (decodeMask 69253))) := by
  have he : decode (actCode 8 (decodeMask 69253)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL270 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨270, by decide +kernel⟩)))

theorem closed_13_9 :
    Closed765 (decode (actCode 8 (decodeMask 69256))) := by
  have he : decode (actCode 8 (decodeMask 69256)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR079 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR079)))⟩)))))))))))))))))))))))

theorem closed_13_10 :
    Closed765 (decode (actCode 5 (decodeMask 69257))) := by
  have he : decode (actCode 5 (decodeMask 69257)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR080 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR080)⟩))))))))))))))))))))))))

theorem closed_13_11 :
    Closed765 (decode (actCode 8 (decodeMask 69260))) := by
  have he : decode (actCode 8 (decodeMask 69260)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR081 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR081))⟩))))))))))))))))))))))))

theorem closed_13_12 :
    Closed765 (decode (actCode 4 (decodeMask 69261))) := by
  have he : decode (actCode 4 (decodeMask 69261)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR082 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR082)))⟩))))))))))))))))))))))))

theorem closed_13_13 :
    Closed765 (decode (actCode 12 (decodeMask 69264))) := by
  have he : decode (actCode 12 (decodeMask 69264)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL169 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨169, by decide +kernel⟩)))

theorem closed_13_14 :
    Closed765 (decode (actCode 8 (decodeMask 69280))) := by
  have he : decode (actCode 8 (decodeMask 69280)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALT003 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨356, by decide +kernel⟩)))

theorem closed_13_15 :
    Closed765 (decode (actCode 12 (decodeMask 69296))) := by
  have he : decode (actCode 12 (decodeMask 69296)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL259 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨259, by decide +kernel⟩)))

theorem closed_13_16 :
    Closed765 (decode (actCode 8 (decodeMask 69642))) := by
  have he : decode (actCode 8 (decodeMask 69642)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL056 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨56, by decide +kernel⟩)))

theorem closed_13_17 :
    Closed765 (decode (actCode 1 (decodeMask 69643))) := by
  have he : decode (actCode 1 (decodeMask 69643)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL076 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨76, by decide +kernel⟩)))

theorem closed_13_18 :
    Closed765 (decode (actCode 3 (decodeMask 69657))) := by
  have he : decode (actCode 3 (decodeMask 69657)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL120 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨120, by decide +kernel⟩)))

theorem closed_13_19 :
    Closed765 (decode (actCode 8 (decodeMask 69658))) := by
  have he : decode (actCode 8 (decodeMask 69658)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR083 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR083)))⟩))))))))))))))))))))))))

theorem closed_13_20 :
    Closed765 (decode (actCode 1 (decodeMask 69659))) := by
  have he : decode (actCode 1 (decodeMask 69659)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR084 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR084)⟩)))))))))))))))))))))))))

theorem closed_13_21 :
    Closed765 (decode (actCode 1 (decodeMask 69706))) := by
  have he : decode (actCode 1 (decodeMask 69706)) =
      PaddedComponents.KCC2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KCC2))⟩)))))))))))

theorem closed_13_22 :
    Closed765 (decode (actCode 1 (decodeMask 69707))) := by
  have he : decode (actCode 1 (decodeMask 69707)) =
      PaddedComponents.KM2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KM2))⟩))))))))))))

theorem closed_13_23 :
    Closed765 (decode (actCode 3 (decodeMask 69721))) := by
  have he : decode (actCode 3 (decodeMask 69721)) =
      PaddedComponents.KTH1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KTH1)))))⟩)))))

theorem closed_13_24 :
    Closed765 (decode (actCode 8 (decodeMask 69722))) := by
  have he : decode (actCode 8 (decodeMask 69722)) =
      PaddedComponents.FM09 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM09, (by exact List.get_mem PaddedComponents.monoList ⟨8, by decide +kernel⟩), identity_perm_family PaddedComponents.FM09⟩)))))))))))))))

theorem closed_13_25 :
    Closed765 (decode (actCode 1 (decodeMask 69723))) := by
  have he : decode (actCode 1 (decodeMask 69723)) =
      PaddedComponents.FM14 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM14, (by exact List.get_mem PaddedComponents.monoList ⟨13, by decide +kernel⟩), identity_perm_family PaddedComponents.FM14⟩)))))))))))))))

theorem closed_13_26 :
    Closed765 (decode (actCode 2 (decodeMask 69765))) := by
  have he : decode (actCode 2 (decodeMask 69765)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL089 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨89, by decide +kernel⟩)))

theorem closed_13_27 :
    Closed765 (decode (actCode 2 (decodeMask 69767))) := by
  have he : decode (actCode 2 (decodeMask 69767)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL153 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨153, by decide +kernel⟩)))

theorem closed_13_28 :
    Closed765 (decode (actCode 4 (decodeMask 69773))) := by
  have he : decode (actCode 4 (decodeMask 69773)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL154 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨154, by decide +kernel⟩)))

theorem closed_13_29 :
    Closed765 (decode (actCode 2 (decodeMask 69781))) := by
  have he : decode (actCode 2 (decodeMask 69781)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL189 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨189, by decide +kernel⟩)))

theorem closed_13_30 :
    Closed765 (decode (actCode 2 (decodeMask 69783))) := by
  have he : decode (actCode 2 (decodeMask 69783)) =
      PaddedNoCommon.KT4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (identity_perm_family PaddedNoCommon.KT4))⟩))))))))))))))))

theorem closed_13_31 :
    Closed765 (decode (actCode 4 (decodeMask 70021))) := by
  have he : decode (actCode 4 (decodeMask 70021)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL182 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨182, by decide +kernel⟩)))

theorem checkedMasks13_closed (m : ℕ) (hm : m ∈ checkedMasks13) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks13, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_13_0
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_13_1
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_2
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_13_3
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_13_4
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_5
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_6
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_7
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_8
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_9
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_13_10
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_11
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_13_12
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_13_13
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_14
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_13_15
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_16
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_17
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_13_18
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_20
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_21
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_22
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_13_23
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_13_24
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_13_25
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_13_26
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_13_27
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_13_28
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_13_29
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_13_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_13_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks13_closed
