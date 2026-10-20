/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks14

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_14_0 :
    Closed765 (decode (actCode 4 (decodeMask 70029))) := by
  have he : decode (actCode 4 (decodeMask 70029)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL239 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨239, by decide +kernel⟩)))

theorem closed_14_1 :
    Closed765 (decode (actCode 8 (decodeMask 70146))) := by
  have he : decode (actCode 8 (decodeMask 70146)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL058 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨58, by decide +kernel⟩)))

theorem closed_14_2 :
    Closed765 (decode (actCode 1 (decodeMask 70147))) := by
  have he : decode (actCode 1 (decodeMask 70147)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL114 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨114, by decide +kernel⟩)))

theorem closed_14_3 :
    Closed765 (decode (actCode 10 (decodeMask 70154))) := by
  have he : decode (actCode 10 (decodeMask 70154)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC050 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨335, by decide +kernel⟩)))

theorem closed_14_4 :
    Closed765 (decode (actCode 3 (decodeMask 70155))) := by
  have he : decode (actCode 3 (decodeMask 70155)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL158 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨158, by decide +kernel⟩)))

theorem closed_14_5 :
    Closed765 (decode (actCode 1 (decodeMask 70161))) := by
  have he : decode (actCode 1 (decodeMask 70161)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL143 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨143, by decide +kernel⟩)))

theorem closed_14_6 :
    Closed765 (decode (actCode 1 (decodeMask 70163))) := by
  have he : decode (actCode 1 (decodeMask 70163)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL192 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨192, by decide +kernel⟩)))

theorem closed_14_7 :
    Closed765 (decode (actCode 14 (decodeMask 70168))) := by
  have he : decode (actCode 14 (decodeMask 70168)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC051 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨336, by decide +kernel⟩)))

theorem closed_14_8 :
    Closed765 (decode (actCode 3 (decodeMask 70169))) := by
  have he : decode (actCode 3 (decodeMask 70169)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL197 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨197, by decide +kernel⟩)))

theorem closed_14_9 :
    Closed765 (decode (actCode 8 (decodeMask 70170))) := by
  have he : decode (actCode 8 (decodeMask 70170)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR085 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR085))⟩)))))))))))))))))))))))))

theorem closed_14_10 :
    Closed765 (decode (actCode 1 (decodeMask 70171))) := by
  have he : decode (actCode 1 (decodeMask 70171)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR086 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR086)))⟩)))))))))))))))))))))))))

theorem closed_14_11 :
    Closed765 (decode (actCode 1 (decodeMask 70210))) := by
  have he : decode (actCode 1 (decodeMask 70210)) =
      PaddedComponents.KC2C := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, identity_perm_family PaddedComponents.KC2C⟩))))))))

theorem closed_14_12 :
    Closed765 (decode (actCode 1 (decodeMask 70211))) := by
  have he : decode (actCode 1 (decodeMask 70211)) =
      PaddedComponents.KCX3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KCX3)))⟩)))))))))

theorem closed_14_13 :
    Closed765 (decode (actCode 3 (decodeMask 70218))) := by
  have he : decode (actCode 3 (decodeMask 70218)) =
      PaddedComponents.KCC3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (identity_perm_family PaddedComponents.KCC3))⟩)))))))))))

theorem closed_14_14 :
    Closed765 (decode (actCode 3 (decodeMask 70219))) := by
  have he : decode (actCode 3 (decodeMask 70219)) =
      PaddedComponents.KM3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KM3)))⟩))))))))))))

theorem closed_14_15 :
    Closed765 (decode (actCode 1 (decodeMask 70225))) := by
  have he : decode (actCode 1 (decodeMask 70225)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR087 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR087)))⟩)))))))))))))))))))))))))

theorem closed_14_16 :
    Closed765 (decode (actCode 1 (decodeMask 70227))) := by
  have he : decode (actCode 1 (decodeMask 70227)) =
      PaddedComponents.KM4 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KM4))))⟩))))))))))))

theorem closed_14_17 :
    Closed765 (decode (actCode 7 (decodeMask 70232))) := by
  have he : decode (actCode 7 (decodeMask 70232)) =
      PaddedComponents.KQ8 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ8))))))))⟩))))

theorem closed_14_18 :
    Closed765 (decode (actCode 3 (decodeMask 70233))) := by
  have he : decode (actCode 3 (decodeMask 70233)) =
      PaddedComponents.KTH2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KTH2))))))⟩)))))

theorem closed_14_19 :
    Closed765 (decode (actCode 8 (decodeMask 70234))) := by
  have he : decode (actCode 8 (decodeMask 70234)) =
      PaddedComponents.FM15 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM15, (by exact List.get_mem PaddedComponents.monoList ⟨14, by decide +kernel⟩), identity_perm_family PaddedComponents.FM15⟩)))))))))))))))

theorem closed_14_20 :
    Closed765 (decode (actCode 1 (decodeMask 70235))) := by
  have he : decode (actCode 1 (decodeMask 70235)) =
      PaddedComponents.FM20 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM20, (by exact List.get_mem PaddedComponents.monoList ⟨19, by decide +kernel⟩), identity_perm_family PaddedComponents.FM20⟩)))))))))))))))

theorem closed_14_21 :
    Closed765 (decode (actCode 4 (decodeMask 70277))) := by
  have he : decode (actCode 4 (decodeMask 70277)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL190 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨190, by decide +kernel⟩)))

theorem closed_14_22 :
    Closed765 (decode (actCode 4 (decodeMask 70285))) := by
  have he : decode (actCode 4 (decodeMask 70285)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL242 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨242, by decide +kernel⟩)))

theorem closed_14_23 :
    Closed765 (decode (actCode 8 (decodeMask 70288))) := by
  have he : decode (actCode 8 (decodeMask 70288)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL138 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨138, by decide +kernel⟩)))

theorem closed_14_24 :
    Closed765 (decode (actCode 8 (decodeMask 70352))) := by
  have he : decode (actCode 8 (decodeMask 70352)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR088 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR088)⟩))))))))))))))))))))))))))

theorem closed_14_25 :
    Closed765 (decode (actCode 3 (decodeMask 70665))) := by
  have he : decode (actCode 3 (decodeMask 70665)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR089 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR089))⟩))))))))))))))))))))))))))

theorem closed_14_26 :
    Closed765 (decode (actCode 1 (decodeMask 70667))) := by
  have he : decode (actCode 1 (decodeMask 70667)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR090 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR090)))⟩))))))))))))))))))))))))))

theorem closed_14_27 :
    Closed765 (decode (actCode 13 (decodeMask 70668))) := by
  have he : decode (actCode 13 (decodeMask 70668)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL139 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨139, by decide +kernel⟩)))

theorem closed_14_28 :
    Closed765 (decode (actCode 4 (decodeMask 70669))) := by
  have he : decode (actCode 4 (decodeMask 70669)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR091 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR091)))⟩))))))))))))))))))))))))))

theorem closed_14_29 :
    Closed765 (decode (actCode 1 (decodeMask 70683))) := by
  have he : decode (actCode 1 (decodeMask 70683)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR092 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR092)⟩)))))))))))))))))))))))))))

theorem closed_14_30 :
    Closed765 (decode (actCode 3 (decodeMask 70729))) := by
  have he : decode (actCode 3 (decodeMask 70729)) =
      PaddedComponents.KCT3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KCT3)))⟩))))))))))

theorem closed_14_31 :
    Closed765 (decode (actCode 1 (decodeMask 70731))) := by
  have he : decode (actCode 1 (decodeMask 70731)) =
      PaddedComponents.FM16 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM16, (by exact List.get_mem PaddedComponents.monoList ⟨15, by decide +kernel⟩), identity_perm_family PaddedComponents.FM16⟩)))))))))))))))

theorem checkedMasks14_closed (m : ℕ) (hm : m ∈ checkedMasks14) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks14, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_14_0
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_14_1
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_2
  · refine ⟨sigma 10, ?_⟩
    rw [← decode_actCode]
    exact closed_14_3
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_4
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_5
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_6
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_14_7
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_8
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_14_9
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_10
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_11
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_12
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_13
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_14
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_15
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_16
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_14_17
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_18
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_14_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_20
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_14_21
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_14_22
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_14_23
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_14_24
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_25
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_26
  · refine ⟨sigma 13, ?_⟩
    rw [← decode_actCode]
    exact closed_14_27
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_14_28
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_29
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_14_30
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_14_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks14_closed
