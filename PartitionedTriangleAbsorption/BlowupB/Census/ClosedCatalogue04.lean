/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks04

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_04_0 :
    Closed765 (decode (actCode 12 (decodeMask 3594))) := by
  have he : decode (actCode 12 (decodeMask 3594)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR006 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR006)))⟩)))))

theorem closed_04_1 :
    Closed765 (decode (actCode 3 (decodeMask 3595))) := by
  have he : decode (actCode 3 (decodeMask 3595)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR007 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR007)))⟩)))))

theorem closed_04_2 :
    Closed765 (decode (actCode 12 (decodeMask 3596))) := by
  have he : decode (actCode 12 (decodeMask 3596)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR008 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR008)⟩))))))

theorem closed_04_3 :
    Closed765 (decode (actCode 5 (decodeMask 3597))) := by
  have he : decode (actCode 5 (decodeMask 3597)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR009 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR009))⟩))))))

theorem closed_04_4 :
    Closed765 (decode (actCode 6 (decodeMask 3601))) := by
  have he : decode (actCode 6 (decodeMask 3601)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL072 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨72, by decide +kernel⟩)))

theorem closed_04_5 :
    Closed765 (decode (actCode 6 (decodeMask 3603))) := by
  have he : decode (actCode 6 (decodeMask 3603)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL152 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨152, by decide +kernel⟩)))

theorem closed_04_6 :
    Closed765 (decode (actCode 6 (decodeMask 3608))) := by
  have he : decode (actCode 6 (decodeMask 3608)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR010 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR010)))⟩))))))

theorem closed_04_7 :
    Closed765 (decode (actCode 6 (decodeMask 3609))) := by
  have he : decode (actCode 6 (decodeMask 3609)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR011 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR011)))⟩))))))

theorem closed_04_8 :
    Closed765 (decode (actCode 6 (decodeMask 3610))) := by
  have he : decode (actCode 6 (decodeMask 3610)) =
      PaddedNoCommon.NC2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC2))⟩))))))))))))))))))

theorem closed_04_9 :
    Closed765 (decode (actCode 1 (decodeMask 3611))) := by
  have he : decode (actCode 1 (decodeMask 3611)) =
      PaddedNoCommon.NC3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedNoCommon.NC3)))⟩))))))))))))))))))

theorem closed_04_10 :
    Closed765 (decode (actCode 12 (decodeMask 3712))) := by
  have he : decode (actCode 12 (decodeMask 3712)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL031 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨31, by decide +kernel⟩)))

theorem closed_04_11 :
    Closed765 (decode (actCode 12 (decodeMask 3713))) := by
  have he : decode (actCode 12 (decodeMask 3713)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL131 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨131, by decide +kernel⟩)))

theorem closed_04_12 :
    Closed765 (decode (actCode 12 (decodeMask 3716))) := by
  have he : decode (actCode 12 (decodeMask 3716)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC020 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨313, by decide +kernel⟩)))

theorem closed_04_13 :
    Closed765 (decode (actCode 4 (decodeMask 3717))) := by
  have he : decode (actCode 4 (decodeMask 3717)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL201 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨201, by decide +kernel⟩)))

theorem closed_04_14 :
    Closed765 (decode (actCode 12 (decodeMask 3720))) := by
  have he : decode (actCode 12 (decodeMask 3720)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC021 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨314, by decide +kernel⟩)))

theorem closed_04_15 :
    Closed765 (decode (actCode 5 (decodeMask 3721))) := by
  have he : decode (actCode 5 (decodeMask 3721)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL204 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨204, by decide +kernel⟩)))

theorem closed_04_16 :
    Closed765 (decode (actCode 12 (decodeMask 3724))) := by
  have he : decode (actCode 12 (decodeMask 3724)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR012 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR012)⟩)))))))

theorem closed_04_17 :
    Closed765 (decode (actCode 4 (decodeMask 3725))) := by
  have he : decode (actCode 4 (decodeMask 3725)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR013 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR013))⟩)))))))

theorem closed_04_18 :
    Closed765 (decode (actCode 12 (decodeMask 3728))) := by
  have he : decode (actCode 12 (decodeMask 3728)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL075 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨75, by decide +kernel⟩)))

theorem closed_04_19 :
    Closed765 (decode (actCode 12 (decodeMask 3744))) := by
  have he : decode (actCode 12 (decodeMask 3744)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC022 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨315, by decide +kernel⟩)))

theorem closed_04_20 :
    Closed765 (decode (actCode 12 (decodeMask 3760))) := by
  have he : decode (actCode 12 (decodeMask 3760)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL165 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨165, by decide +kernel⟩)))

theorem closed_04_21 :
    Closed765 (decode (actCode 12 (decodeMask 3841))) := by
  have he : decode (actCode 12 (decodeMask 3841)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL140 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨140, by decide +kernel⟩)))

theorem closed_04_22 :
    Closed765 (decode (actCode 12 (decodeMask 3844))) := by
  have he : decode (actCode 12 (decodeMask 3844)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC023 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨344, by decide +kernel⟩)))

theorem closed_04_23 :
    Closed765 (decode (actCode 4 (decodeMask 3845))) := by
  have he : decode (actCode 4 (decodeMask 3845)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL213 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨213, by decide +kernel⟩)))

theorem closed_04_24 :
    Closed765 (decode (actCode 12 (decodeMask 3848))) := by
  have he : decode (actCode 12 (decodeMask 3848)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC024 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨345, by decide +kernel⟩)))

theorem closed_04_25 :
    Closed765 (decode (actCode 5 (decodeMask 3849))) := by
  have he : decode (actCode 5 (decodeMask 3849)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL187 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨187, by decide +kernel⟩)))

theorem closed_04_26 :
    Closed765 (decode (actCode 12 (decodeMask 3852))) := by
  have he : decode (actCode 12 (decodeMask 3852)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR014 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR014)))⟩)))))))

theorem closed_04_27 :
    Closed765 (decode (actCode 5 (decodeMask 3853))) := by
  have he : decode (actCode 5 (decodeMask 3853)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR015 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR015)))⟩)))))))

theorem closed_04_28 :
    Closed765 (decode (actCode 6 (decodeMask 3856))) := by
  have he : decode (actCode 6 (decodeMask 3856)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL080 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨80, by decide +kernel⟩)))

theorem closed_04_29 :
    Closed765 (decode (actCode 12 (decodeMask 3872))) := by
  have he : decode (actCode 12 (decodeMask 3872)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC025 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨316, by decide +kernel⟩)))

theorem closed_04_30 :
    Closed765 (decode (actCode 6 (decodeMask 3888))) := by
  have he : decode (actCode 6 (decodeMask 3888)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL166 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨166, by decide +kernel⟩)))

theorem closed_04_31 :
    Closed765 (decode (actCode 4 (decodeMask 6156))) := by
  have he : decode (actCode 4 (decodeMask 6156)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL063 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨63, by decide +kernel⟩)))

theorem checkedMasks04_closed (m : ℕ) (hm : m ∈ checkedMasks04) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks04, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_0
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_04_1
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_2
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_04_3
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_4
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_5
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_6
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_7
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_8
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_04_9
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_10
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_11
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_04_13
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_14
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_04_15
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_04_17
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_18
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_19
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_20
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_21
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_04_23
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_24
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_04_25
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_26
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_04_27
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_28
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_04_29
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_04_30
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_04_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks04_closed
