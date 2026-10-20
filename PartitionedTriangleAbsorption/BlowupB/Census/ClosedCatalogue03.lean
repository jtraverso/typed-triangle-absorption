/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks03

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_03_0 :
    Closed765 (decode (actCode 5 (decodeMask 2817))) := by
  have he : decode (actCode 5 (decodeMask 2817)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL040 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨40, by decide +kernel⟩)))

theorem closed_03_1 :
    Closed765 (decode (actCode 4 (decodeMask 2821))) := by
  have he : decode (actCode 4 (decodeMask 2821)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL096 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨96, by decide +kernel⟩)))

theorem closed_03_2 :
    Closed765 (decode (actCode 5 (decodeMask 2824))) := by
  have he : decode (actCode 5 (decodeMask 2824)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC016 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨342, by decide +kernel⟩)))

theorem closed_03_3 :
    Closed765 (decode (actCode 5 (decodeMask 2825))) := by
  have he : decode (actCode 5 (decodeMask 2825)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL082 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨82, by decide +kernel⟩)))

theorem closed_03_4 :
    Closed765 (decode (actCode 5 (decodeMask 2828))) := by
  have he : decode (actCode 5 (decodeMask 2828)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC017 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨312, by decide +kernel⟩)))

theorem closed_03_5 :
    Closed765 (decode (actCode 5 (decodeMask 2829))) := by
  have he : decode (actCode 5 (decodeMask 2829)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL150 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨150, by decide +kernel⟩)))

theorem closed_03_6 :
    Closed765 (decode (actCode 6 (decodeMask 2832))) := by
  have he : decode (actCode 6 (decodeMask 2832)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL062 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨62, by decide +kernel⟩)))

theorem closed_03_7 :
    Closed765 (decode (actCode 11 (decodeMask 2848))) := by
  have he : decode (actCode 11 (decodeMask 2848)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC018 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨352, by decide +kernel⟩)))

theorem closed_03_8 :
    Closed765 (decode (actCode 6 (decodeMask 2864))) := by
  have he : decode (actCode 6 (decodeMask 2864)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC019 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨343, by decide +kernel⟩)))

theorem closed_03_9 :
    Closed765 (decode (actCode 3 (decodeMask 3081))) := by
  have he : decode (actCode 3 (decodeMask 3081)) =
      PaddedComponents.FB1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.FB1)⟩))))))))))))))))

theorem closed_03_10 :
    Closed765 (decode (actCode 1 (decodeMask 3083))) := by
  have he : decode (actCode 1 (decodeMask 3083)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR000 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR000)⟩))))

theorem closed_03_11 :
    Closed765 (decode (actCode 12 (decodeMask 3084))) := by
  have he : decode (actCode 12 (decodeMask 3084)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL035 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨35, by decide +kernel⟩)))

theorem closed_03_12 :
    Closed765 (decode (actCode 4 (decodeMask 3085))) := by
  have he : decode (actCode 4 (decodeMask 3085)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR001 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR001))⟩))))

theorem closed_03_13 :
    Closed765 (decode (actCode 1 (decodeMask 3099))) := by
  have he : decode (actCode 1 (decodeMask 3099)) =
      PaddedNoCommon.NC1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedNoCommon.NC1)⟩))))))))))))))))))

theorem closed_03_14 :
    Closed765 (decode (actCode 12 (decodeMask 3208))) := by
  have he : decode (actCode 12 (decodeMask 3208)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL030 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨30, by decide +kernel⟩)))

theorem closed_03_15 :
    Closed765 (decode (actCode 5 (decodeMask 3209))) := by
  have he : decode (actCode 5 (decodeMask 3209)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL126 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨126, by decide +kernel⟩)))

theorem closed_03_16 :
    Closed765 (decode (actCode 12 (decodeMask 3212))) := by
  have he : decode (actCode 12 (decodeMask 3212)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR002 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR002)))⟩))))

theorem closed_03_17 :
    Closed765 (decode (actCode 4 (decodeMask 3213))) := by
  have he : decode (actCode 4 (decodeMask 3213)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR003 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR003)))⟩))))

theorem closed_03_18 :
    Closed765 (decode (actCode 12 (decodeMask 3329))) := by
  have he : decode (actCode 12 (decodeMask 3329)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case08.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨8, rfl⟩

theorem closed_03_19 :
    Closed765 (decode (actCode 4 (decodeMask 3333))) := by
  have he : decode (actCode 4 (decodeMask 3333)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL106 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨106, by decide +kernel⟩)))

theorem closed_03_20 :
    Closed765 (decode (actCode 12 (decodeMask 3336))) := by
  have he : decode (actCode 12 (decodeMask 3336)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL038 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨38, by decide +kernel⟩)))

theorem closed_03_21 :
    Closed765 (decode (actCode 5 (decodeMask 3337))) := by
  have he : decode (actCode 5 (decodeMask 3337)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL108 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨108, by decide +kernel⟩)))

theorem closed_03_22 :
    Closed765 (decode (actCode 12 (decodeMask 3340))) := by
  have he : decode (actCode 12 (decodeMask 3340)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR004 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR004)⟩)))))

theorem closed_03_23 :
    Closed765 (decode (actCode 4 (decodeMask 3341))) := by
  have he : decode (actCode 4 (decodeMask 3341)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR005 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR005))⟩)))))

theorem closed_03_24 :
    Closed765 (decode (actCode 6 (decodeMask 3344))) := by
  have he : decode (actCode 6 (decodeMask 3344)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case09.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨9, rfl⟩

theorem closed_03_25 :
    Closed765 (decode (actCode 6 (decodeMask 3376))) := by
  have he : decode (actCode 6 (decodeMask 3376)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL070 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨70, by decide +kernel⟩)))

theorem closed_03_26 :
    Closed765 (decode (actCode 12 (decodeMask 3585))) := by
  have he : decode (actCode 12 (decodeMask 3585)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL039 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨39, by decide +kernel⟩)))

theorem closed_03_27 :
    Closed765 (decode (actCode 1 (decodeMask 3587))) := by
  have he : decode (actCode 1 (decodeMask 3587)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL109 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨109, by decide +kernel⟩)))

theorem closed_03_28 :
    Closed765 (decode (actCode 12 (decodeMask 3588))) := by
  have he : decode (actCode 12 (decodeMask 3588)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL036 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨36, by decide +kernel⟩)))

theorem closed_03_29 :
    Closed765 (decode (actCode 4 (decodeMask 3589))) := by
  have he : decode (actCode 4 (decodeMask 3589)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL124 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨124, by decide +kernel⟩)))

theorem closed_03_30 :
    Closed765 (decode (actCode 3 (decodeMask 3592))) := by
  have he : decode (actCode 3 (decodeMask 3592)) =
      PaddedComponents.KQ2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KQ2))⟩))))

theorem closed_03_31 :
    Closed765 (decode (actCode 3 (decodeMask 3593))) := by
  have he : decode (actCode 3 (decodeMask 3593)) =
      PaddedComponents.FB2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.FB2))⟩))))))))))))))))

theorem checkedMasks03_closed (m : ℕ) (hm : m ∈ checkedMasks03) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks03, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_0
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_1
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_2
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_3
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_4
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_5
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_03_6
  · refine ⟨sigma 11, ?_⟩
    rw [← decode_actCode]
    exact closed_03_7
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_03_8
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_03_9
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_03_10
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_11
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_12
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_03_13
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_14
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_15
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_17
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_18
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_19
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_20
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_03_21
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_23
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_03_24
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_03_25
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_26
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_03_27
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_03_28
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_03_29
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_03_30
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_03_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks03_closed
