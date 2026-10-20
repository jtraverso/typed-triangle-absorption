/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks08

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_08_0 :
    Closed765 (decode (actCode 8 (decodeMask 12428))) := by
  have he : decode (actCode 8 (decodeMask 12428)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC039 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨348, by decide +kernel⟩)))

theorem closed_08_1 :
    Closed765 (decode (actCode 4 (decodeMask 12429))) := by
  have he : decode (actCode 4 (decodeMask 12429)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL157 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨157, by decide +kernel⟩)))

theorem closed_08_2 :
    Closed765 (decode (actCode 4 (decodeMask 12804))) := by
  have he : decode (actCode 4 (decodeMask 12804)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL066 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨66, by decide +kernel⟩)))

theorem closed_08_3 :
    Closed765 (decode (actCode 4 (decodeMask 12805))) := by
  have he : decode (actCode 4 (decodeMask 12805)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL117 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨117, by decide +kernel⟩)))

theorem closed_08_4 :
    Closed765 (decode (actCode 5 (decodeMask 12812))) := by
  have he : decode (actCode 5 (decodeMask 12812)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC040 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨328, by decide +kernel⟩)))

theorem closed_08_5 :
    Closed765 (decode (actCode 5 (decodeMask 12813))) := by
  have he : decode (actCode 5 (decodeMask 12813)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL160 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨160, by decide +kernel⟩)))

theorem closed_08_6 :
    Closed765 (decode (actCode 4 (decodeMask 12929))) := by
  have he : decode (actCode 4 (decodeMask 12929)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL145 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨145, by decide +kernel⟩)))

theorem closed_08_7 :
    Closed765 (decode (actCode 4 (decodeMask 12933))) := by
  have he : decode (actCode 4 (decodeMask 12933)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL195 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨195, by decide +kernel⟩)))

theorem closed_08_8 :
    Closed765 (decode (actCode 5 (decodeMask 12937))) := by
  have he : decode (actCode 5 (decodeMask 12937)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL199 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨199, by decide +kernel⟩)))

theorem closed_08_9 :
    Closed765 (decode (actCode 4 (decodeMask 12940))) := by
  have he : decode (actCode 4 (decodeMask 12940)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC041 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨329, by decide +kernel⟩)))

theorem closed_08_10 :
    Closed765 (decode (actCode 4 (decodeMask 12941))) := by
  have he : decode (actCode 4 (decodeMask 12941)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL243 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨243, by decide +kernel⟩)))

theorem closed_08_11 :
    Closed765 (decode (actCode 5 (decodeMask 13449))) := by
  have he : decode (actCode 5 (decodeMask 13449)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL234 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨234, by decide +kernel⟩)))

theorem closed_08_12 :
    Closed765 (decode (actCode 19 (decodeMask 13452))) := by
  have he : decode (actCode 19 (decodeMask 13452)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR037 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR037))⟩)))))))))))))

theorem closed_08_13 :
    Closed765 (decode (actCode 4 (decodeMask 13453))) := by
  have he : decode (actCode 4 (decodeMask 13453)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR038 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR038)))⟩)))))))))))))

theorem closed_08_14 :
    Closed765 (decode (actCode 4 (decodeMask 13829))) := by
  have he : decode (actCode 4 (decodeMask 13829)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL232 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨232, by decide +kernel⟩)))

theorem closed_08_15 :
    Closed765 (decode (actCode 19 (decodeMask 13836))) := by
  have he : decode (actCode 19 (decodeMask 13836)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC042 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨330, by decide +kernel⟩)))

theorem closed_08_16 :
    Closed765 (decode (actCode 5 (decodeMask 13837))) := by
  have he : decode (actCode 5 (decodeMask 13837)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL258 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨258, by decide +kernel⟩)))

theorem closed_08_17 :
    Closed765 (decode (actCode 19 (decodeMask 13952))) := by
  have he : decode (actCode 19 (decodeMask 13952)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL116 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨116, by decide +kernel⟩)))

theorem closed_08_18 :
    Closed765 (decode (actCode 19 (decodeMask 13953))) := by
  have he : decode (actCode 19 (decodeMask 13953)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL231 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨231, by decide +kernel⟩)))

theorem closed_08_19 :
    Closed765 (decode (actCode 19 (decodeMask 13956))) := by
  have he : decode (actCode 19 (decodeMask 13956)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC043 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨331, by decide +kernel⟩)))

theorem closed_08_20 :
    Closed765 (decode (actCode 4 (decodeMask 13957))) := by
  have he : decode (actCode 4 (decodeMask 13957)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL280 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨280, by decide +kernel⟩)))

theorem closed_08_21 :
    Closed765 (decode (actCode 19 (decodeMask 13960))) := by
  have he : decode (actCode 19 (decodeMask 13960)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC044 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨332, by decide +kernel⟩)))

theorem closed_08_22 :
    Closed765 (decode (actCode 5 (decodeMask 13961))) := by
  have he : decode (actCode 5 (decodeMask 13961)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL282 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨282, by decide +kernel⟩)))

theorem closed_08_23 :
    Closed765 (decode (actCode 19 (decodeMask 13964))) := by
  have he : decode (actCode 19 (decodeMask 13964)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR039 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR039)))⟩)))))))))))))

theorem closed_08_24 :
    Closed765 (decode (actCode 4 (decodeMask 13965))) := by
  have he : decode (actCode 4 (decodeMask 13965)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR040 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR040)⟩))))))))))))))

theorem closed_08_25 :
    Closed765 (decode (actCode 8 (decodeMask 14476))) := by
  have he : decode (actCode 8 (decodeMask 14476)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR600 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR600)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_08_26 :
    Closed765 (decode (actCode 4 (decodeMask 14477))) := by
  have he : decode (actCode 4 (decodeMask 14477)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR500 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR500)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_08_27 :
    Closed765 (decode (actCode 5 (decodeMask 14860))) := by
  have he : decode (actCode 5 (decodeMask 14860)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR041 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR041))⟩))))))))))))))

theorem closed_08_28 :
    Closed765 (decode (actCode 5 (decodeMask 14861))) := by
  have he : decode (actCode 5 (decodeMask 14861)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR042 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR042)))⟩))))))))))))))

theorem closed_08_29 :
    Closed765 (decode (actCode 4 (decodeMask 14977))) := by
  have he : decode (actCode 4 (decodeMask 14977)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC045 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨333, by decide +kernel⟩)))

theorem closed_08_30 :
    Closed765 (decode (actCode 4 (decodeMask 14981))) := by
  have he : decode (actCode 4 (decodeMask 14981)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL276 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨276, by decide +kernel⟩)))

theorem closed_08_31 :
    Closed765 (decode (actCode 14 (decodeMask 14984))) := by
  have he : decode (actCode 14 (decodeMask 14984)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR043 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR043)))⟩))))))))))))))

theorem checkedMasks08_closed (m : ℕ) (hm : m ∈ checkedMasks08) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks08, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_08_0
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_1
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_2
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_3
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_4
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_5
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_6
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_7
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_9
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_10
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_11
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_12
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_13
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_14
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_15
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_16
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_17
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_18
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_19
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_20
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_21
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_22
  · refine ⟨sigma 19, ?_⟩
    rw [← decode_actCode]
    exact closed_08_23
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_24
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_08_25
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_26
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_27
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_08_28
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_29
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_08_30
  · refine ⟨sigma 14, ?_⟩
    rw [← decode_actCode]
    exact closed_08_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks08_closed
