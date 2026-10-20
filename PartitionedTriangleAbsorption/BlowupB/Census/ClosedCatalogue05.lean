/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks05

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_05_0 :
    Closed765 (decode (actCode 4 (decodeMask 6157))) := by
  have he : decode (actCode 4 (decodeMask 6157)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL081 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨81, by decide +kernel⟩)))

theorem closed_05_1 :
    Closed765 (decode (actCode 2 (decodeMask 6273))) := by
  have he : decode (actCode 2 (decodeMask 6273)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL048 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨48, by decide +kernel⟩)))

theorem closed_05_2 :
    Closed765 (decode (actCode 2 (decodeMask 6277))) := by
  have he : decode (actCode 2 (decodeMask 6277)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL092 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨92, by decide +kernel⟩)))

theorem closed_05_3 :
    Closed765 (decode (actCode 18 (decodeMask 6280))) := by
  have he : decode (actCode 18 (decodeMask 6280)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL061 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨61, by decide +kernel⟩)))

theorem closed_05_4 :
    Closed765 (decode (actCode 5 (decodeMask 6281))) := by
  have he : decode (actCode 5 (decodeMask 6281)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL123 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨123, by decide +kernel⟩)))

theorem closed_05_5 :
    Closed765 (decode (actCode 4 (decodeMask 6284))) := by
  have he : decode (actCode 4 (decodeMask 6284)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC026 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨317, by decide +kernel⟩)))

theorem closed_05_6 :
    Closed765 (decode (actCode 4 (decodeMask 6285))) := by
  have he : decode (actCode 4 (decodeMask 6285)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL161 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨161, by decide +kernel⟩)))

theorem closed_05_7 :
    Closed765 (decode (actCode 4 (decodeMask 6401))) := by
  have he : decode (actCode 4 (decodeMask 6401)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case10.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨10, rfl⟩

theorem closed_05_8 :
    Closed765 (decode (actCode 4 (decodeMask 6405))) := by
  have he : decode (actCode 4 (decodeMask 6405)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL105 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨105, by decide +kernel⟩)))

theorem closed_05_9 :
    Closed765 (decode (actCode 4 (decodeMask 6412))) := by
  have he : decode (actCode 4 (decodeMask 6412)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC027 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨318, by decide +kernel⟩)))

theorem closed_05_10 :
    Closed765 (decode (actCode 4 (decodeMask 6413))) := by
  have he : decode (actCode 4 (decodeMask 6413)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL168 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨168, by decide +kernel⟩)))

theorem closed_05_11 :
    Closed765 (decode (actCode 18 (decodeMask 6784))) := by
  have he : decode (actCode 18 (decodeMask 6784)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL060 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨60, by decide +kernel⟩)))

theorem closed_05_12 :
    Closed765 (decode (actCode 4 (decodeMask 6785))) := by
  have he : decode (actCode 4 (decodeMask 6785)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL147 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨147, by decide +kernel⟩)))

theorem closed_05_13 :
    Closed765 (decode (actCode 18 (decodeMask 6788))) := by
  have he : decode (actCode 18 (decodeMask 6788)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC028 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨319, by decide +kernel⟩)))

theorem closed_05_14 :
    Closed765 (decode (actCode 4 (decodeMask 6789))) := by
  have he : decode (actCode 4 (decodeMask 6789)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL200 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨200, by decide +kernel⟩)))

theorem closed_05_15 :
    Closed765 (decode (actCode 4 (decodeMask 6796))) := by
  have he : decode (actCode 4 (decodeMask 6796)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC029 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨320, by decide +kernel⟩)))

theorem closed_05_16 :
    Closed765 (decode (actCode 4 (decodeMask 6797))) := by
  have he : decode (actCode 4 (decodeMask 6797)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL244 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨244, by decide +kernel⟩)))

theorem closed_05_17 :
    Closed765 (decode (actCode 4 (decodeMask 7181))) := by
  have he : decode (actCode 4 (decodeMask 7181)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR016 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR016)⟩))))))))

theorem closed_05_18 :
    Closed765 (decode (actCode 18 (decodeMask 7297))) := by
  have he : decode (actCode 18 (decodeMask 7297)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL079 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨79, by decide +kernel⟩)))

theorem closed_05_19 :
    Closed765 (decode (actCode 18 (decodeMask 7301))) := by
  have he : decode (actCode 18 (decodeMask 7301)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR017 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR017))⟩))))))))

theorem closed_05_20 :
    Closed765 (decode (actCode 18 (decodeMask 7304))) := by
  have he : decode (actCode 18 (decodeMask 7304)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL078 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨78, by decide +kernel⟩)))

theorem closed_05_21 :
    Closed765 (decode (actCode 18 (decodeMask 7305))) := by
  have he : decode (actCode 18 (decodeMask 7305)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL179 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨179, by decide +kernel⟩)))

theorem closed_05_22 :
    Closed765 (decode (actCode 18 (decodeMask 7308))) := by
  have he : decode (actCode 18 (decodeMask 7308)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR018 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR018)))⟩))))))))

theorem closed_05_23 :
    Closed765 (decode (actCode 4 (decodeMask 7309))) := by
  have he : decode (actCode 4 (decodeMask 7309)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR019 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR019)))⟩))))))))

theorem closed_05_24 :
    Closed765 (decode (actCode 18 (decodeMask 7425))) := by
  have he : decode (actCode 18 (decodeMask 7425)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case11.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨11, rfl⟩

theorem closed_05_25 :
    Closed765 (decode (actCode 18 (decodeMask 7429))) := by
  have he : decode (actCode 18 (decodeMask 7429)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL180 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨180, by decide +kernel⟩)))

theorem closed_05_26 :
    Closed765 (decode (actCode 18 (decodeMask 7436))) := by
  have he : decode (actCode 18 (decodeMask 7436)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR020 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR020)⟩)))))))))

theorem closed_05_27 :
    Closed765 (decode (actCode 4 (decodeMask 7437))) := by
  have he : decode (actCode 4 (decodeMask 7437)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR021 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR021))⟩)))))))))

theorem closed_05_28 :
    Closed765 (decode (actCode 18 (decodeMask 7808))) := by
  have he : decode (actCode 18 (decodeMask 7808)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL077 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨77, by decide +kernel⟩)))

theorem closed_05_29 :
    Closed765 (decode (actCode 18 (decodeMask 7809))) := by
  have he : decode (actCode 18 (decodeMask 7809)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL178 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨178, by decide +kernel⟩)))

theorem closed_05_30 :
    Closed765 (decode (actCode 18 (decodeMask 7812))) := by
  have he : decode (actCode 18 (decodeMask 7812)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC030 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨321, by decide +kernel⟩)))

theorem closed_05_31 :
    Closed765 (decode (actCode 18 (decodeMask 7813))) := by
  have he : decode (actCode 18 (decodeMask 7813)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL265 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨265, by decide +kernel⟩)))

theorem checkedMasks05_closed (m : ℕ) (hm : m ∈ checkedMasks05) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks05, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_0
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_05_1
  · refine ⟨sigma 2, ?_⟩
    rw [← decode_actCode]
    exact closed_05_2
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_3
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_05_4
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_5
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_6
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_7
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_9
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_10
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_11
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_12
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_13
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_14
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_15
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_16
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_17
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_18
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_19
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_20
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_21
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_23
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_24
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_25
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_26
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_05_27
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_28
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_29
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_30
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_05_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks05_closed
