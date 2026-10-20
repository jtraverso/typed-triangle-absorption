/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks11

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_11_0 :
    Closed765 (decode (actCode 1 (decodeMask 67075))) := by
  have he : decode (actCode 1 (decodeMask 67075)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL113 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨113, by decide +kernel⟩)))

theorem closed_11_1 :
    Closed765 (decode (actCode 3 (decodeMask 67080))) := by
  have he : decode (actCode 3 (decodeMask 67080)) =
      PaddedComponents.KQ11 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (identity_perm_family PaddedComponents.KQ11))))))))))⟩))))

theorem closed_11_2 :
    Closed765 (decode (actCode 3 (decodeMask 67081))) := by
  have he : decode (actCode 3 (decodeMask 67081)) =
      PaddedComponents.KE3 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PaddedComponents.KE3)))⟩))))))

theorem closed_11_3 :
    Closed765 (decode (actCode 7 (decodeMask 67082))) := by
  have he : decode (actCode 7 (decodeMask 67082)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR054 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR054)))⟩)))))))))))))))))

theorem closed_11_4 :
    Closed765 (decode (actCode 3 (decodeMask 67083))) := by
  have he : decode (actCode 3 (decodeMask 67083)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR055 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR055)))⟩)))))))))))))))))

theorem closed_11_5 :
    Closed765 (decode (actCode 7 (decodeMask 67088))) := by
  have he : decode (actCode 7 (decodeMask 67088)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL037 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨37, by decide +kernel⟩)))

theorem closed_11_6 :
    Closed765 (decode (actCode 7 (decodeMask 67089))) := by
  have he : decode (actCode 7 (decodeMask 67089)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL129 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨129, by decide +kernel⟩)))

theorem closed_11_7 :
    Closed765 (decode (actCode 7 (decodeMask 67090))) := by
  have he : decode (actCode 7 (decodeMask 67090)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL094 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨94, by decide +kernel⟩)))

theorem closed_11_8 :
    Closed765 (decode (actCode 1 (decodeMask 67091))) := by
  have he : decode (actCode 1 (decodeMask 67091)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL191 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨191, by decide +kernel⟩)))

theorem closed_11_9 :
    Closed765 (decode (actCode 7 (decodeMask 67096))) := by
  have he : decode (actCode 7 (decodeMask 67096)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR056 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR056)⟩))))))))))))))))))

theorem closed_11_10 :
    Closed765 (decode (actCode 3 (decodeMask 67097))) := by
  have he : decode (actCode 3 (decodeMask 67097)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR057 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR057))⟩))))))))))))))))))

theorem closed_11_11 :
    Closed765 (decode (actCode 7 (decodeMask 67098))) := by
  have he : decode (actCode 7 (decodeMask 67098)) =
      PaddedComponents.FM08 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM08, (by exact List.get_mem PaddedComponents.monoList ⟨7, by decide +kernel⟩), identity_perm_family PaddedComponents.FM08⟩)))))))))))))))

theorem closed_11_12 :
    Closed765 (decode (actCode 1 (decodeMask 67099))) := by
  have he : decode (actCode 1 (decodeMask 67099)) =
      PaddedComponents.FM12 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM12, (by exact List.get_mem PaddedComponents.monoList ⟨11, by decide +kernel⟩), identity_perm_family PaddedComponents.FM12⟩)))))))))))))))

theorem closed_11_13 :
    Closed765 (decode (actCode 12 (decodeMask 67104))) := by
  have he : decode (actCode 12 (decodeMask 67104)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case14.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨14, rfl⟩

theorem closed_11_14 :
    Closed765 (decode (actCode 6 (decodeMask 67120))) := by
  have he : decode (actCode 6 (decodeMask 67120)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL104 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨104, by decide +kernel⟩)))

theorem closed_11_15 :
    Closed765 (decode (actCode 3 (decodeMask 67137))) := by
  have he : decode (actCode 3 (decodeMask 67137)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL142 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨142, by decide +kernel⟩)))

theorem closed_11_16 :
    Closed765 (decode (actCode 7 (decodeMask 67138))) := by
  have he : decode (actCode 7 (decodeMask 67138)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC048 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨350, by decide +kernel⟩)))

theorem closed_11_17 :
    Closed765 (decode (actCode 1 (decodeMask 67139))) := by
  have he : decode (actCode 1 (decodeMask 67139)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL212 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨212, by decide +kernel⟩)))

theorem closed_11_18 :
    Closed765 (decode (actCode 7 (decodeMask 67144))) := by
  have he : decode (actCode 7 (decodeMask 67144)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC049 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨351, by decide +kernel⟩)))

theorem closed_11_19 :
    Closed765 (decode (actCode 3 (decodeMask 67145))) := by
  have he : decode (actCode 3 (decodeMask 67145)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL186 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨186, by decide +kernel⟩)))

theorem closed_11_20 :
    Closed765 (decode (actCode 7 (decodeMask 67146))) := by
  have he : decode (actCode 7 (decodeMask 67146)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR058 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR058)))⟩))))))))))))))))))

theorem closed_11_21 :
    Closed765 (decode (actCode 3 (decodeMask 67147))) := by
  have he : decode (actCode 3 (decodeMask 67147)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR059 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR059)))⟩))))))))))))))))))

theorem closed_11_22 :
    Closed765 (decode (actCode 7 (decodeMask 67152))) := by
  have he : decode (actCode 7 (decodeMask 67152)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL101 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨101, by decide +kernel⟩)))

theorem closed_11_23 :
    Closed765 (decode (actCode 7 (decodeMask 67153))) := by
  have he : decode (actCode 7 (decodeMask 67153)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL214 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨214, by decide +kernel⟩)))

theorem closed_11_24 :
    Closed765 (decode (actCode 7 (decodeMask 67154))) := by
  have he : decode (actCode 7 (decodeMask 67154)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL185 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨185, by decide +kernel⟩)))

theorem closed_11_25 :
    Closed765 (decode (actCode 1 (decodeMask 67155))) := by
  have he : decode (actCode 1 (decodeMask 67155)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL266 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨266, by decide +kernel⟩)))

theorem closed_11_26 :
    Closed765 (decode (actCode 7 (decodeMask 67160))) := by
  have he : decode (actCode 7 (decodeMask 67160)) =
      PaddedComponents.KCX2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KCX2))⟩)))))))))

theorem closed_11_27 :
    Closed765 (decode (actCode 3 (decodeMask 67161))) := by
  have he : decode (actCode 3 (decodeMask 67161)) =
      PaddedComponents.KCT2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KCT2))⟩))))))))))

theorem closed_11_28 :
    Closed765 (decode (actCode 7 (decodeMask 67162))) := by
  have he : decode (actCode 7 (decodeMask 67162)) =
      PaddedComponents.FM13 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM13, (by exact List.get_mem PaddedComponents.monoList ⟨12, by decide +kernel⟩), identity_perm_family PaddedComponents.FM13⟩)))))))))))))))

theorem closed_11_29 :
    Closed765 (decode (actCode 1 (decodeMask 67163))) := by
  have he : decode (actCode 1 (decodeMask 67163)) =
      PaddedComponents.FM19 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM19, (by exact List.get_mem PaddedComponents.monoList ⟨18, by decide +kernel⟩), identity_perm_family PaddedComponents.FM19⟩)))))))))))))))

theorem closed_11_30 :
    Closed765 (decode (actCode 6 (decodeMask 67216))) := by
  have he : decode (actCode 6 (decodeMask 67216)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL137 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨137, by decide +kernel⟩)))

theorem closed_11_31 :
    Closed765 (decode (actCode 6 (decodeMask 67248))) := by
  have he : decode (actCode 6 (decodeMask 67248)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALT002 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨355, by decide +kernel⟩)))

theorem checkedMasks11_closed (m : ℕ) (hm : m ∈ checkedMasks11) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks11, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_0
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_1
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_2
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_3
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_4
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_5
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_6
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_7
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_8
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_9
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_10
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_11
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_12
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_11_13
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_11_14
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_15
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_16
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_17
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_18
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_19
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_20
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_21
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_22
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_23
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_24
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_25
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_26
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_11_27
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_11_28
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_11_29
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_11_30
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_11_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks11_closed
