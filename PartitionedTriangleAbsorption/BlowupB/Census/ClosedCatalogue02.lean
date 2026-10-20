/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks02

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_02_0 :
    Closed765 (decode (actCode 5 (decodeMask 2312))) := by
  have he : decode (actCode 5 (decodeMask 2312)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL012 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨12, by decide +kernel⟩)))

theorem closed_02_1 :
    Closed765 (decode (actCode 5 (decodeMask 2313))) := by
  have he : decode (actCode 5 (decodeMask 2313)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL022 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨22, by decide +kernel⟩)))

theorem closed_02_2 :
    Closed765 (decode (actCode 4 (decodeMask 2316))) := by
  have he : decode (actCode 4 (decodeMask 2316)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC005 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨303, by decide +kernel⟩)))

theorem closed_02_3 :
    Closed765 (decode (actCode 4 (decodeMask 2317))) := by
  have he : decode (actCode 4 (decodeMask 2317)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL071 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨71, by decide +kernel⟩)))

theorem closed_02_4 :
    Closed765 (decode (actCode 6 (decodeMask 2320))) := by
  have he : decode (actCode 6 (decodeMask 2320)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case07.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨7, rfl⟩

theorem closed_02_5 :
    Closed765 (decode (actCode 6 (decodeMask 2352))) := by
  have he : decode (actCode 6 (decodeMask 2352)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC006 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨340, by decide +kernel⟩)))

theorem closed_02_6 :
    Closed765 (decode (actCode 3 (decodeMask 2561))) := by
  have he : decode (actCode 3 (decodeMask 2561)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL002 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨2, by decide +kernel⟩)))

theorem closed_02_7 :
    Closed765 (decode (actCode 1 (decodeMask 2563))) := by
  have he : decode (actCode 1 (decodeMask 2563)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL024 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨24, by decide +kernel⟩)))

theorem closed_02_8 :
    Closed765 (decode (actCode 4 (decodeMask 2564))) := by
  have he : decode (actCode 4 (decodeMask 2564)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL014 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨14, by decide +kernel⟩)))

theorem closed_02_9 :
    Closed765 (decode (actCode 4 (decodeMask 2565))) := by
  have he : decode (actCode 4 (decodeMask 2565)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL025 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨25, by decide +kernel⟩)))

theorem closed_02_10 :
    Closed765 (decode (actCode 3 (decodeMask 2568))) := by
  have he : decode (actCode 3 (decodeMask 2568)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC007 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨304, by decide +kernel⟩)))

theorem closed_02_11 :
    Closed765 (decode (actCode 3 (decodeMask 2569))) := by
  have he : decode (actCode 3 (decodeMask 2569)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL019 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨19, by decide +kernel⟩)))

theorem closed_02_12 :
    Closed765 (decode (actCode 3 (decodeMask 2570))) := by
  have he : decode (actCode 3 (decodeMask 2570)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC008 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨305, by decide +kernel⟩)))

theorem closed_02_13 :
    Closed765 (decode (actCode 3 (decodeMask 2571))) := by
  have he : decode (actCode 3 (decodeMask 2571)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL068 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨68, by decide +kernel⟩)))

theorem closed_02_14 :
    Closed765 (decode (actCode 5 (decodeMask 2572))) := by
  have he : decode (actCode 5 (decodeMask 2572)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC009 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨306, by decide +kernel⟩)))

theorem closed_02_15 :
    Closed765 (decode (actCode 5 (decodeMask 2573))) := by
  have he : decode (actCode 5 (decodeMask 2573)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL069 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨69, by decide +kernel⟩)))

theorem closed_02_16 :
    Closed765 (decode (actCode 1 (decodeMask 2577))) := by
  have he : decode (actCode 1 (decodeMask 2577)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL042 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨42, by decide +kernel⟩)))

theorem closed_02_17 :
    Closed765 (decode (actCode 1 (decodeMask 2579))) := by
  have he : decode (actCode 1 (decodeMask 2579)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL084 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨84, by decide +kernel⟩)))

theorem closed_02_18 :
    Closed765 (decode (actCode 6 (decodeMask 2584))) := by
  have he : decode (actCode 6 (decodeMask 2584)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC010 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨307, by decide +kernel⟩)))

theorem closed_02_19 :
    Closed765 (decode (actCode 3 (decodeMask 2585))) := by
  have he : decode (actCode 3 (decodeMask 2585)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL086 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨86, by decide +kernel⟩)))

theorem closed_02_20 :
    Closed765 (decode (actCode 1 (decodeMask 2586))) := by
  have he : decode (actCode 1 (decodeMask 2586)) =
      PaddedCharge.KCb := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (identity_perm_family PaddedCharge.KCb)⟩)))))))))))))

theorem closed_02_21 :
    Closed765 (decode (actCode 1 (decodeMask 2587))) := by
  have he : decode (actCode 1 (decodeMask 2587)) =
      PaddedNoCommon.KT2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedNoCommon.KT2)⟩))))))))))))))))

theorem closed_02_22 :
    Closed765 (decode (actCode 4 (decodeMask 2689))) := by
  have he : decode (actCode 4 (decodeMask 2689)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL043 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨43, by decide +kernel⟩)))

theorem closed_02_23 :
    Closed765 (decode (actCode 4 (decodeMask 2692))) := by
  have he : decode (actCode 4 (decodeMask 2692)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC011 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨308, by decide +kernel⟩)))

theorem closed_02_24 :
    Closed765 (decode (actCode 4 (decodeMask 2693))) := by
  have he : decode (actCode 4 (decodeMask 2693)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL085 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨85, by decide +kernel⟩)))

theorem closed_02_25 :
    Closed765 (decode (actCode 5 (decodeMask 2696))) := by
  have he : decode (actCode 5 (decodeMask 2696)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC012 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨309, by decide +kernel⟩)))

theorem closed_02_26 :
    Closed765 (decode (actCode 5 (decodeMask 2697))) := by
  have he : decode (actCode 5 (decodeMask 2697)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL087 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨87, by decide +kernel⟩)))

theorem closed_02_27 :
    Closed765 (decode (actCode 4 (decodeMask 2700))) := by
  have he : decode (actCode 4 (decodeMask 2700)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC013 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨310, by decide +kernel⟩)))

theorem closed_02_28 :
    Closed765 (decode (actCode 4 (decodeMask 2701))) := by
  have he : decode (actCode 4 (decodeMask 2701)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL151 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨151, by decide +kernel⟩)))

theorem closed_02_29 :
    Closed765 (decode (actCode 12 (decodeMask 2704))) := by
  have he : decode (actCode 12 (decodeMask 2704)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL059 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨59, by decide +kernel⟩)))

theorem closed_02_30 :
    Closed765 (decode (actCode 8 (decodeMask 2720))) := by
  have he : decode (actCode 8 (decodeMask 2720)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC014 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨341, by decide +kernel⟩)))

theorem closed_02_31 :
    Closed765 (decode (actCode 12 (decodeMask 2736))) := by
  have he : decode (actCode 12 (decodeMask 2736)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC015 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨311, by decide +kernel⟩)))

theorem checkedMasks02_closed (m : ℕ) (hm : m ∈ checkedMasks02) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks02, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_0
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_1
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_2
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_3
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_02_4
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_02_5
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_6
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_02_7
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_9
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_10
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_11
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_12
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_13
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_14
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_15
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_02_16
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_02_17
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_02_18
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_02_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_02_20
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_02_21
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_22
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_23
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_24
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_25
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_02_26
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_27
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_02_28
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_02_29
  · refine ⟨sigma 8, ?_⟩
    rw [← decode_actCode]
    exact closed_02_30
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_02_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks02_closed
