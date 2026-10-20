/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks06

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_06_0 :
    Closed765 (decode (actCode 18 (decodeMask 7820))) := by
  have he : decode (actCode 18 (decodeMask 7820)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR022 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR022)))⟩)))))))))

theorem closed_06_1 :
    Closed765 (decode (actCode 4 (decodeMask 7821))) := by
  have he : decode (actCode 4 (decodeMask 7821)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR023 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR023)))⟩)))))))))

theorem closed_06_2 :
    Closed765 (decode (actCode 12 (decodeMask 9352))) := by
  have he : decode (actCode 12 (decodeMask 9352)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL045 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨45, by decide +kernel⟩)))

theorem closed_06_3 :
    Closed765 (decode (actCode 5 (decodeMask 9353))) := by
  have he : decode (actCode 5 (decodeMask 9353)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL125 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨125, by decide +kernel⟩)))

theorem closed_06_4 :
    Closed765 (decode (actCode 12 (decodeMask 9356))) := by
  have he : decode (actCode 12 (decodeMask 9356)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR024 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR024)⟩))))))))))

theorem closed_06_5 :
    Closed765 (decode (actCode 4 (decodeMask 9357))) := by
  have he : decode (actCode 4 (decodeMask 9357)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR025 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR025))⟩))))))))))

theorem closed_06_6 :
    Closed765 (decode (actCode 3 (decodeMask 9729))) := by
  have he : decode (actCode 3 (decodeMask 9729)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL051 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨51, by decide +kernel⟩)))

theorem closed_06_7 :
    Closed765 (decode (actCode 1 (decodeMask 9731))) := by
  have he : decode (actCode 1 (decodeMask 9731)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL110 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨110, by decide +kernel⟩)))

theorem closed_06_8 :
    Closed765 (decode (actCode 12 (decodeMask 9732))) := by
  have he : decode (actCode 12 (decodeMask 9732)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL049 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨49, by decide +kernel⟩)))

theorem closed_06_9 :
    Closed765 (decode (actCode 4 (decodeMask 9733))) := by
  have he : decode (actCode 4 (decodeMask 9733)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL118 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨118, by decide +kernel⟩)))

theorem closed_06_10 :
    Closed765 (decode (actCode 12 (decodeMask 9736))) := by
  have he : decode (actCode 12 (decodeMask 9736)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC031 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨322, by decide +kernel⟩)))

theorem closed_06_11 :
    Closed765 (decode (actCode 3 (decodeMask 9737))) := by
  have he : decode (actCode 3 (decodeMask 9737)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL095 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨95, by decide +kernel⟩)))

theorem closed_06_12 :
    Closed765 (decode (actCode 6 (decodeMask 9738))) := by
  have he : decode (actCode 6 (decodeMask 9738)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC032 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨323, by decide +kernel⟩)))

theorem closed_06_13 :
    Closed765 (decode (actCode 3 (decodeMask 9739))) := by
  have he : decode (actCode 3 (decodeMask 9739)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL162 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨162, by decide +kernel⟩)))

theorem closed_06_14 :
    Closed765 (decode (actCode 12 (decodeMask 9740))) := by
  have he : decode (actCode 12 (decodeMask 9740)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC033 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨324, by decide +kernel⟩)))

theorem closed_06_15 :
    Closed765 (decode (actCode 5 (decodeMask 9741))) := by
  have he : decode (actCode 5 (decodeMask 9741)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL163 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨163, by decide +kernel⟩)))

theorem closed_06_16 :
    Closed765 (decode (actCode 1 (decodeMask 9747))) := by
  have he : decode (actCode 1 (decodeMask 9747)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL188 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨188, by decide +kernel⟩)))

theorem closed_06_17 :
    Closed765 (decode (actCode 6 (decodeMask 9752))) := by
  have he : decode (actCode 6 (decodeMask 9752)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC034 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨325, by decide +kernel⟩)))

theorem closed_06_18 :
    Closed765 (decode (actCode 3 (decodeMask 9753))) := by
  have he : decode (actCode 3 (decodeMask 9753)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL202 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨202, by decide +kernel⟩)))

theorem closed_06_19 :
    Closed765 (decode (actCode 6 (decodeMask 9754))) := by
  have he : decode (actCode 6 (decodeMask 9754)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL193 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨193, by decide +kernel⟩)))

theorem closed_06_20 :
    Closed765 (decode (actCode 1 (decodeMask 9755))) := by
  have he : decode (actCode 1 (decodeMask 9755)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL241 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨241, by decide +kernel⟩)))

theorem closed_06_21 :
    Closed765 (decode (actCode 12 (decodeMask 9856))) := by
  have he : decode (actCode 12 (decodeMask 9856)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL046 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨46, by decide +kernel⟩)))

theorem closed_06_22 :
    Closed765 (decode (actCode 4 (decodeMask 9857))) := by
  have he : decode (actCode 4 (decodeMask 9857)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL146 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨146, by decide +kernel⟩)))

theorem closed_06_23 :
    Closed765 (decode (actCode 12 (decodeMask 9860))) := by
  have he : decode (actCode 12 (decodeMask 9860)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC035 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨326, by decide +kernel⟩)))

theorem closed_06_24 :
    Closed765 (decode (actCode 4 (decodeMask 9861))) := by
  have he : decode (actCode 4 (decodeMask 9861)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL196 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨196, by decide +kernel⟩)))

theorem closed_06_25 :
    Closed765 (decode (actCode 12 (decodeMask 9864))) := by
  have he : decode (actCode 12 (decodeMask 9864)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC036 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨327, by decide +kernel⟩)))

theorem closed_06_26 :
    Closed765 (decode (actCode 5 (decodeMask 9865))) := by
  have he : decode (actCode 5 (decodeMask 9865)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL203 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨203, by decide +kernel⟩)))

theorem closed_06_27 :
    Closed765 (decode (actCode 12 (decodeMask 9868))) := by
  have he : decode (actCode 12 (decodeMask 9868)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR026 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR026)))⟩))))))))))

theorem closed_06_28 :
    Closed765 (decode (actCode 4 (decodeMask 9869))) := by
  have he : decode (actCode 4 (decodeMask 9869)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR027 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR027)))⟩))))))))))

theorem closed_06_29 :
    Closed765 (decode (actCode 6 (decodeMask 9872))) := by
  have he : decode (actCode 6 (decodeMask 9872)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL119 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨119, by decide +kernel⟩)))

theorem closed_06_30 :
    Closed765 (decode (actCode 12 (decodeMask 9888))) := by
  have he : decode (actCode 12 (decodeMask 9888)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALC037 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨346, by decide +kernel⟩)))

theorem closed_06_31 :
    Closed765 (decode (actCode 6 (decodeMask 9904))) := by
  have he : decode (actCode 6 (decodeMask 9904)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BALT000 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨353, by decide +kernel⟩)))

theorem checkedMasks06_closed (m : ℕ) (hm : m ∈ checkedMasks06) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks06, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_06_0
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_1
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_2
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_06_3
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_4
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_5
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_06_6
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_06_7
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_9
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_10
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_06_11
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_06_12
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_06_13
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_14
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_06_15
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_06_16
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_06_17
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_06_18
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_06_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_06_20
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_21
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_22
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_23
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_24
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_25
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_06_26
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_27
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_06_28
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_06_29
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_06_30
  · refine ⟨sigma 6, ?_⟩
    rw [← decode_actCode]
    exact closed_06_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks06_closed
