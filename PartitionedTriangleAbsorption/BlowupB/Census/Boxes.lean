/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Universe

@[expose] public section

/-! A kernel-checked reduction from all admissible families to 26 boxes.
The constants were generated, but every inclusion is checked by Lean. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus
open Finset

def box : Fin 26 → Finset (Fin 20) :=
  ![{0,10,11,12,13,14,15,16,17,18,19},
    {0,1,13,14,15,16,17,18,19},
    {0,1,2,4,7,10,12,15,16,17,18,19},
    {0,1,3,4,9,10,11,13,16,17,18,19},
    {4,7,8,9,10,16,17,18,19},
    {0,2,3,7,8,9,10,16,17,18,19},
    {0,2,10,11,12,14,15,18,19},
    {0,1,2,5,14,15,18,19},
    {4,5,8,9,10,11,18,19},
    {0,2,3,8,9,10,11,18,19},
    {0,1,2,4,5,10,11,18,19},
    {0,2,3,7,9,10,11,12,13,15,16,19},
    {5,6,7,9,13,15,16,19},
    {0,1,3,6,9,13,15,16,19},
    {0,1,2,5,7,13,15,16,19},
    {4,6,7,9,10,12,15,16,19},
    {0,1,3,4,6,9,10,12,15,16,19},
    {4,5,7,9,10,11,13,16,19},
    {0,1,2,4,5,7,10,11,13,16,19},
    {0,3,10,11,12,13,14,16,17},
    {0,1,3,6,13,14,16,17},
    {4,6,7,8,10,12,16,17},
    {0,2,3,7,8,10,12,16,17},
    {0,1,3,4,6,10,12,16,17},
    {0,2,3,8,10,11,12,14},
    {5,6,8,14}]

def choiceTable : Fin 256 → Fin 26 :=
  ![0,3,11,19,2,4,11,21,6,8,11,24,11,11,11,11,1,3,12,20,2,4,12,21,7,8,12,25,12,12,12,12,2,3,15,21,2,4,15,21,2,4,15,21,2,4,15,15,3,3,3,3,2,4,4,4,8,8,8,8,17,17,17,17,0,3,11,19,2,5,11,22,6,9,11,24,11,11,11,11,0,3,11,19,2,5,11,22,6,9,11,24,11,11,11,11,0,3,11,19,2,5,11,22,2,5,11,22,2,5,11,11,0,3,3,3,2,5,5,5,6,9,9,9,11,11,11,11,0,3,11,19,0,3,11,19,0,3,11,19,0,3,11,11,1,3,13,20,1,3,13,20,1,3,13,20,1,3,13,13,2,3,16,23,2,3,16,23,2,3,16,23,2,3,16,16,3,3,3,3,2,3,3,3,3,3,3,3,3,3,3,3,0,0,0,0,2,2,2,2,6,6,6,6,11,11,11,11,1,1,1,1,2,2,2,2,7,7,7,7,14,14,14,14,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,2,2,2,2,10,10,10,10,18,18,18,18]

def choice (a b c d : Fin 4) : Fin 26 :=
  choiceTable ⟨a.val*64+b.val*16+c.val*4+d.val, by omega⟩

theorem box_contains_00 : ∀ c d : Fin 4,
    forbiddenBox ![0,0,c,d] ⊆ box (choice 0 0 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_01 : ∀ c d : Fin 4,
    forbiddenBox ![0,1,c,d] ⊆ box (choice 0 1 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_02 : ∀ c d : Fin 4,
    forbiddenBox ![0,2,c,d] ⊆ box (choice 0 2 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_03 : ∀ c d : Fin 4,
    forbiddenBox ![0,3,c,d] ⊆ box (choice 0 3 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_10 : ∀ c d : Fin 4,
    forbiddenBox ![1,0,c,d] ⊆ box (choice 1 0 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_11 : ∀ c d : Fin 4,
    forbiddenBox ![1,1,c,d] ⊆ box (choice 1 1 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_12 : ∀ c d : Fin 4,
    forbiddenBox ![1,2,c,d] ⊆ box (choice 1 2 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_13 : ∀ c d : Fin 4,
    forbiddenBox ![1,3,c,d] ⊆ box (choice 1 3 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_20 : ∀ c d : Fin 4,
    forbiddenBox ![2,0,c,d] ⊆ box (choice 2 0 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_21 : ∀ c d : Fin 4,
    forbiddenBox ![2,1,c,d] ⊆ box (choice 2 1 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_22 : ∀ c d : Fin 4,
    forbiddenBox ![2,2,c,d] ⊆ box (choice 2 2 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_23 : ∀ c d : Fin 4,
    forbiddenBox ![2,3,c,d] ⊆ box (choice 2 3 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_30 : ∀ c d : Fin 4,
    forbiddenBox ![3,0,c,d] ⊆ box (choice 3 0 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_31 : ∀ c d : Fin 4,
    forbiddenBox ![3,1,c,d] ⊆ box (choice 3 1 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_32 : ∀ c d : Fin 4,
    forbiddenBox ![3,2,c,d] ⊆ box (choice 3 2 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem box_contains_33 : ∀ c d : Fin 4,
    forbiddenBox ![3,3,c,d] ⊆ box (choice 3 3 c d) := by
  intro c d
  fin_cases c <;> fin_cases d <;> decide +kernel

theorem forbiddenBox_subset_box (f : Fin 4 → Fin 4) :
    forbiddenBox f ⊆ box (choice (f 0) (f 1) (f 2) (f 3)) := by
  have hf : f = ![f 0,f 1,f 2,f 3] := by
    funext i
    fin_cases i <;> rfl
  have h : ∀ a b c d : Fin 4, forbiddenBox ![a,b,c,d] ⊆ box (choice a b c d) := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact box_contains_00
    · exact box_contains_01
    · exact box_contains_02
    · exact box_contains_03
    · exact box_contains_10
    · exact box_contains_11
    · exact box_contains_12
    · exact box_contains_13
    · exact box_contains_20
    · exact box_contains_21
    · exact box_contains_22
    · exact box_contains_23
    · exact box_contains_30
    · exact box_contains_31
    · exact box_contains_32
    · exact box_contains_33
  simpa only [← hf] using h (f 0) (f 1) (f 2) (f 3)

theorem box_card_le : ∀ b : Fin 26, (box b).card ≤ 12 := by decide +kernel

theorem admissible_subset_one_of_26 (C : Finset (Fin 20)) (hC : Admissible C) :
    ∃ b : Fin 26, C ∈ (box b).powerset := by
  obtain ⟨f,hf⟩ := admissible_subset_box C hC
  exact ⟨choice (f 0) (f 1) (f 2) (f 3),
    mem_powerset.mpr (hf.trans (forbiddenBox_subset_box f))⟩

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.admissible_subset_one_of_26
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.box_card_le
