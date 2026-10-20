/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Representatives

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus
open Finset

def permValues : Fin 24 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],
    ![0,1,3,2],
    ![0,2,1,3],
    ![0,2,3,1],
    ![0,3,1,2],
    ![0,3,2,1],
    ![1,0,2,3],
    ![1,0,3,2],
    ![1,2,0,3],
    ![1,2,3,0],
    ![1,3,0,2],
    ![1,3,2,0],
    ![2,0,1,3],
    ![2,0,3,1],
    ![2,1,0,3],
    ![2,1,3,0],
    ![2,3,0,1],
    ![2,3,1,0],
    ![3,0,1,2],
    ![3,0,2,1],
    ![3,1,0,2],
    ![3,1,2,0],
    ![3,2,0,1],
    ![3,2,1,0]]

theorem permValues_bijective : ∀ i, Function.Bijective (permValues i) := by
  decide +kernel

noncomputable def sigma (i : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (permValues i) (permValues_bijective i)

theorem sigma_covers (s : Equiv.Perm (Fin 4)) : ∃ i, sigma i = s := by
  have hf : (s : Fin 4 → Fin 4) = ![s 0,s 1,s 2,s 3] := by
    funext i
    fin_cases i <;> rfl
  have ht : ∀ a b c d : Fin 4, Function.Injective ![a,b,c,d] →
      ∃ i : Fin 24, permValues i = ![a,b,c,d] := by
    decide +kernel
  obtain ⟨i,hi⟩ := ht (s 0) (s 1) (s 2) (s 3) (by rw [← hf]; exact s.injective)
  refine ⟨i, ?_⟩
  apply Equiv.ext
  intro a
  exact congrFun (hi.trans hf.symm) a

def typeAction : Fin 24 → Fin 20 → Fin 20 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],
    ![0,1,3,2,4,6,5,9,8,7,10,12,11,15,14,13,19,18,17,16],
    ![0,2,1,3,7,5,8,4,6,9,16,13,17,11,14,18,10,12,15,19],
    ![0,2,3,1,7,8,5,9,6,4,16,17,13,18,14,11,19,15,12,10],
    ![0,3,1,2,9,6,8,4,5,7,19,15,18,12,14,17,10,11,13,16],
    ![0,3,2,1,9,8,6,7,5,4,19,18,15,17,14,12,16,13,11,10],
    ![10,4,11,12,1,5,6,13,14,15,0,2,3,7,8,9,16,17,18,19],
    ![10,4,12,11,1,6,5,15,14,13,0,3,2,9,8,7,19,18,17,16],
    ![10,11,4,12,13,5,14,1,6,15,16,7,17,2,8,18,0,3,9,19],
    ![10,11,12,4,13,14,5,15,6,1,16,17,7,18,8,2,19,9,3,0],
    ![10,12,4,11,15,6,14,1,5,13,19,9,18,3,8,17,0,2,7,16],
    ![10,12,11,4,15,14,6,13,5,1,19,18,9,17,8,3,16,7,2,0],
    ![16,7,13,17,2,5,8,11,14,18,0,1,3,4,6,9,10,12,15,19],
    ![16,7,17,13,2,8,5,18,14,11,0,3,1,9,6,4,19,15,12,10],
    ![16,13,7,17,11,5,14,2,8,18,10,4,12,1,6,15,0,3,9,19],
    ![16,13,17,7,11,14,5,18,8,2,10,12,4,15,6,1,19,9,3,0],
    ![16,17,7,13,18,8,14,2,5,11,19,9,15,3,6,12,0,1,4,10],
    ![16,17,13,7,18,14,8,11,5,2,19,15,9,12,6,3,10,4,1,0],
    ![19,9,15,18,3,6,8,12,14,17,0,1,2,4,5,7,10,11,13,16],
    ![19,9,18,15,3,8,6,17,14,12,0,2,1,7,5,4,16,13,11,10],
    ![19,15,9,18,12,6,14,3,8,17,10,4,11,1,5,13,0,2,7,16],
    ![19,15,18,9,12,14,6,17,8,3,10,11,4,13,5,1,16,7,2,0],
    ![19,18,9,15,17,8,14,3,6,12,16,7,13,2,5,11,0,1,4,10],
    ![19,18,15,9,17,14,8,12,6,3,16,13,7,11,5,2,10,4,1,0]]

theorem typeAction_spec (i : Fin 24) :
    ∀ j, tri (typeAction i j) = (tri j).map (sigma i) := by
  change ∀ j, tri (typeAction i j) = (tri j).map (permValues i)
  fin_cases i <;> decide +kernel

def actCode (i : Fin 24) (C : Finset (Fin 20)) : Finset (Fin 20) :=
  C.image (typeAction i)

theorem decode_actCode (i : Fin 24) (C : Finset (Fin 20)) :
    decode (actCode i C) = (decode C).image (Multiset.map (sigma i)) := by
  simp only [decode, actCode, image_image, Function.comp_def, typeAction_spec]

def decodeMask (n : ℕ) : Finset (Fin 20) :=
  univ.filter fun i => i.val ∈ Finset.equivBitIndices n

theorem decodeMask_familyMask (C : Finset (Fin 20)) :
    decodeMask (familyMask C) = C := by
  ext i
  simp only [decodeMask, mem_filter, mem_univ, true_and, familyMask,
    Equiv.apply_symm_apply, mem_image]
  constructor
  · rintro ⟨j,hj,hji⟩
    exact Fin.val_injective hji ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

def canonicalMask (C : Finset (Fin 20)) : ℕ :=
  (univ.image fun i : Fin 24 => familyMask (actCode i C)).min'
    (by simp only [image_nonempty, univ_nonempty])

theorem canonicalMask_attained (C : Finset (Fin 20)) :
    ∃ i : Fin 24, canonicalMask C = familyMask (actCode i C) := by
  obtain ⟨i,hi,he⟩ := mem_image.mp
    (min'_mem (univ.image fun i : Fin 24 => familyMask (actCode i C))
      (by simp only [image_nonempty, univ_nonempty]))
  exact ⟨i,he.symm⟩

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.sigma_covers
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.decode_actCode
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.canonicalMask_attained
