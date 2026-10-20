/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! A lossless finite encoding for the four-label census. This module is
independent of the family-existence build. It does not assume Python output. -/

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

open Finset

def tri : Fin 20 → Multiset (Fin 4) :=
  ![{0,0,0}, {0,0,1}, {0,0,2}, {0,0,3}, {0,1,1},
    {0,1,2}, {0,1,3}, {0,2,2}, {0,2,3}, {0,3,3},
    {1,1,1}, {1,1,2}, {1,1,3}, {1,2,2}, {1,2,3},
    {1,3,3}, {2,2,2}, {2,2,3}, {2,3,3}, {3,3,3}]

theorem tri_card : ∀ i, (tri i).card = 3 := by decide +kernel

theorem tri_injective : Function.Injective tri := by decide +kernel

theorem tri_exhaustive {τ : Multiset (Fin 4)} (hτ : τ.card = 3) :
    ∃ i, tri i = τ := by
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hτ
  exact (by decide +kernel : ∀ a b c : Fin 4, ∃ i, tri i = {a,b,c}) a b c

def encode (F : Finset (Multiset (Fin 4))) : Finset (Fin 20) :=
  univ.filter fun i => tri i ∈ F

def decode (C : Finset (Fin 20)) : Finset (Multiset (Fin 4)) :=
  C.image tri

theorem decode_encode (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, τ.card = 3) : decode (encode F) = F := by
  ext τ
  constructor
  · rintro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    exact (mem_filter.mp hi).2
  · intro h
    obtain ⟨i, hi⟩ := tri_exhaustive (hF τ h)
    apply mem_image.mpr
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi ▸ h⟩, hi⟩

theorem encode_decode (C : Finset (Fin 20)) : encode (decode C) = C := by
  ext i
  simp only [encode, mem_filter, mem_univ, true_and, decode, mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact tri_injective hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

def Allowed (C : Finset (Fin 20)) (a b : Fin 4) : Prop :=
  ∃ i ∈ C, ∃ z : Fin 4, tri i = {a,b,z}

instance (C : Finset (Fin 20)) (a b : Fin 4) : Decidable (Allowed C a b) :=
  inferInstanceAs (Decidable (∃ i ∈ C, ∃ z : Fin 4, tri i = {a,b,z}))

theorem allowed_encode_iff (F : Finset (Multiset (Fin 4))) (a b : Fin 4) :
    Allowed (encode F) a b ↔ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F := by
  constructor
  · rintro ⟨i, hi, z, hz⟩
    exact ⟨z, hz ▸ (mem_filter.mp hi).2⟩
  · rintro ⟨z, hz⟩
    obtain ⟨i, hi⟩ := tri_exhaustive (τ := ({a,b,z} : Multiset (Fin 4))) (by simp)
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi ▸ hz⟩, z, hi⟩

def UsesAll (C : Finset (Fin 20)) : Prop :=
  ∀ a : Fin 4, ∃ i ∈ C, a ∈ tri i

def Admissible (C : Finset (Fin 20)) : Prop :=
  UsesAll C ∧ ∀ a : Fin 4, ∃ b : Fin 4, ¬ Allowed C a b

instance (C : Finset (Fin 20)) : Decidable (Admissible C) := by
  unfold Admissible UsesAll
  infer_instance

def forbiddenBox (f : Fin 4 → Fin 4) : Finset (Fin 20) :=
  univ.filter fun i => ∀ a : Fin 4, ¬ ∃ z : Fin 4, tri i = {a, f a, z}

/-- Every admissible family occurs in a box with one forbidden partner per
label. This covers all families, not just preselected representatives. -/
theorem admissible_subset_box (C : Finset (Fin 20)) (hC : Admissible C) :
    ∃ f : Fin 4 → Fin 4, C ⊆ forbiddenBox f := by
  classical
  choose f hf using hC.2
  refine ⟨f, ?_⟩
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ i, ?_⟩
  intro a h
  obtain ⟨z, hz⟩ := h
  exact hf a ⟨i, hi, z, hz⟩

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.decode_encode
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.admissible_subset_box
