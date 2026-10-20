/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# A partially defined additive torsion value modulo `q` on finite edge sets

Generalization of `PaddedF12.ParityEvaluation` (`q = 2`).
-/

namespace TorsionQ

open Finset

variable {α : Type*} [DecidableEq α]

structure QEvaluation (q : Nat) (Good : Finset α → Prop) where
  empty_good : Good ∅
  union_good : ∀ {A B : Finset α}, Disjoint A B → Good A → Good B → Good (A ∪ B)
  value : Finset α → Nat
  value_lt : ∀ A, Good A → value A < q
  empty_value : value ∅ = 0
  union_value : ∀ {A B : Finset α}, Disjoint A B → Good A → Good B →
    value (A ∪ B) = (value A + value B) % q

namespace QEvaluation

variable {q : Nat} {Good : Finset α → Prop} (ev : QEvaluation q Good)

include ev

theorem good_biUnion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : ι → Finset α)
    (hdis : (S : Set ι).PairwiseDisjoint E) (hgood : ∀ i ∈ S, Good (E i)) :
    Good (S.biUnion E) := by
  induction S using Finset.induction_on with
  | empty => simpa using ev.empty_good
  | insert i S hi ih =>
    rw [biUnion_insert]
    have hrest : (S : Set ι).PairwiseDisjoint E :=
      hdis.subset (by intro j hj; exact mem_insert_of_mem hj)
    have hgoods : ∀ j ∈ S, Good (E j) := fun j hj => hgood j (mem_insert_of_mem hj)
    apply ev.union_good
    · rw [disjoint_biUnion_right]
      intro j hj
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
    · exact hgood i (mem_insert_self _ _)
    · exact ih hrest hgoods

theorem value_biUnion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : ι → Finset α)
    (hdis : (S : Set ι).PairwiseDisjoint E) (hgood : ∀ i ∈ S, Good (E i)) :
    ev.value (S.biUnion E) = (∑ i ∈ S, ev.value (E i)) % q := by
  induction S using Finset.induction_on with
  | empty => simp [ev.empty_value]
  | insert i S hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have hrest : (S : Set ι).PairwiseDisjoint E :=
      hdis.subset (by intro j hj; exact mem_insert_of_mem hj)
    have hgoods : ∀ j ∈ S, Good (E j) := fun j hj => hgood j (mem_insert_of_mem hj)
    have hgoodi := hgood i (mem_insert_self _ _)
    have hsep : Disjoint (E i) (S.biUnion E) := by
      rw [disjoint_biUnion_right]
      intro j hj
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
    rw [ev.union_value hsep hgoodi (ev.good_biUnion S E hrest hgoods), ih hrest hgoods,
      Nat.add_mod_mod]

end QEvaluation

end TorsionQ
