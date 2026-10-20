/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Push

@[expose] public section

/-! Integral directed counts can be realized by distinct indexed channels.
Indices sharing endpoints remain different elements of E, rather than copied
edges of a simple graph. No expansion or routing oracle is assumed here. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelSelection

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def capacity (src dst : E → V) (u v : V) : ℕ :=
  (univ.filter (fun e => src e = u ∧ dst e = v)).card

/-- Each integer count up to its endpoint capacity is realized without reusing
any channel index. The selection is allowed to depend on the counts. -/
theorem exists_selection (src dst : E → V) (f : V → V → ℕ)
    (hf : ∀ u v, f u v ≤ capacity src dst u v) :
    ∃ T : Finset E, ∀ u v,
      (T.filter (fun e => src e = u ∧ dst e = v)).card = f u v := by
  classical
  have hq : ∀ u v, ∃ Q ⊆ univ.filter (fun e => src e = u ∧ dst e = v),
      Q.card = f u v := fun u v => exists_subset_card_eq (hf u v)
  choose Q hQsub hQcard using hq
  let T := univ.biUnion (fun u => univ.biUnion (fun v => Q u v))
  refine ⟨T, fun u v => ?_⟩
  have hfilter : T.filter (fun e => src e = u ∧ dst e = v) = Q u v := by
    ext e
    constructor
    · intro he
      obtain ⟨heT, heu, hev⟩ := mem_filter.mp he
      obtain ⟨i, _, heI⟩ := mem_biUnion.mp heT
      obtain ⟨j, _, heQ⟩ := mem_biUnion.mp heI
      obtain ⟨_, hei, hej⟩ := mem_filter.mp (hQsub i j heQ)
      have hi : i = u := hei.symm.trans heu
      have hj : j = v := hej.symm.trans hev
      simpa only [hi, hj] using heQ
    · intro he
      have heuv := (mem_filter.mp (hQsub u v he)).2
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨u, mem_univ _,
        mem_biUnion.mpr ⟨v, mem_univ _, he⟩⟩, heuv⟩
  rw [hfilter]
  exact hQcard u v

theorem incoming_count (src dst : E → V) (T : Finset E) (v : V) :
    (∑ u, (T.filter (fun e => src e = u ∧ dst e = v)).card) =
      (T.filter (fun e => dst e = v)).card := by
  have h := sum_card_fiberwise_eq_card_filter
    (T.filter (fun e => dst e = v)) univ src
  simpa [Finset.filter_filter, and_comm] using h

theorem outgoing_count (src dst : E → V) (T : Finset E) (v : V) :
    (∑ u, (T.filter (fun e => src e = v ∧ dst e = u)).card) =
      (T.filter (fun e => src e = v)).card := by
  have h := sum_card_fiberwise_eq_card_filter
    (T.filter (fun e => src e = v)) univ dst
  simpa [Finset.filter_filter] using h

/-- Selection preserves every prescribed integral imbalance exactly. -/
theorem exists_selection_with_demand (src dst : E → V) (f : V → V → ℕ)
    (hf : ∀ u v, f u v ≤ capacity src dst u v) (b : V → ℤ)
    (hb : ∀ v, (∑ u, (f u v : ℤ)) - ∑ w, (f v w : ℤ) = b v) :
    ∃ T : Finset E,
      (∀ u v, (T.filter (fun e => src e = u ∧ dst e = v)).card = f u v) ∧
      ∀ v, ((T.filter (fun e => dst e = v)).card : ℤ) -
        ((T.filter (fun e => src e = v)).card : ℤ) = b v := by
  obtain ⟨T, hT⟩ := exists_selection src dst f hf
  refine ⟨T, hT, fun v => ?_⟩
  rw [← incoming_count src dst T v, ← outgoing_count src dst T v]
  simp_rw [hT]
  push_cast
  exact hb v

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelSelection

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelSelection.exists_selection_with_demand
