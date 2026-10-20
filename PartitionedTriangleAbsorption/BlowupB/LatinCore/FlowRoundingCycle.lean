/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-! The finite graph step in integral flow rounding: a nonempty
fractional-edge graph with no degree-one vertex must contain a cycle. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingCycle

open SimpleGraph SimpleGraph.Walk

theorem exists_cycle_of_no_leaf {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ∃ a b, G.Adj a b) (hno : ∀ v, G.degree v ≠ 1) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle := by
  classical
  by_contra hc
  have hacyc : G.IsAcyclic := by
    intro v p hp
    exact hc ⟨v, p, hp⟩
  obtain ⟨a, b, hab⟩ := hne
  let : Nonempty V := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have hsingle : (SimpleGraph.Walk.cons hab .nil).IsPath := by simp [hab.ne]
  have hnil : ¬p.Nil := by grind
  apply hno u
  rw [degree_eq_one_iff_existsUnique_adj]
  refine ⟨_, p.adj_snd hnil, fun w hadj => ?_⟩
  apply hacyc.eq_snd_of_adj_start hp hadj
  have : ¬(p.cons hadj.symm).IsPath := by grind [length_cons]
  grind [hp.cons]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingCycle

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingCycle.exists_cycle_of_no_leaf
