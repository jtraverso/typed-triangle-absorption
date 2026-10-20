/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PortFlow

@[expose] public section

/-! Recover directed nonnegative integer counts from a signed current.
Forward and reverse counts are never both positive. Parallel channels are
still indexed separately by the caller; this module does not copy graph edges. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PortFlow

open Finset Matrix OrientedCycleVector

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

noncomputable def directedCount (z : G.edgeSet → ℤ) (u v : V) : ℕ :=
  if h : G.Adj u v then
    let e : G.edgeSet := ⟨s(u,v), h⟩
    if (o e).fst = u then (z e).toNat else (-z e).toNat
  else 0

include ho in
theorem directedCount_forward (z : G.edgeSet → ℤ) (e : G.edgeSet) :
    directedCount G o z (o e).fst (o e).snd = (z e).toNat := by
  classical
  have he : (⟨s((o e).fst, (o e).snd), (o e).adj⟩ : G.edgeSet) = e :=
    Subtype.ext (ho e)
  simp only [directedCount, dif_pos (o e).adj, he, ite_true]

include ho in
theorem directedCount_reverse (z : G.edgeSet → ℤ) (e : G.edgeSet) :
    directedCount G o z (o e).snd (o e).fst = (-z e).toNat := by
  classical
  have he : (⟨s((o e).snd, (o e).fst), (o e).adj.symm⟩ : G.edgeSet) = e := by
    apply Subtype.ext
    exact (o e).edge_symm.trans (ho e)
  simp only [directedCount, dif_pos (o e).adj.symm, he, (o e).adj.ne, ite_false]

theorem directedCount_not_adj (z : G.edgeSet → ℤ) (u v : V) (h : ¬G.Adj u v) :
    directedCount G o z u v = 0 := by simp only [directedCount, dif_neg h]

include ho in
theorem directedCount_signed (z : G.edgeSet → ℤ) :
    DirectedFlowIncidence.signed G o (fun u v => (directedCount G o z u v : ℝ)) =
      fun e => (z e : ℝ) := by
  funext e
  rw [DirectedFlowIncidence.signed_entry G o ho,
    directedCount_forward G o ho, directedCount_reverse G o ho]
  exact_mod_cast Int.toNat_sub_toNat_neg (z e)

include ho in
theorem directedCount_cap (z : G.edgeSet → ℤ) (cap : V → V → ℕ)
    (hz : ∀ e, -(cap (o e).snd (o e).fst : ℤ) ≤ z e ∧
      z e ≤ (cap (o e).fst (o e).snd : ℤ)) :
    ∀ u v, directedCount G o z u v ≤ cap u v := by
  classical
  have hforward : ∀ e, directedCount G o z (o e).fst (o e).snd ≤ cap (o e).fst (o e).snd := by
    intro e
    rw [directedCount_forward G o ho]
    exact Int.toNat_le.mpr (hz e).2
  have hreverse : ∀ e, directedCount G o z (o e).snd (o e).fst ≤ cap (o e).snd (o e).fst := by
    intro e
    rw [directedCount_reverse G o ho]
    apply Int.toNat_le.mpr
    have := (hz e).1
    omega
  intro u v
  by_cases huv : G.Adj u v
  · let e : G.edgeSet := ⟨s(u,v), huv⟩
    rcases SimpleGraph.dart_edge_eq_mk'_iff'.mp (ho e) with ⟨hf, ht⟩ | ⟨hf, ht⟩
    · simpa only [hf, ht] using hforward e
    · simpa only [hf, ht] using hreverse e
  · rw [directedCount_not_adj G o z u v huv]
    exact Nat.zero_le _

include ho in
/-- Actual integral directed counts, with no assumed integral-flow oracle. -/
theorem integer_directed_flow_of_cut (cap : V → V → ℕ)
    (hsupport : ∀ u v, ¬G.Adj u v → cap u v = 0)
    (b : V → ℤ) (hsum : ∑ v, b v = 0)
    (hcut : ∀ S : Finset V, ∑ v ∈ S, (b v : ℝ) ≤
      ∑ u ∈ Sᶜ, ∑ v ∈ S, (cap u v : ℝ)) :
    ∃ f : V → V → ℕ, (∀ u v, f u v ≤ cap u v) ∧
      ∀ v, (∑ u, (f u v : ℤ)) - ∑ w, (f v w : ℤ) = b v := by
  classical
  obtain ⟨z, hz, hzb⟩ := integer_current_of_cut G o ho cap hsupport b hsum hcut
  refine ⟨directedCount G o z, directedCount_cap G o ho z cap hzb, ?_⟩
  have hf : ∀ u v, ¬G.Adj u v → (directedCount G o z u v : ℝ) = 0 := by
    intro u v huv
    rw [directedCount_not_adj G o z u v huv, Nat.cast_zero]
  have hd := DirectedFlowIncidence.signed_divergence G o ho
    (fun u v => (directedCount G o z u v : ℝ)) hf
  rw [directedCount_signed G o ho, hz] at hd
  intro v
  have hv := (congrFun hd v).symm
  exact_mod_cast hv

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PortFlow
