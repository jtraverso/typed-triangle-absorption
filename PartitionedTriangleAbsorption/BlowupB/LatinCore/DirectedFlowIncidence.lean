/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Convert a nonnegative directed flow supported on graph edges to the
signed physical-edge incidence convention used by the rounding producer. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence

open Matrix OrientedCycleVector

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

include ho in
theorem step_entry (d : G.Dart) (e : G.edgeSet) :
    step G o d e = (if d = o e then 1 else 0) - (if d = (o e).symm then 1 else 0) := by
  classical
  have he : edgeOf G (o e) = e := Subtype.ext (ho e)
  have hes : edgeOf G (o e).symm = e := by
    apply Subtype.ext
    exact (o e).edge_symm.trans (ho e)
  by_cases hde : edgeOf G d = e
  · have hd : d.edge = (o e).edge := (congrArg Subtype.val hde).trans (ho e).symm
    rcases (SimpleGraph.dart_edge_eq_iff d (o e)).mp hd with hd | hd
    · subst d
      simp [step, he, Ne.symm (o e).symm_ne]
    · subst d
      simp [step, hes, (o e).symm_ne]
  · have h1 : d ≠ o e := by intro hd; exact hde (hd ▸ he)
    have h2 : d ≠ (o e).symm := by intro hd; exact hde (hd ▸ hes)
    simp [step, Pi.single_apply, hde, h1, h2]

noncomputable def arc (f : V → V → ℝ) (u v : V) : G.edgeSet → ℝ := by
  classical
  exact if h : G.Adj u v then f u v • step G o ⟨(u,v), h⟩ else 0

noncomputable def signed (f : V → V → ℝ) : G.edgeSet → ℝ :=
  ∑ u, ∑ v, arc G o f u v

include ho in
theorem arc_entry (f : V → V → ℝ) (u v : V) (e : G.edgeSet) :
    arc G o f u v e =
      f u v * ((if u = (o e).fst ∧ v = (o e).snd then 1 else 0) -
        (if u = (o e).snd ∧ v = (o e).fst then 1 else 0)) := by
  classical
  by_cases h : G.Adj u v
  · rw [arc, dif_pos h]
    change f u v * step G o ⟨(u,v),h⟩ e = _
    rw [step_entry G o ho]
    congr 1
    simp [SimpleGraph.Dart.ext_iff, Prod.ext_iff, SimpleGraph.Dart.symm]
  · have h1 : ¬(u = (o e).fst ∧ v = (o e).snd) := by
      rintro ⟨rfl, rfl⟩
      exact h (o e).adj
    have h2 : ¬(u = (o e).snd ∧ v = (o e).fst) := by
      rintro ⟨rfl, rfl⟩
      exact h (o e).adj.symm
    simp [arc, h, h1, h2]

include ho in
theorem signed_entry (f : V → V → ℝ) (e : G.edgeSet) :
    signed G o f e = f (o e).fst (o e).snd - f (o e).snd (o e).fst := by
  classical
  simp only [signed, Finset.sum_apply, arc_entry G o ho, mul_sub,
    Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  have hsum (a b : V) : (∑ u, ∑ v, if u = a ∧ v = b then f u v else 0) = f a b := by
    calc
      _ = ∑ u, if u = a then f u b else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u = a <;> simp [hu]
      _ = _ := by simp
  rw [hsum, hsum]

include ho in
theorem arc_divergence (f : V → V → ℝ)
    (hf : ∀ u v, ¬G.Adj u v → f u v = 0) (u v : V) :
    (incidence G o).mulVecLin (arc G o f u v) =
      fun w => f u v * ((if w = v then 1 else 0) - (if w = u then 1 else 0)) := by
  classical
  by_cases h : G.Adj u v
  · rw [arc, dif_pos h, map_smul, incidence_step G o ho]
    rfl
  · funext w
    simp [arc, h, hf u v h]

include ho in
theorem signed_divergence (f : V → V → ℝ)
    (hf : ∀ u v, ¬G.Adj u v → f u v = 0) :
    (incidence G o).mulVecLin (signed G o f) =
      fun w => (∑ u, f u w) - ∑ v, f w v := by
  classical
  change (incidence G o).mulVecLin (∑ u, ∑ v, arc G o f u v) = _
  simp only [map_sum, arc_divergence G o ho f hf]
  funext w
  simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite]

include ho in
theorem signed_bound (f : V → V → ℝ) (K : ℝ)
    (h0 : ∀ u v, 0 ≤ f u v) (hK : ∀ u v, f u v ≤ K) :
    ∀ e, |signed G o f e| ≤ K := by
  intro e
  rw [signed_entry G o ho]
  apply abs_le.mpr
  constructor <;> linarith [h0 (o e).fst (o e).snd, h0 (o e).snd (o e).fst,
    hK (o e).fst (o e).snd, hK (o e).snd (o e).fst]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence.signed_divergence
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence.signed_bound
