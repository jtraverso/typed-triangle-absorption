/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Signed walk vectors for an arbitrary choice of one orientation per
physical edge. A closed trail gives a genuine ±1 kernel vector. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector

open SimpleGraph SimpleGraph.Walk Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edgeOf (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

variable (o : G.edgeSet → G.Dart)

noncomputable def incidence : Matrix V G.edgeSet ℝ := by
  classical
  exact fun v e => (if v = (o e).snd then 1 else 0) -
    (if v = (o e).fst then 1 else 0)

noncomputable def step (d : G.Dart) : G.edgeSet → ℝ := by
  classical
  exact Pi.single (edgeOf G d) (if d = o (edgeOf G d) then 1 else -1)

noncomputable def chain {u v : V} (p : G.Walk u v) : G.edgeSet → ℝ :=
  (p.darts.map (step G o)).sum

variable (ho : ∀ e, (o e).edge = e.val)

include ho in
theorem incidence_step (d : G.Dart) :
    (incidence G o).mulVecLin (step G o d) =
      (fun v => (if v = d.snd then 1 else 0) - (if v = d.fst then 1 else 0)) := by
  classical
  have hed : d.edge = (o (edgeOf G d)).edge := (ho (edgeOf G d)).symm
  rcases (SimpleGraph.dart_edge_eq_iff d (o (edgeOf G d))).mp hed with hd | hd
  · rw [show step G o d = Pi.single (edgeOf G d) 1 by simp only [step, if_pos hd]]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    funext v
    change ((if v = (o (edgeOf G d)).snd then (1 : ℝ) else 0) -
      (if v = (o (edgeOf G d)).fst then 1 else 0)) = _
    rw [← hd]
  · have hn : d ≠ o (edgeOf G d) := by
      intro hh
      have := (o (edgeOf G d)).symm_ne
      exact this (hd.symm.trans hh)
    rw [show step G o d = Pi.single (edgeOf G d) (-1) by simp only [step, if_neg hn]]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single]
    funext v
    have hfst : d.fst = (o (edgeOf G d)).snd := congrArg (fun t : G.Dart => t.fst) hd
    have hsnd : d.snd = (o (edgeOf G d)).fst := congrArg (fun t : G.Dart => t.snd) hd
    change ((if v = (o (edgeOf G d)).snd then (1 : ℝ) else 0) -
      (if v = (o (edgeOf G d)).fst then 1 else 0)) * (-1) = _
    rw [hfst, hsnd]
    ring

include ho in
theorem incidence_chain {u v : V} (p : G.Walk u v) :
    (incidence G o).mulVecLin (chain G o p) =
      (fun w => (if w = v then 1 else 0) - (if w = u then 1 else 0)) := by
  classical
  induction p with
  | nil => ext x; simp [chain]
  | @cons u v w h p ih =>
    have hc : chain G o (.cons h p) = step G o ⟨(u,v), h⟩ + chain G o p := by
      simp [chain]
    rw [hc, map_add, incidence_step G o ho, ih]
    funext x
    simp only [Pi.add_apply]
    change ((if x = v then 1 else 0) - (if x = u then 1 else 0)) +
      ((if x = w then 1 else 0) - (if x = v then 1 else 0)) = _
    ring

theorem chain_zero_of_not_mem {u v : V} (p : G.Walk u v) (e : G.edgeSet)
    (he : e.val ∉ p.edges) : chain G o p e = 0 := by
  classical
  induction p with
  | nil => simp [chain]
  | @cons u v w h p ih =>
    have heq : e ≠ edgeOf G ⟨(u,v), h⟩ := by
      intro hh
      apply he
      simp [hh, edgeOf]
    have hp : e.val ∉ p.edges := fun hm => he (by simp [hm])
    have hz := ih hp
    have hc : chain G o (.cons h p) = step G o ⟨(u,v), h⟩ + chain G o p := by
      simp [chain]
    rw [hc]
    change step G o ⟨(u,v), h⟩ e + chain G o p e = 0
    rw [hz]
    simp [step, Ne.symm heq]

theorem chain_sign {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    (e : G.edgeSet) (he : e.val ∈ p.edges) :
    chain G o p e = 1 ∨ chain G o p e = -1 := by
  classical
  induction p with
  | nil => simp at he
  | @cons u v w h p ih =>
    obtain ⟨hpt, hnot⟩ := (Walk.isTrail_cons h p).mp hp
    have hc : chain G o (.cons h p) = step G o ⟨(u,v), h⟩ + chain G o p := by
      simp [chain]
    rw [hc]
    change step G o ⟨(u,v), h⟩ e + chain G o p e = 1 ∨
      step G o ⟨(u,v), h⟩ e + chain G o p e = -1
    by_cases heq : e = edgeOf G ⟨(u,v), h⟩
    · have hz : chain G o p e = 0 := chain_zero_of_not_mem G o p e (by simpa [heq, edgeOf] using hnot)
      rw [hz, add_zero]
      simp only [step, ← heq, Pi.single_eq_same]
      split_ifs <;> simp
    · have hs : step G o ⟨(u,v), h⟩ e = 0 := by
        simp [step, Pi.single_apply, Ne.symm heq]
      rw [hs, zero_add]
      apply ih hpt
      have hne : e.val ≠ s(u,v) := by
        intro hh
        apply heq
        exact Subtype.ext hh
      simpa [hne] using he

include ho in
theorem closed_chain_kernel {v : V} (p : G.Walk v v) :
    (incidence G o).mulVecLin (chain G o p) = 0 := by
  rw [incidence_chain G o ho]
  ext w
  simp

end PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector.closed_chain_kernel
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector.chain_sign
