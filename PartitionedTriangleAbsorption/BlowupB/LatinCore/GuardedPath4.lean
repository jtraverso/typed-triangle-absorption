/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply

@[expose] public section

/-! One physical four-arc path, avoiding a forbidden graph and heavy vertices.
Only queries of at most two roots are used. This is the geometric greedy step,
not the global catalogue-load induction. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.GuardedPath4

open Finset AntiEdgeSelection StructuralF3General

variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_path (p : V → Fin 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hd : 0 ≤ d)
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (Z : Finset V)
    (hbudget : (Z.card : ℝ) + 4 + 2 * d < a)
    (u v : V) (i j k : Fin 3) (hu : p u = i) (hv : p v = j)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x y z : V,
      p x = j ∧ p y = k ∧ p z = i ∧
      x ∉ insert u (insert v Z) ∧
      z ∉ insert x (insert u (insert v Z)) ∧
      y ∉ insert z (insert x (insert u (insert v Z))) ∧
      G.Adj u x ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj z v ∧
      s(u,x) ∉ B ∧ s(x,y) ∉ B ∧ s(y,z) ∉ B ∧ s(z,v) ∉ B := by
  classical
  let Z0 := insert u (insert v Z)
  have hZ0 : (Z0.card : ℝ) ≤ Z.card + 2 := by
    have h1 := card_insert_le u (insert v Z)
    have h2 := card_insert_le v Z
    have h : Z0.card ≤ Z.card + 2 := by dsimp [Z0]; omega
    exact_mod_cast h
  obtain ⟨x, hx, hxadj, hxZ, hxB⟩ := guarded_exists_avoiding p G
    (fun i j => i ≠ j) 2 a d hs {u} Z0 (by simp) B hB hd (by norm_num; linarith)
    j (by intro w hw; have : w = u := mem_singleton.mp hw; subst w; simpa [hu] using hij)
  have hZ1 : ((insert x Z0).card : ℝ) ≤ Z.card + 3 := by
    have h := card_insert_le x Z0
    have hr : ((insert x Z0).card : ℝ) ≤ Z0.card + 1 := by exact_mod_cast h
    linarith
  obtain ⟨z, hz, hzadj, hzZ, hzB⟩ := guarded_exists_avoiding p G
    (fun i j => i ≠ j) 2 a d hs {v} (insert x Z0) (by simp) B hB hd (by norm_num; linarith)
    i (by intro w hw; have : w = v := mem_singleton.mp hw; subst w; simpa [hv] using hij.symm)
  have hZ2 : ((insert z (insert x Z0)).card : ℝ) ≤ Z.card + 4 := by
    have h := card_insert_le z (insert x Z0)
    have hr : ((insert z (insert x Z0)).card : ℝ) ≤ (insert x Z0).card + 1 := by
      exact_mod_cast h
    linarith
  have hguard : ∀ w ∈ ({x,z} : Finset V), p w ≠ k := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · simpa [hx] using hjk
    · have : w = z := mem_singleton.mp hw
      subst w
      simpa [hz] using hik
  obtain ⟨y, hy, hyadj, hyZ, hyB⟩ := guarded_exists_avoiding p G
    (fun i j => i ≠ j) 2 a d hs {x,z} (insert z (insert x Z0))
    (by have h := card_insert_le x ({z} : Finset V); simpa using h)
    B hB hd (by norm_num; linarith) k hguard
  refine ⟨x, y, z, hx, hy, hz, hxZ, hzZ, hyZ, hxadj u (by simp),
    hyadj x (by simp), (hyadj z (by simp)).symm, (hzadj v (by simp)).symm,
    hxB u (by simp), hyB x (by simp), ?_, ?_⟩
  · simpa only [Sym2.eq_swap] using hyB z (by simp)
  · simpa only [Sym2.eq_swap] using hzB v (by simp)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.GuardedPath4
