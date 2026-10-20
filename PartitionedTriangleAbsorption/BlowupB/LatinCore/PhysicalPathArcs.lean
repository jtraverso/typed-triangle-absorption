/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.Channels
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Paths
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Directed versions of the four-edge paths constructed in the physical
host. Their net incidence is exactly the incidence of the replaced arc. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs

open Finset Cycles Positivization PaddedNoCommon

variable {V : Type} [DecidableEq V]

def arcs (u x y z v : V) : Finset (V × V) := {(u,x), (x,y), (y,z), (z,v)}

def forget (P : Finset (V × V)) : Finset (Sym2 V) := P.image (fun e => s(e.1,e.2))

def vertex (u x y z v : V) (j : ℕ) : V :=
  if j = 0 then u else if j = 1 then x else if j = 2 then y else if j = 3 then z else v

theorem arcs_walk (u x y z v : V) :
    arcs u x y z v = pathArcs (vertex u x y z v) 4 := by
  have hr : range 4 = ({0,1,2,3} : Finset ℕ) := by decide
  unfold pathArcs
  rw [hr]
  simp [arcs, vertex]

theorem card_le (u x y z v : V) : (arcs u x y z v).card ≤ 4 := by
  rw [arcs_walk]
  exact card_pathArcs_le _ _

theorem net_eq {G : SimpleGraph V} {u x y z v : V}
    (hp : IsPath4 G u x y z v) (r : V) :
    net (arcs u x y z v) r = (if v = r then 1 else 0) - (if u = r then 1 else 0) := by
  have hux := G.ne_of_adj hp.ux
  have hxy := G.ne_of_adj hp.xy
  have hyz := G.ne_of_adj hp.yz
  have hzu := hp.zu
  have hxu := Ne.symm hux
  have hyu := hp.yu
  have hxz := hp.xz
  have hinj : Set.InjOn
      (fun j => (vertex u x y z v j, vertex u x y z v (j + 1)))
      (range 4 : Set ℕ) := by
    intro i hi j hj hij
    have hi4 : i < 4 := mem_range.mp hi
    have hj4 : j < 4 := mem_range.mp hj
    have hfirst := congrArg Prod.fst hij
    interval_cases i <;> interval_cases j <;> simp_all [vertex]
  rw [arcs_walk, net_pathArcs _ _ hinj]
  simp [vertex]

theorem supported {G : SimpleGraph V} {u x y z v : V}
    (hp : IsPath4 G u x y z v) : ∀ e ∈ arcs u x y z v, G.Adj e.1 e.2 := by
  intro e he
  simp only [arcs, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hp.ux
  · exact hp.xy
  · exact hp.yz
  · exact hp.zv

theorem cyclic (c : V → ZMod 3) (u x y z v : V)
    (hux : c x = c u + 1) (hxy : c y = c x + 1)
    (hyz : c z = c y + 1) (hzv : c v = c z + 1) : IsCyc c (arcs u x y z v) := by
  intro e he
  simp only [arcs, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hux
  · exact hxy
  · exact hyz
  · exact hzv

theorem symImage_eq (u x y z v : V) :
    forget (arcs u x y z v) = pathEdges u x y z v := by
  simp [forget, arcs, pathEdges]

theorem disjoint_of_sym {P Q : Finset (V × V)}
    (h : Disjoint (forget P) (forget Q)) : Disjoint P Q := by
  rw [disjoint_left] at h ⊢
  intro e he hf
  exact h (mem_image.mpr ⟨e, he, rfl⟩) (mem_image.mpr ⟨e, hf, rfl⟩)

theorem singleton_net (u v r : V) :
    net ({(u,v)} : Finset (V × V)) r =
      (if v = r then 1 else 0) - (if u = r then 1 else 0) := by
  unfold net inDeg outDeg
  rw [filter_singleton, filter_singleton]
  split_ifs <;> simp

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs.net_eq
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs.disjoint_of_sym
