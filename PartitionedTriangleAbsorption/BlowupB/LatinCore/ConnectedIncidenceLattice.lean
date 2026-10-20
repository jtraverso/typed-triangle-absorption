/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding

@[expose] public section

/-! Integer incidence preimages constructed from paths. No boundedness is
claimed here: this is the lattice baseline used before bounded rounding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedIncidenceLattice

open Matrix OrientedCycleVector

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

include ho in
/-- On a connected graph every integral zero-sum demand has an integral
oriented flow. Paths construct a real preimage; network rounding makes it
integral without changing its divergence. -/
theorem integer_preimage (hG : G.Connected) (z : V → ℤ)
    (hz : ∑ v, z v = 0) :
    ∃ f : G.edgeSet → ℤ,
      (incidence G o).mulVecLin (fun e => (f e : ℝ)) = fun v => (z v : ℝ) := by
  classical
  let root : V := Classical.choice hG.nonempty
  let p : ∀ v, G.Walk root v := fun v => (hG root v).some
  let f : G.edgeSet → ℝ := ∑ v, (z v : ℝ) • chain G o (p v)
  have hsum : ∑ v, (z v : ℝ) = 0 := by exact_mod_cast hz
  have hf : (incidence G o).mulVecLin f = fun v => (z v : ℝ) := by
    change (incidence G o).mulVecLin (∑ v, (z v : ℝ) • chain G o (p v)) = _
    simp only [map_sum, map_smul, incidence_chain G o ho]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hfirst : (∑ v, (z v : ℝ) * (if w = v then 1 else 0)) = z w := by
      simp [mul_ite, eq_comm]
    rw [hfirst, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  obtain ⟨g, hg, -, -⟩ := NetworkFlowRounding.round G o ho f
    (by intro v; rw [hf]; exact ⟨z v, rfl⟩)
  exact ⟨g, hg.trans hf⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedIncidenceLattice

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedIncidenceLattice.integer_preimage
