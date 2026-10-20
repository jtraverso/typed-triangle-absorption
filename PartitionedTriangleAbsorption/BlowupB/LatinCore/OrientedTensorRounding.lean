/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection

@[expose] public section

/-! Integer rounding of a two-sided incidence preimage with additive
entrywise error < 2. Integer lattice membership is supplied by an actual
integer baseline, not inferred from integrality of the target alone. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedTensorRounding

open Matrix OrientedCycleVector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (GA : SimpleGraph A) (GB : SimpleGraph B)
    [DecidableRel GA.Adj] [DecidableRel GB.Adj]
    (oa : GA.edgeSet → GA.Dart) (ob : GB.edgeSet → GB.Dart)
    (hoa : ∀ e, (oa e).edge = e.val) (hob : ∀ e, (ob e).edge = e.val)

include hoa hob in
/-- Round a real preimage in the same two-sided incidence fibre as an
integer baseline. The baseline may be unbounded; the error bound is not. -/
theorem round_preimage (c : Matrix GA.edgeSet GB.edgeSet ℝ)
    (base : Matrix GA.edgeSet GB.edgeSet ℤ)
    (himage : incidence GA oa * c * (incidence GB ob).transpose =
      incidence GA oa * base.map (fun z : ℤ => (z : ℝ)) * (incidence GB ob).transpose) :
    ∃ z : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * z.map (fun z : ℤ => (z : ℝ)) * (incidence GB ob).transpose =
        incidence GA oa * c * (incidence GB ob).transpose ∧
      ∀ i j, |(z i j : ℝ) - c i j| < 2 := by
  classical
  let cr : Matrix GA.edgeSet GB.edgeSet ℝ := fun i j => (base i j : ℝ)
  have hd : incidence GA oa * (c - cr) * (incidence GB ob).transpose = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, himage]
    exact sub_self _
  obtain ⟨u, v, huv, hu, hv⟩ :=
    IncidenceProjection.split (incidence GA oa) (incidence GB ob).transpose (c - cr) hd
  have hc : c = cr + u + v := by
    rw [add_assoc, ← huv, add_sub_cancel]
  have hcols : ∀ j : GB.edgeSet, ∃ z : GA.edgeSet → ℤ,
      (incidence GA oa).mulVecLin (fun i => (z i : ℝ)) = 0 ∧
      ∀ i, |(z i : ℝ) - u i j| < 1 := by
    intro j
    have hzero : (incidence GA oa).mulVecLin (fun i => u i j) = 0 := by
      funext a
      exact congrFun (congrFun hu a) j
    obtain ⟨z, hz, -, herr⟩ := NetworkFlowRounding.round GA oa hoa (fun i => u i j)
      (by intro a; rw [hzero]; exact ⟨0, by simp⟩)
    exact ⟨z, hz.trans hzero, herr⟩
  choose uz huz hezu using hcols
  have hrows : ∀ i : GA.edgeSet, ∃ z : GB.edgeSet → ℤ,
      (incidence GB ob).mulVecLin (fun j => (z j : ℝ)) = 0 ∧
      ∀ j, |(z j : ℝ) - v i j| < 1 := by
    intro i
    have hzero : (incidence GB ob).mulVecLin (fun j => v i j) = 0 := by
      funext b
      have hh := congrFun (congrFun hv i) b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.zero_apply, mul_comm] using hh
    obtain ⟨z, hz, -, herr⟩ := NetworkFlowRounding.round GB ob hob (fun j => v i j)
      (by intro b; rw [hzero]; exact ⟨0, by simp⟩)
    exact ⟨z, hz.trans hzero, herr⟩
  choose vz hvz hezv using hrows
  let ur : Matrix GA.edgeSet GB.edgeSet ℝ := fun i j => (uz j i : ℝ)
  let vr : Matrix GA.edgeSet GB.edgeSet ℝ := fun i j => (vz i j : ℝ)
  have hur : incidence GA oa * ur = 0 := by
    ext a j
    exact congrFun (huz j) a
  have hvr : vr * (incidence GB ob).transpose = 0 := by
    ext i b
    have hh := congrFun (hvz i) b
    change (∑ j, (vz i j : ℝ) * incidence GB ob b j) = 0
    simpa only [Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using hh
  let z : Matrix GA.edgeSet GB.edgeSet ℤ := fun i j => base i j + uz j i + vz i j
  have hzr : z.map (fun z : ℤ => (z : ℝ)) = cr + ur + vr := by
    ext i j
    change ((base i j + uz j i + vz i j : ℤ) : ℝ) =
      (base i j : ℝ) + (uz j i : ℝ) + (vz i j : ℝ)
    simp
  refine ⟨z, ?_, ?_⟩
  · rw [hzr, TensorKernelSplit.preserve_image _ _ _ _ _ hur hvr]
    exact himage.symm
  · intro i j
    have hentry := congrFun (congrFun hc i) j
    change c i j = cr i j + u i j + v i j at hentry
    rw [hentry]
    have hzentry := congrFun (congrFun hzr i) j
    change (z i j : ℝ) = cr i j + ur i j + vr i j at hzentry
    rw [hzentry]
    exact TensorKernelSplit.entry_error _ _ _ _ _ (hezu j i) (hezv i j)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedTensorRounding

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedTensorRounding.round_preimage
