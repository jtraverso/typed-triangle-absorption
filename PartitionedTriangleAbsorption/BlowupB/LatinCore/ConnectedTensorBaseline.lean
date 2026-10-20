/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedIncidenceLattice
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedTensorRounding

@[expose] public section

/-! An actual integer baseline for a two-sided incidence image with zero
margins. Connectedness, not a preimage oracle, supplies the baseline. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedTensorBaseline

open Matrix OrientedCycleVector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def anchored (r : A) : Matrix A A ℝ :=
  fun i j => (if i = j then 1 else 0) - (if i = r then 1 else 0)

theorem anchored_mul (r : A) (x : Matrix A B ℝ)
    (hcol : ∀ j, ∑ i, x i j = 0) : anchored r * x = x := by
  classical
  ext i j
  simp only [Matrix.mul_apply, anchored, sub_mul, Finset.sum_sub_distrib]
  have hfirst : (∑ k, (if i = k then (1 : ℝ) else 0) * x k j) = x i j := by
    simp [ite_mul, eq_comm]
  rw [hfirst, ← Finset.mul_sum, hcol j, mul_zero, sub_zero]

theorem mul_anchored_transpose (r : B) (x : Matrix A B ℝ)
    (hrow : ∀ i, ∑ j, x i j = 0) : x * (anchored r).transpose = x := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, anchored,
    mul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ k, x i k * (if j = k then (1 : ℝ) else 0)) = x i j := by
    simp [mul_ite, eq_comm]
  rw [hfirst, ← Finset.sum_mul, hrow i, zero_mul, sub_zero]

variable (GA : SimpleGraph A) (GB : SimpleGraph B)
    [DecidableRel GA.Adj] [DecidableRel GB.Adj]
    (oa : GA.edgeSet → GA.Dart) (ob : GB.edgeSet → GB.Dart)
    (hoa : ∀ e, (oa e).edge = e.val) (hob : ∀ e, (ob e).edge = e.val)

include hoa in
theorem anchored_preimage (hGA : GA.Connected) (r : A) :
    ∃ p : Matrix GA.edgeSet A ℤ,
      incidence GA oa * p.map (Int.castRingHom ℝ) = anchored r := by
  classical
  have hpaths : ∀ a : A, ∃ f : GA.edgeSet → ℤ,
      (incidence GA oa).mulVecLin (fun e => (f e : ℝ)) =
        fun v => (((if v = a then 1 else 0) - (if v = r then 1 else 0) : ℤ) : ℝ) := by
    intro a
    apply ConnectedIncidenceLattice.integer_preimage GA oa hoa hGA
    simp [Finset.sum_sub_distrib]
  choose f hf using hpaths
  refine ⟨fun e a => f a e, ?_⟩
  ext v a
  have hh := congrFun (hf a) v
  change (∑ e, incidence GA oa v e * (f a e : ℝ)) =
    (if v = a then 1 else 0) - (if v = r then 1 else 0)
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero] using hh

include hoa hob in
theorem integer_baseline (hGA : GA.Connected) (hGB : GB.Connected)
    (x : Matrix A B ℤ) (hcol : ∀ j, ∑ i, x i j = 0)
    (hrow : ∀ i, ∑ j, x i j = 0) :
    ∃ z : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * z.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
        x.map (Int.castRingHom ℝ) := by
  classical
  let a : A := Classical.choice hGA.nonempty
  let b : B := Classical.choice hGB.nonempty
  obtain ⟨p, hp⟩ := anchored_preimage GA oa hoa hGA a
  obtain ⟨q, hq⟩ := anchored_preimage GB ob hob hGB b
  refine ⟨p * x * q.transpose, ?_⟩
  have hcolr : ∀ j, ∑ i, (x.map (Int.castRingHom ℝ)) i j = 0 := by
    intro j
    change (∑ i, (x i j : ℝ)) = 0
    exact_mod_cast hcol j
  have hrowr : ∀ i, ∑ j, (x.map (Int.castRingHom ℝ)) i j = 0 := by
    intro i
    change (∑ j, (x i j : ℝ)) = 0
    exact_mod_cast hrow i
  have hqt : q.transpose.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
      (anchored b).transpose := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_map] using
      congrArg Matrix.transpose hq
  rw [Matrix.map_mul, Matrix.map_mul]
  calc
    incidence GA oa * (p.map (Int.castRingHom ℝ) * x.map (Int.castRingHom ℝ) *
        q.transpose.map (Int.castRingHom ℝ)) * (incidence GB ob).transpose =
        (incidence GA oa * p.map (Int.castRingHom ℝ)) * x.map (Int.castRingHom ℝ) *
          (q.transpose.map (Int.castRingHom ℝ) * (incidence GB ob).transpose) := by
            simp only [Matrix.mul_assoc]
    _ = anchored a * x.map (Int.castRingHom ℝ) * (anchored b).transpose := by rw [hp, hqt]
    _ = x.map (Int.castRingHom ℝ) := by
      rw [anchored_mul a _ hcolr, mul_anchored_transpose b _ hrowr]

include hoa hob in
/-- The integer baseline is now constructed, not assumed. -/
theorem round_zero_margins (hGA : GA.Connected) (hGB : GB.Connected)
    (x : Matrix A B ℤ) (hcol : ∀ j, ∑ i, x i j = 0)
    (hrow : ∀ i, ∑ j, x i j = 0)
    (c : Matrix GA.edgeSet GB.edgeSet ℝ)
    (hc : incidence GA oa * c * (incidence GB ob).transpose = x.map (Int.castRingHom ℝ)) :
    ∃ z : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * z.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
        x.map (Int.castRingHom ℝ) ∧ ∀ i j, |(z i j : ℝ) - c i j| < 2 := by
  obtain ⟨base, hb⟩ := integer_baseline GA GB oa ob hoa hob hGA hGB x hcol hrow
  obtain ⟨z, hz, herr⟩ := OrientedTensorRounding.round_preimage GA GB oa ob hoa hob
    c base (hc.trans hb.symm)
  exact ⟨z, hz.trans hc, herr⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedTensorBaseline

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedTensorBaseline.integer_baseline
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedTensorBaseline.round_zero_margins
