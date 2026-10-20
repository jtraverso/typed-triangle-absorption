/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ConnectedTensorBaseline

@[expose] public section

/-! Producer-facing rounding: an integral two-sided incidence image has an
integer preimage at distance < 2. A real bound K propagates to K + 2.
The real bounded inverse and positive catalogue are separate constructions. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.BoundedIntegerFilling

open Matrix OrientedCycleVector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (GA : SimpleGraph A) (GB : SimpleGraph B)
    [DecidableRel GA.Adj] [DecidableRel GB.Adj]
    (oa : GA.edgeSet → GA.Dart) (ob : GB.edgeSet → GB.Dart)
    (hoa : ∀ e, (oa e).edge = e.val) (hob : ∀ e, (ob e).edge = e.val)

theorem incidence_sum (e : GA.edgeSet) : ∑ a, incidence GA oa a e = 0 := by
  classical
  simp [incidence, Finset.sum_sub_distrib]

theorem col_sum (y : Matrix GA.edgeSet B ℝ) (b : B) :
    ∑ a, (incidence GA oa * y) a b = 0 := by
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.sum_mul, incidence_sum GA oa, zero_mul]

theorem row_sum (y : Matrix A GB.edgeSet ℝ) (a : A) :
    ∑ b, (y * (incidence GB ob).transpose) a b = 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum, incidence_sum GB ob, mul_zero]

include hoa hob in
/-- No baseline or zero-margin condition is assumed: both are produced
from connectedness and the integral image equation. -/
theorem round_integer_image (hGA : GA.Connected) (hGB : GB.Connected)
    (x : Matrix A B ℤ) (c : Matrix GA.edgeSet GB.edgeSet ℝ)
    (hc : incidence GA oa * c * (incidence GB ob).transpose = x.map (Int.castRingHom ℝ)) :
    ∃ z : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * z.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
        x.map (Int.castRingHom ℝ) ∧ ∀ i j, |(z i j : ℝ) - c i j| < 2 := by
  have hcol : ∀ b, ∑ a, x a b = 0 := by
    intro b
    have hh := col_sum GA oa (c * (incidence GB ob).transpose) b
    rw [← Matrix.mul_assoc, hc] at hh
    change (∑ a, (x a b : ℝ)) = 0 at hh
    exact_mod_cast hh
  have hrow : ∀ a, ∑ b, x a b = 0 := by
    intro a
    have hh := row_sum GB ob (incidence GA oa * c) a
    rw [hc] at hh
    change (∑ b, (x a b : ℝ)) = 0 at hh
    exact_mod_cast hh
  exact ConnectedTensorBaseline.round_zero_margins GA GB oa ob hoa hob
    hGA hGB x hcol hrow c hc

include hoa hob in
/-- Propagation of the additive rounding constant to the bounded producer.
In particular a real bound 4 M / (hA hB) gives the integer bound
4 M / (hA hB) + 2, with no norm bound on the intermediate projection. -/
theorem bounded_integer_preimage (hGA : GA.Connected) (hGB : GB.Connected)
    (x : Matrix A B ℤ) (c : Matrix GA.edgeSet GB.edgeSet ℝ)
    (hc : incidence GA oa * c * (incidence GB ob).transpose = x.map (Int.castRingHom ℝ))
    (K : ℝ) (hK : ∀ i j, |c i j| ≤ K) :
    ∃ z : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * z.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
        x.map (Int.castRingHom ℝ) ∧ ∀ i j, |(z i j : ℝ)| < K + 2 := by
  obtain ⟨z, hz, herr⟩ := round_integer_image GA GB oa ob hoa hob hGA hGB x c hc
  refine ⟨z, hz, ?_⟩
  intro i j
  obtain ⟨hel, heu⟩ := abs_lt.mp (herr i j)
  obtain ⟨hkl, hku⟩ := abs_le.mp (hK i j)
  apply abs_lt.mpr
  constructor <;> linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.BoundedIntegerFilling

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.BoundedIntegerFilling.round_integer_image
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.BoundedIntegerFilling.bounded_integer_preimage
