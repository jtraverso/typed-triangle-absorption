/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Algebraic part of the integer rectangular rounding argument.
This file does NOT construct the spanning-tree projection, round a flow,
or assert DenseRefiner. Those producers remain separate obligations. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit

open Matrix

variable {A E F B : Type*} [Fintype E] [Fintype F]

/-- A divergence-preserving projection that kills the first kernel splits
the kernel of the two-sided operator into its two one-sided kernels. -/
theorem split (left : Matrix A E ℝ) (right : Matrix F B ℝ)
    (proj : Matrix E E ℝ) (d : Matrix E F ℝ)
    (hpreserve : left * proj = left)
    (hkill : ∀ z : Matrix E B ℝ, left * z = 0 → proj * z = 0)
    (hd : left * d * right = 0) :
    ∃ u v : Matrix E F ℝ,
      d = u + v ∧ left * u = 0 ∧ v * right = 0 := by
  refine ⟨d - proj * d, proj * d, ?_, ?_, ?_⟩
  · exact (sub_add_cancel d (proj * d)).symm
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc, hpreserve, sub_self]
  · rw [Matrix.mul_assoc]
    apply hkill
    simpa only [← Matrix.mul_assoc] using hd

/-- Replacing the two kernel summands by other elements of those same
kernels leaves the two-sided image of the baseline unchanged. -/
theorem preserve_image (left : Matrix A E ℝ) (right : Matrix F B ℝ)
    (base u v : Matrix E F ℝ)
    (hu : left * u = 0) (hv : v * right = 0) :
    left * (base + u + v) * right = left * base * right := by
  simp only [Matrix.mul_add, Matrix.add_mul, hu,
    add_zero, Matrix.mul_assoc, hv, Matrix.mul_zero]

/-- Two entrywise strict rounding errors below one give an error below two;
the potentially large common baseline cancels exactly. -/
theorem entry_error (base u v u' v' : ℝ)
    (hu : |u' - u| < 1) (hv : |v' - v| < 1) :
    |(base + u' + v') - (base + u + v)| < 2 := by
  have heq : (base + u' + v') - (base + u + v) = (u' - u) + (v' - v) := by
    ring
  rw [heq]
  obtain ⟨hu_lower, hu_upper⟩ := abs_lt.mp hu
  obtain ⟨hv_lower, hv_upper⟩ := abs_lt.mp hv
  apply abs_lt.mpr
  constructor <;> linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit.split
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit.preserve_image
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit.entry_error
