/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.TensorKernelSplit

@[expose] public section

/-! An actual producer of the projection used in tensor-incidence rounding.
A linear section of the range replaces the spanning-tree construction. No
norm bound on this projection is needed by the rounding proof. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection

open Matrix

section Linear

variable {U W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup W] [Module ℝ W]

/-- Every real linear map admits a divergence-preserving projection that
kills its kernel. The section is constructed, not a hypothesis. -/
theorem exists_projection (f : U →ₗ[ℝ] W) :
    ∃ p : U →ₗ[ℝ] U,
      (∀ x, f (p x) = f x) ∧ (∀ x, f x = 0 → p x = 0) := by
  obtain ⟨s, hs⟩ :=
    f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  refine ⟨s.comp f.rangeRestrict, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
  · intro x hx
    have hx' : f.rangeRestrict x = 0 := Subtype.ext hx
    change s (f.rangeRestrict x) = 0
    rw [hx', map_zero]

end Linear

section Matrix

variable {A E F B : Type*} [Fintype E] [Fintype F]

/-- Matrix form of the producer, including the columnwise kernel property
required by `TensorKernelSplit.split`. -/
theorem exists_matrix_projection (left : Matrix A E ℝ) :
    ∃ proj : Matrix E E ℝ,
      left * proj = left ∧
      (∀ z : Matrix E B ℝ, left * z = 0 → proj * z = 0) := by
  classical
  obtain ⟨p, hp, hk⟩ := exists_projection left.mulVecLin
  refine ⟨LinearMap.toMatrix' p, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    exact hp x
  · intro z hz
    ext i j
    change ((LinearMap.toMatrix' p) *ᵥ (fun e => z e j)) i = 0
    rw [LinearMap.toMatrix'_mulVec]
    apply congrFun (hk (fun e => z e j) ?_) i
    funext a
    exact congrFun (congrFun hz a) j

/-- Unconditional kernel splitting for two finite real matrices. This
discharges the projection assumption of the earlier algebraic lemma. -/
theorem split (left : Matrix A E ℝ) (right : Matrix F B ℝ)
    (d : Matrix E F ℝ) (hd : left * d * right = 0) :
    ∃ u v : Matrix E F ℝ,
      d = u + v ∧ left * u = 0 ∧ v * right = 0 := by
  obtain ⟨proj, hp, hk⟩ := exists_matrix_projection (B := B) left
  exact TensorKernelSplit.split left right proj d hp hk hd

end Matrix

end PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection.exists_projection
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection.exists_matrix_projection
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.IncidenceProjection.split
