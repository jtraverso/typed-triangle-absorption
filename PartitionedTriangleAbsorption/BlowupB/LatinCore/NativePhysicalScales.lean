/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEmbeddingBudget

@[expose] public section

/-! The native sparsity and smallness assumptions supply the scales used
by the physical catalogue constructor. Directed degree counts both ends. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.NativePhysicalScales

open Finset Cycles

theorem total_degree {V : Type} [Fintype V] [DecidableEq V] (X : Finset (V × V)) :
    ∑ v, deg X v = 2 * X.card := by
  have h := CataloguePrecharge.total_degree ({X} : Finset (Finset (V × V)))
  have hArc : CatalogueWeights.arcs {X} = X := by
    ext e
    constructor
    · intro he
      obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
      have hPX : P = X := mem_singleton.mp hP
      subst P
      exact heP
    · intro he
      exact mem_biUnion.mpr ⟨X, mem_singleton_self X, he⟩
  have hw : (∑ e ∈ CatalogueWeights.arcs {X}, CatalogueWeights.weight {X} e) = X.card := by
    rw [hArc]
    calc _ = ∑ _e ∈ X, 1 := sum_congr rfl (fun e he => by
            simp [CatalogueWeights.weight, filter_singleton, he])
      _ = _ := by simp
  rw [hw] at h
  simpa only [catalogLoad, sum_singleton] using h

theorem input_card {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V × V)) (rho : ℝ)
    (hdeg : ∀ v, (deg X v : ℝ) ≤ 2 * rho * Fintype.card V) :
    (X.card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2 := by
  have hsum : (∑ v, (deg X v : ℝ)) = 2 * (X.card : ℝ) := by exact_mod_cast total_degree X
  have hbound := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hdeg v)
  rw [hsum, sum_const, card_univ, nsmul_eq_mul] at hbound
  nlinarith

theorem small_of_power (q : ℕ) (lam ω : ℝ) (hlam : 0 ≤ lam)
    (h : (2 : ℝ) ^ q * lam ≤ ω ^ 3) : (q : ℝ) * lam ≤ ω ^ 3 := by
  have hp : (q : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast (show q < 2 ^ q from Nat.lt_two_pow_self).le
  exact (mul_le_mul_of_nonneg_right hp hlam).trans h

theorem parameters (q : ℕ) (ω lam rho n : ℝ) (hq : 1 ≤ (q : ℝ))
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hlam : 0 < lam) (hrho : 0 < rho)
    (hsmall : (q : ℝ) * lam ≤ ω ^ 3) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hsize : 1 ≤ rho * n) :
    0 < lam / 4096 ∧ lam / 4096 ≤ 1 ∧ 0 < n ∧
      rho ≤ (lam / 4096) ^ 2 ∧ 1 ≤ (lam / 4096) ^ 2 * n ∧
      32 * (q : ℝ) * (lam / 4096) ≤ ω ∧ 4096 * (lam / 4096) ≤ lam := by
  have hn : 0 < n := by nlinarith
  have hω2 : ω * ω ≤ ω := mul_le_of_le_one_right hω.le hω1
  have hω3 : ω ^ 3 ≤ 1 := by nlinarith
  have hlam1 : lam ≤ 1 := by nlinarith
  have hρt : rho ≤ (lam / 4096) ^ 2 := by norm_num at hscale; nlinarith
  have htn : 1 ≤ (lam / 4096) ^ 2 * n :=
    hsize.trans (mul_le_mul_of_nonneg_right hρt hn.le)
  have heq : 4096 * (lam / 4096) ≤ lam := by linarith
  exact ⟨by positivity, by linarith, hn, hρt, htn,
    WeightedEmbeddingBudget.scale q (lam / 4096) lam ω (by linarith) hω.le hω1 heq hsmall, heq⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.NativePhysicalScales

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.NativePhysicalScales.input_card
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.NativePhysicalScales.parameters
