/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Family
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCounts
public import PartitionedTriangleAbsorption.OnePartDivisibility

@[expose] public section

/-!
# The lattice of `Ftriv` is trivial

For a loopless edge set `E` all of whose edges join allowed class pairs of `Ftriv`,

  `IsIntDiv p Ftriv E  ↔  3 ∣ |E|  ∧  every degree is even`

(`isIntDiv_Ftriv_iff_even3`). The forward direction holds for every family of three-element
types (`even3_of_isIntDiv`).

We also give the explicit integral witness with bounded negative mass: every edge set `P`
with `|P| ≤ K` and `IsIntDiv p Ftriv P` has a witness `c` with
`negativeMass Ftriv c ≤ 2 K + 16` (`Ftriv_bounded_coefficients`). The witness is the given one
shifted along the kernel vector `κ = (2, -3, -3, 6, -6, 3, 3, -2)` so that `c₀₁₂ ∈ [0, 6)`.
-/

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12

/-! ### Generic forward direction -/

section Generic

variable {V : Type*} [DecidableEq V] {t : ℕ}

theorem tot_sum {ι : Type*} (S : Finset ι) (f : ι → Fin t → Fin t → ℤ) :
    ∑ i, ∑ j, (∑ s ∈ S, f s) i j = ∑ s ∈ S, ∑ i, ∑ j, f s i j := by
  simp only [Finset.sum_apply]
  rw [sum_congr rfl fun i _ => sum_comm]
  exact sum_comm

theorem pairVec_total (p : V → Fin t) (e : Sym2 V) : ∑ i, ∑ j, pairVec p e i j = 2 := by
  induction e using Sym2.ind with
  | _ a b => simp [pairVec, sum_add_distrib, ite_and]

theorem typeEdgeVec_total {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) :
    ∑ i, ∑ j, typeEdgeVec τ i j = 6 := by
  have h : ∑ j : Fin t, (τ.count j : ℤ) = 3 := by
    exact_mod_cast (Multiset.sum_count_eq_card (by simp)).trans hτ
  simp only [typeEdgeVec, sum_sub_distrib, ← mul_sum, ← sum_mul, h]
  simp [sum_ite_eq, h]

theorem edgeVec_total (p : V → Fin t) (E : Finset (Sym2 V)) :
    ∑ i, ∑ j, edgeVec p E i j = 2 * E.card := by
  rw [edgeVec, tot_sum, sum_congr rfl fun e _ => pairVec_total p e]
  simp [mul_comm]

/-- **Integral divisibility implies ordinary divisibility**, for any family of triangles. -/
theorem even3_of_isIntDiv {F : Finset (Multiset (Fin t))} (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (p : V → Fin t) {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (h : IsIntDiv p F E) : OnePart.Even3 E := by
  refine ⟨?_, even_of_isIntDiv hcard hloop h⟩
  obtain ⟨c, hc⟩ := h.1
  have htot := edgeVec_total p E
  rw [hc, tot_sum] at htot
  have hτ : ∀ τ ∈ F, ∑ i, ∑ j, (c τ • typeEdgeVec τ) i j = 6 * c τ := by
    intro τ hτ
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, typeEdgeVec_total (hcard τ hτ)]
    ring
  rw [sum_congr rfl hτ, ← mul_sum] at htot
  have h3 : (3 : ℤ) ∣ E.card := ⟨∑ τ ∈ F, c τ, by linarith⟩
  exact_mod_cast h3

end Generic

/-! ### Evaluation of the `Ftriv` lattices -/

theorem sum_Ftriv {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ Ftriv, f τ = f {0, 0, 0} + f {0, 0, 1} + f {0, 0, 2} + f {0, 1, 2} +
      f {1, 2, 3} + f {1, 3, 3} + f {2, 3, 3} + f {3, 3, 3} := by
  unfold Ftriv
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  abel

/-- The ordered edge vector of an integer combination of the `Ftriv` types. -/
def trivEdgeMatrix (c000 c001 c002 c012 c123 c133 c233 c333 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![6 * c000 + 2 * c001 + 2 * c002, 2 * c001 + c012, 2 * c002 + c012, 0],
    ![2 * c001 + c012, 0, c012 + c123, c123 + 2 * c133],
    ![2 * c002 + c012, c012 + c123, 0, c123 + 2 * c233],
    ![0, c123 + 2 * c133, c123 + 2 * c233, 2 * c133 + 2 * c233 + 6 * c333]]

theorem edge_lattice_eval (c : Multiset (Fin 4) → ℤ) :
    ∑ τ ∈ Ftriv, c τ • typeEdgeVec τ =
      trivEdgeMatrix (c {0, 0, 0}) (c {0, 0, 1}) (c {0, 0, 2}) (c {0, 1, 2})
        (c {1, 2, 3}) (c {1, 3, 3}) (c {2, 3, 3}) (c {3, 3, 3}) := by
  funext i j
  rw [sum_Ftriv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [typeEdgeVec, trivEdgeMatrix] <;> ring

/-- The kernel vector of the `Ftriv` edge lattice. -/
noncomputable def kappa (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then 2 else if τ = {0, 0, 1} then -3 else if τ = {0, 0, 2} then -3 else
  if τ = {0, 1, 2} then 6 else if τ = {1, 2, 3} then -6 else if τ = {1, 3, 3} then 3 else
  if τ = {2, 3, 3} then 3 else if τ = {3, 3, 3} then -2 else 0

theorem kappa_kernel : ∑ τ ∈ Ftriv, kappa τ • typeEdgeVec τ = 0 := by
  rw [edge_lattice_eval]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [kappa, trivEdgeMatrix] <;> decide

/-- Degree vectors at a vertex of class `a`, as explicit integer vectors. -/
theorem deg_lattice_eval (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ Ftriv with (0 : Fin 4) ∈ τ, c τ • typeDegVec τ 0 =
      ![2 * c {0, 0, 0} + c {0, 0, 1} + c {0, 0, 2}, c {0, 0, 1} + c {0, 1, 2},
        c {0, 0, 2} + c {0, 1, 2}, 0]) ∧
    (∑ τ ∈ Ftriv with (1 : Fin 4) ∈ τ, c τ • typeDegVec τ 1 =
      ![2 * c {0, 0, 1} + c {0, 1, 2}, 0, c {0, 1, 2} + c {1, 2, 3},
        c {1, 2, 3} + 2 * c {1, 3, 3}]) ∧
    (∑ τ ∈ Ftriv with (2 : Fin 4) ∈ τ, c τ • typeDegVec τ 2 =
      ![2 * c {0, 0, 2} + c {0, 1, 2}, c {0, 1, 2} + c {1, 2, 3}, 0,
        c {1, 2, 3} + 2 * c {2, 3, 3}]) ∧
    (∑ τ ∈ Ftriv with (3 : Fin 4) ∈ τ, c τ • typeDegVec τ 3 =
      ![0, c {1, 2, 3} + c {1, 3, 3}, c {1, 2, 3} + c {2, 3, 3},
        c {1, 3, 3} + c {2, 3, 3} + 2 * c {3, 3, 3}]) := by
  have f0 : Ftriv.filter (fun τ => (0 : Fin 4) ∈ τ) = {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}} := by
    unfold Ftriv; decide
  have f1 : Ftriv.filter (fun τ => (1 : Fin 4) ∈ τ) = {{0, 0, 1}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}} := by
    unfold Ftriv; decide
  have f2 : Ftriv.filter (fun τ => (2 : Fin 4) ∈ τ) = {{0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {2, 3, 3}} := by
    unfold Ftriv; decide
  have f3 : Ftriv.filter (fun τ => (3 : Fin 4) ∈ τ) = {{1, 2, 3}, {1, 3, 3}, {2, 3, 3}, {3, 3, 3}} := by
    unfold Ftriv; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f0, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    funext j; fin_cases j <;> simp [typeDegVec] <;> ring
  · rw [f1, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    funext j; fin_cases j <;> simp [typeDegVec] <;> ring
  · rw [f2, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    funext j; fin_cases j <;> simp [typeDegVec] <;> ring
  · rw [f3, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    funext j; fin_cases j <;> simp [typeDegVec] <;> ring


/-! ### Explicit bounded witness -/

theorem pairVec_nonneg {W : Type*} (p : W → Fin 4) (e : Sym2 W) (i j : Fin 4) :
    0 ≤ pairVec p e i j := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [pairVec, Sym2.lift_mk]
    split_ifs <;> norm_num

theorem edgeVec_nonneg {W : Type*} [DecidableEq W] (p : W → Fin 4) (P : Finset (Sym2 W))
    (i j : Fin 4) : 0 ≤ edgeVec p P i j := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  exact sum_nonneg fun e _ => pairVec_nonneg p e i j

theorem kappa_values : kappa {0, 0, 0} = 2 ∧ kappa {0, 0, 1} = -3 ∧ kappa {0, 0, 2} = -3 ∧
    kappa {0, 1, 2} = 6 ∧ kappa {1, 2, 3} = -6 ∧ kappa {1, 3, 3} = 3 ∧ kappa {2, 3, 3} = 3 ∧
    kappa {3, 3, 3} = -2 := by
  unfold kappa; decide

theorem sum_fin4 (f : Fin 4 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

/-- **Explicit bounded witness.** Every integrally `Ftriv`-divisible edge set with at most `K`
edges has an integral witness of negative mass at most `2 K + 16`. -/
theorem Ftriv_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W] (p : W → Fin 4)
    (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p Ftriv P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ Ftriv, c τ • typeEdgeVec τ ∧
      negativeMass Ftriv c ≤ 2 * K + 16 := by
  obtain ⟨c0, hc0⟩ := hdiv.1
  let k : ℤ := c0 {0, 1, 2} / 6
  let c : Multiset (Fin 4) → ℤ := fun τ => c0 τ - k * kappa τ
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ := kappa_values
  have hmat : ∑ τ ∈ Ftriv, c τ • typeEdgeVec τ = ∑ τ ∈ Ftriv, c0 τ • typeEdgeVec τ := by
    rw [edge_lattice_eval, edge_lattice_eval]
    simp only [c, k0, k1, k2, k3, k4, k5, k6, k7]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [trivEdgeMatrix] <;> ring
  refine ⟨c, hmat.trans hc0.symm |>.symm, ?_⟩
  have htot := edgeVec_total p P
  have hX := hc0
  rw [edge_lattice_eval] at hX
  have hnn := edgeVec_nonneg p P
  simp only [sum_fin4] at htot
  rw [hX] at htot hnn
  have n01 := hnn 0 1
  have n02 := hnn 0 2
  have n12 := hnn 1 2
  have n13 := hnn 1 3
  have n23 := hnn 2 3
  have n00 := hnn 0 0
  have n33 := hnn 3 3
  simp only [trivEdgeMatrix, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue] at htot n01 n02 n12 n13 n23 n00 n33
  unfold negativeMass
  rw [sum_Ftriv]
  simp only [c, k0, k1, k2, k3, k4, k5, k6, k7]
  have hKz : (P.card : ℤ) ≤ K := by exact_mod_cast hK
  omega


end PaddedTrivial
