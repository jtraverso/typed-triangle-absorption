/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ExpandingFlowInverse
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.BoundedIntegerFilling

@[expose] public section

/-! The real rectangular inverse by two scalar flow inverses and row
centering. This avoids a separate tensor separation/coarea proof. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RealTensorFilling

open Finset Matrix OrientedCycleVector

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty B] (GA : SimpleGraph A) (GB : SimpleGraph B)
    [DecidableRel GA.Adj] [DecidableRel GB.Adj]
    (oa : GA.edgeSet → GA.Dart) (ob : GB.edgeSet → GB.Dart)
    (hoa : ∀ e, (oa e).edge = e.val) (hob : ∀ e, (ob e).edge = e.val)

include hoa hob in
/-- A real zero-margin matrix bounded by M has a bilateral preimage
bounded by 2 M/(hA hB). Each scalar lifting follows from cut expansion. -/
theorem bounded_real_preimage (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hexA : ExpandingFlowInverse.Expands GA hA) (hexB : ExpandingFlowInverse.Expands GB hB)
    (x : Matrix A B ℝ) (hcol : ∀ b, ∑ a, x a b = 0)
    (hrow : ∀ a, ∑ b, x a b = 0) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ a b, |x a b| ≤ M) :
    ∃ c : Matrix GA.edgeSet GB.edgeSet ℝ,
      incidence GA oa * c * (incidence GB ob).transpose = x ∧
        ∀ e f, |c e f| ≤ 2 * M / (hA * hB) := by
  classical
  let n : ℝ := Fintype.card B
  have hn : 0 < n := by
    change (0 : ℝ) < Fintype.card B
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hK : 0 ≤ M / hA := div_nonneg hM hhA.le
  have hcols : ∀ b : B, ∃ u : GA.edgeSet → ℝ,
      (incidence GA oa).mulVecLin u = (fun a => x a b) ∧ ∀ e, |u e| ≤ M / hA := by
    intro b
    exact ExpandingFlowInverse.bounded_preimage GA oa hoa hA hhA hexA
      (fun a => x a b) (hcol b) M hM (fun a => hx a b)
  choose u hu hbu using hcols
  let avg : GA.edgeSet → ℝ := fun e => (∑ b, u b e) / n
  let s : Matrix GA.edgeSet B ℝ := fun e b => u b e - avg e
  have havg : ∀ e, |avg e| ≤ M / hA := by
    intro e
    have hlo : ∑ b, -(M / hA) ≤ ∑ b, u b e :=
      Finset.sum_le_sum fun b _ => (abs_le.mp (hbu b e)).1
    have hhi : ∑ b, u b e ≤ ∑ b, M / hA :=
      Finset.sum_le_sum fun b _ => (abs_le.mp (hbu b e)).2
    have hlo' : - (M / hA) * n ≤ ∑ b, u b e := by
      simpa [n, mul_comm] using hlo
    have hhi' : ∑ b, u b e ≤ (M / hA) * n := by
      simpa [n, mul_comm] using hhi
    apply abs_le.mpr
    exact ⟨(le_div_iff₀ hn).mpr hlo', (div_le_iff₀ hn).mpr hhi'⟩
  have hsbound : ∀ e b, |s e b| ≤ 2 * (M / hA) := by
    intro e b
    obtain ⟨hl, hr⟩ := abs_le.mp (hbu b e)
    obtain ⟨hal, har⟩ := abs_le.mp (havg e)
    apply abs_le.mpr
    change -(2 * (M / hA)) ≤ u b e - avg e ∧ u b e - avg e ≤ 2 * (M / hA)
    constructor <;> linarith
  have hsrow : ∀ e, ∑ b, s e b = 0 := by
    intro e
    simp only [s, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change (∑ b, u b e) - n * ((∑ b, u b e) / n) = 0
    field_simp <;> ring
  have havgzero : ∀ a, ∑ e, incidence GA oa a e * avg e = 0 := by
    intro a
    calc
      _ = (∑ e, ∑ b, incidence GA oa a e * u b e) / n := by
        simp only [avg, div_eq_mul_inv, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      _ = (∑ b, ∑ e, incidence GA oa a e * u b e) / n := by rw [Finset.sum_comm]
      _ = (∑ b, x a b) / n := by
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        exact congrFun (hu b) a
      _ = 0 := by rw [hrow a, zero_div]
  have hsimage : incidence GA oa * s = x := by
    ext a b
    change (∑ e, incidence GA oa a e * (u b e - avg e)) = x a b
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [havgzero a, sub_zero]
    exact congrFun (hu b) a
  have hrows : ∀ e : GA.edgeSet, ∃ c : GB.edgeSet → ℝ,
      (incidence GB ob).mulVecLin c = (fun b => s e b) ∧
        ∀ f, |c f| ≤ (2 * (M / hA)) / hB := by
    intro e
    exact ExpandingFlowInverse.bounded_preimage GB ob hob hB hhB hexB
      (fun b => s e b) (hsrow e) (2 * (M / hA)) (by positivity) (hsbound e)
  choose c hc hbc using hrows
  let cm : Matrix GA.edgeSet GB.edgeSet ℝ := c
  refine ⟨cm, ?_, ?_⟩
  · have hright : cm *
        (incidence GB ob).transpose = s := by
      ext e b
      have hh := congrFun (hc e) b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, mul_comm] using hh
    rw [Matrix.mul_assoc, hright, hsimage]
  · intro e f
    convert hbc e f using 1 <;> field_simp <;> ring

include hoa hob in
/-- A bounded integer rectangular producer. Cut expansion constructs the
real filling; the previously checked rounding constructs its integer lift. -/
theorem bounded_integer_preimage (hGA : GA.Connected) (hGB : GB.Connected)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hexA : ExpandingFlowInverse.Expands GA hA) (hexB : ExpandingFlowInverse.Expands GB hB)
    (x : Matrix A B ℤ) (hcol : ∀ b, ∑ a, x a b = 0)
    (hrow : ∀ a, ∑ b, x a b = 0) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ a b, |(x a b : ℝ)| ≤ M) :
    ∃ c : Matrix GA.edgeSet GB.edgeSet ℤ,
      incidence GA oa * c.map (Int.castRingHom ℝ) * (incidence GB ob).transpose =
        x.map (Int.castRingHom ℝ) ∧ ∀ e f, |(c e f : ℝ)| < 2 * M / (hA * hB) + 2 := by
  have hcolr : ∀ b, ∑ a, (x.map (Int.castRingHom ℝ)) a b = 0 := by
    intro b
    change (∑ a, (x a b : ℝ)) = 0
    exact_mod_cast hcol b
  have hrowr : ∀ a, ∑ b, (x.map (Int.castRingHom ℝ)) a b = 0 := by
    intro a
    change (∑ b, (x a b : ℝ)) = 0
    exact_mod_cast hrow a
  obtain ⟨c, hc, hbound⟩ := bounded_real_preimage GA GB oa ob hoa hob hA hB hhA hhB
    hexA hexB (x.map (Int.castRingHom ℝ)) hcolr hrowr M hM hx
  exact BoundedIntegerFilling.bounded_integer_preimage GA GB oa ob hoa hob hGA hGB
    x c hc (2 * M / (hA * hB)) hbound

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RealTensorFilling

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RealTensorFilling.bounded_real_preimage
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RealTensorFilling.bounded_integer_preimage
