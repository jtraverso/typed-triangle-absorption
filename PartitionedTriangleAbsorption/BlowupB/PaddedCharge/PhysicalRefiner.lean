/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Universal

@[expose] public section

/-!
# The physical ordinary refiner (virtual refiner in `⊤` plus paths of length four)

This isolates the first half of `PaddedNoCommon.universal_budget_walk` as a reusable statement:
for a host `G` with guarded supply and `Walk4` on the allowed-pair graph, and a reserve `X`,
there are a fixed edge set `R' ⊆ G \ X` and a fixed library of `Even3` pieces `P' i ⊆ X ∪ R'` of at
most `168` edges such that EVERY `Even3` leftover `L ⊆ X` is partitioned, together with `R'`, by
pairwise disjoint library pieces. `R'` and the library are chosen before `L`.

The numerical output (degree of `R'`, number of edges of `R'`, size of the library and the
incidence of the library) is what the charge layer needs downstream.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The physical ordinary refiner.** -/
theorem exists_physical_refiner {t : ℕ} (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (hwalk : Walk4 Allowed) (a : ℝ)
    (hs : GuardedSupply p G Allowed 2 a)
    (lam rho Q : ℝ)
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hQ : 0 < Q)
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < a)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3)) (P' : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V))
      (R' : Finset (Sym2 V)),
      R' ⊆ G.edgeFinset ∧ Disjoint R' X ∧
      (∀ L ⊆ X, OnePart.Even3 L → ∃ s ⊆ indices,
        (s : Set (ℕ × Bool × Fin 3 × Fin 3)).PairwiseDisjoint P' ∧ s.biUnion P' = R' ∪ L) ∧
      (∀ i ∈ indices, P' i ⊆ X ∪ R' ∧ P' i ⊆ G.edgeFinset ∧ OnePart.Even3 (P' i) ∧
        (P' i).card ≤ 168) ∧
      DegBounded R' (4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1))) ∧
      (R'.card : ℝ) ≤ 16 * lam * (Fintype.card V : ℝ) ^ 2 ∧
      (indices.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤
        4096 * lam * Fintype.card V + 2 * (Q + (4096 * lam * Fintype.card V + 1)) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hn4 : 4 ≤ Fintype.card V := by
    have h1 : (2 ^ 14 : ℝ) ≤ n := by
      have := mul_le_mul_of_nonneg_right hlam64 hn0
      nlinarith
    have : ((4 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by rw [← hn]; push_cast; linarith
    exact_mod_cast this
  have hloopG : ∀ P ⊆ G.edgeFinset, ∀ e ∈ P, ¬ e.IsDiag :=
    fun P hP e he => G.not_isDiag_of_mem_edgeFinset (hP he)
  have hXtop : X ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro e he
    have hnd := hloopG X hXG e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      intro hab; exact hnd (by simp [hab])
  obtain ⟨indices, P, R, hRtop, hRX, href, hpieces, hRdeg, hcardI, hinc⟩ :=
    exists_universal_refiner_alpha (⊤ : SimpleGraph V) X hXtop lam rho hlam hlam64 hrho
      (by nlinarith only [hscale, hrho.le]) hn1 hn2 hX (1 / 2) (by linarith)
      (antiEdgeful_top hn4)
  have hRloop : ∀ e ∈ R, ¬ e.IsDiag := fun e he =>
    (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeFinset (hRtop he)
  let wt : Sym2 V → ℕ := fun e => (∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1
  have hwt1 : ∀ e ∈ R, 1 ≤ wt e := fun e _ => Nat.le_add_left _ _
  have hwtM : ∀ e ∈ R, (wt e : ℝ) ≤ 4096 * lam * n + 1 := by
    intro e _
    have h1 := multiplicity_le_incidence P indices e
    have h2 : ((∑ i ∈ indices, incidentLoad (P i) (endU e) : ℕ) : ℝ) ≤ 4096 * lam * n :=
      hinc (endU e)
    have h3 : ((∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤ 4096 * lam * n :=
      le_trans (by exact_mod_cast h1) h2
    change (((∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hW : ∑ e ∈ R, (wt e : ℝ) ≤ 4100 * lam * n ^ 2 := by
    have h1 := sum_multiplicity_le P indices R
    have h2 : ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) ≤ n * (4096 * lam * n) := by
      calc ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ)
          = ∑ w, ((∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := Nat.cast_sum _ _
        _ ≤ ∑ _w : V, 4096 * lam * n := sum_le_sum fun w _ => hinc w
        _ = n * (4096 * lam * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
    have h3 := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have hsum : ∑ e ∈ R, (wt e : ℝ) =
        ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) + R.card := by
      simp only [wt]
      push_cast
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    have h1' : ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤
        ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hsum]
    change _ ≤ n * (4 * lam * n) at h3
    nlinarith
  obtain ⟨x, y, z, hpath, havoid, hdisj, hint⟩ := exists_path_system p G Allowed a
    hs hwalk X R hRloop (2 * rho * n) (4 * lam * n) hX hRdeg wt
    (4096 * lam * n + 1) (4100 * lam * n ^ 2) Q hwt1 hwtM hW (by positivity) (by positivity)
    (by positivity) hQ hpathB
  have hsys : PathSystem G X R x y z := ⟨hRX, hRloop, hpath, havoid, hdisj⟩
  set R' := R.biUnion (physPath x y z) with hR'
  let P' : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V) := fun i => physPiece X x y z (P i)
  have hR'G : R' ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun e he => pathEdges_subset (hpath e he)
  have hR'X : Disjoint R' X := (disjoint_biUnion_left _ _ _).mpr fun e he => havoid e he
  have hPsub : ∀ i ∈ indices, P i ⊆ X ∪ R := fun i hi => (hpieces i hi).1
  refine ⟨indices, P', R', hR'G, hR'X, ?_, ?_, ?_, ?_, hcardI, ?_⟩
  · intro L hL h3
    have hloop := hloopG L (hL.trans hXG)
    obtain ⟨s, hs_sub, hsdis, hsU⟩ := href L hL ((OnePart.isIntDiv_part1_iff L hloop).mpr h3)
    exact ⟨s, hs_sub, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL
      hsU).1, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL hsU).2⟩
  · intro i hi
    have hE3 : OnePart.Even3 (P i) := ⟨(hpieces i hi).2.2.2.1, (hpieces i hi).2.2.1⟩
    exact ⟨hsys.physPiece_subset (hPsub i hi), hsys.physPiece_subset_G hXG (hPsub i hi),
      hsys.physPiece_even3 (hPsub i hi) hE3,
      (hsys.physPiece_card_le (hPsub i hi)).trans (by have := (hpieces i hi).2.2.2.2; omega)⟩
  · intro v
    have h1 := incidentLoad_biUnion_physPath_le R x y z hRloop hpath wt hwt1 v
    have h1' : ((incidentLoad R' v : ℕ) : ℝ) ≤
        (incidentLoad R v : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by exact_mod_cast h1
    have h2 := hRdeg v
    have h3 := hint v
    change ((incidentLoad R' v : ℕ) : ℝ) ≤ _
    change ((incidentLoad R v : ℕ) : ℝ) ≤ _ at h2
    linarith
  · have hRc := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have : R'.card ≤ ∑ e ∈ R, (physPath x y z e).card := card_biUnion_le
    have h4 : ∑ e ∈ R, (physPath x y z e).card = ∑ _e ∈ R, 4 :=
      sum_congr rfl fun e he => pathEdges_card (ends_ne (hRloop e he)) (hpath e he)
    rw [h4, sum_const, smul_eq_mul] at this
    have hR'c : (R'.card : ℝ) ≤ R.card * 4 := by exact_mod_cast this
    change (R.card : ℝ) ≤ n * (4 * lam * n) at hRc
    nlinarith
  · intro v
    have h1 := hsys.sum_physPiece_incidentLoad P indices hPsub wt
      (fun e _ => Nat.le_succ _) v
    have h1' : ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by
      exact_mod_cast h1
    have h2 := hinc v
    have h3 := hint v
    linarith

end PaddedCharge

#print axioms PaddedCharge.exists_physical_refiner
