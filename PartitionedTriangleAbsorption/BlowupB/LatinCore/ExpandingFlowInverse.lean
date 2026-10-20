/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CapacitatedFlowFeasibility
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence

@[expose] public section

/-! A bounded real incidence inverse from edge expansion, using the
already proved finite capacitated-flow feasibility theorem. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ExpandingFlowInverse

open Finset Matrix OrientedCycleVector

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def cutSize (S : Finset V) : ℝ := by
  classical
  exact ∑ u ∈ Sᶜ, ∑ v ∈ S, if G.Adj u v then 1 else 0

def Expands (h : ℝ) : Prop := ∀ S : Finset V,
  h * min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ cutSize G S

theorem demand_cut_bound (g : V → ℝ) (M : ℝ) (hg : ∑ v, g v = 0)
    (hM : ∀ v, |g v| ≤ M) (S : Finset V) :
    ∑ v ∈ S, g v ≤ M * min (S.card : ℝ) (Sᶜ.card : ℝ) := by
  classical
  have hsum : ∑ v ∈ S, g v + ∑ v ∈ Sᶜ, g v = 0 := by
    rw [Finset.sum_add_sum_compl, hg]
  have h1 : ∑ v ∈ S, g v ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ v ∈ S, M := Finset.sum_le_sum fun v _ => (abs_le.mp (hM v)).2
      _ = _ := by simp
  have h2 : -(Sᶜ.card : ℝ) * M ≤ ∑ v ∈ Sᶜ, g v := by
    calc
      _ = ∑ v ∈ Sᶜ, -M := by simp
      _ ≤ _ := Finset.sum_le_sum fun v _ => (abs_le.mp (hM v)).1
  rcases le_total (S.card : ℝ) (Sᶜ.card : ℝ) with hh | hh
  · rw [min_eq_left hh]
    nlinarith
  · rw [min_eq_right hh]
    nlinarith

variable (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

include ho in
/-- Every zero-sum real demand bounded by M has a physical oriented flow
bounded by M/h when all graph cuts expand by h. -/
theorem bounded_preimage (h : ℝ) (hh : 0 < h) (hexp : Expands G h)
    (g : V → ℝ) (hg : ∑ v, g v = 0) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ v, |g v| ≤ M) :
    ∃ f : G.edgeSet → ℝ, (incidence G o).mulVecLin f = g ∧
      ∀ e, |f e| ≤ M / h := by
  classical
  let cap : V → V → ℝ := fun u v => if G.Adj u v then M / h else 0
  have hC : 0 ≤ M / h := div_nonneg hM0 hh.le
  have hcap : ∀ u v, 0 ≤ cap u v := by
    intro u v
    dsimp [cap]
    split_ifs <;> positivity
  have hcut : ∀ S : Finset V, ∑ v ∈ S, g v ≤ ∑ u ∈ Sᶜ, ∑ v ∈ S, cap u v := by
    intro S
    calc
      _ ≤ M * min (S.card : ℝ) (Sᶜ.card : ℝ) := demand_cut_bound g M hg hM S
      _ = (M / h) * (h * min (S.card : ℝ) (Sᶜ.card : ℝ)) := by field_simp
      _ ≤ (M / h) * cutSize G S := mul_le_mul_of_nonneg_left (hexp S) hC
      _ = _ := by
        simp only [cutSize, cap, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  obtain ⟨f, hfnn, hfcap, hfdiv⟩ := Nibble.Flow.exists_feasible_of_cut cap g hcap hg hcut
  have hzero : ∀ u v, ¬ G.Adj u v → f u v = 0 := by
    intro u v huv
    exact le_antisymm (by simpa [cap, huv] using hfcap u v) (hfnn u v)
  refine ⟨DirectedFlowIncidence.signed G o f, ?_, ?_⟩
  · rw [DirectedFlowIncidence.signed_divergence G o ho f hzero]
    funext v
    exact hfdiv v
  · apply DirectedFlowIncidence.signed_bound G o ho f (M / h) hfnn
    intro u v
    by_cases huv : G.Adj u v
    · simpa [cap, huv] using hfcap u v
    · rw [hzero u v huv]
      exact hC

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ExpandingFlowInverse

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ExpandingFlowInverse.bounded_preimage
