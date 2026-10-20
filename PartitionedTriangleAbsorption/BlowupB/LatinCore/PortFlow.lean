/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CapacitatedFlowFeasibility
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DirectedFlowIncidence
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding

@[expose] public section

/-! Integer currents with asymmetric capacities. Oppositely directed and parallel
channels are accounted for by their aggregate capacities, not copied graph edges.
This supplies the integral-current stage, not a channel-network producer or a
physical embedding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PortFlow

open Finset Matrix OrientedCycleVector

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every zero-sum unit demand is bounded by the smaller side of each cut. -/
theorem unit_demand_cut (b : V → ℤ) (hsum : ∑ v, b v = 0)
    (hb : ∀ v, |(b v : ℝ)| ≤ 1) (S : Finset V) :
    ∑ v ∈ S, (b v : ℝ) ≤ min (S.card : ℝ) (Sᶜ.card : ℝ) := by
  have hS : ∑ v ∈ S, (b v : ℝ) ≤ S.card := by
    calc
      _ ≤ ∑ _v ∈ S, (1 : ℝ) := sum_le_sum fun v _ => (abs_le.mp (hb v)).2
      _ = _ := by simp
  have hC : -(∑ v ∈ Sᶜ, (b v : ℝ)) ≤ Sᶜ.card := by
    calc
      _ = ∑ v ∈ Sᶜ, -(b v : ℝ) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ _v ∈ Sᶜ, (1 : ℝ) := sum_le_sum fun v _ => by
        have := (abs_le.mp (hb v)).1
        linarith
      _ = _ := by simp
  have hz : (∑ v ∈ S, (b v : ℝ)) + ∑ v ∈ Sᶜ, (b v : ℝ) = 0 := by
    rw [sum_add_sum_compl]
    exact_mod_cast hsum
  exact le_min hS (by linarith)

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

include ho

/-- Cut feasibility and box rounding produce an integer current. In the chosen
orientation the lower bound is minus the REVERSE capacity, not minus the forward
capacity. This distinction is essential for directed port channels. -/
theorem integer_current_of_cut (cap : V → V → ℕ)
    (hsupport : ∀ u v, ¬G.Adj u v → cap u v = 0)
    (b : V → ℤ) (hsum : ∑ v, b v = 0)
    (hcut : ∀ S : Finset V, ∑ v ∈ S, (b v : ℝ) ≤
      ∑ u ∈ Sᶜ, ∑ v ∈ S, (cap u v : ℝ)) :
    ∃ z : G.edgeSet → ℤ,
      (incidence G o).mulVecLin (fun e => (z e : ℝ)) = (fun v => (b v : ℝ)) ∧
      ∀ e, -(cap (o e).snd (o e).fst : ℤ) ≤ z e ∧
        z e ≤ (cap (o e).fst (o e).snd : ℤ) := by
  classical
  obtain ⟨f, hf0, hfcap, hfdiv⟩ := Nibble.Flow.exists_feasible_of_cut
    (fun u v => (cap u v : ℝ)) (fun v => (b v : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (by exact_mod_cast hsum) hcut
  have hf : ∀ u v, ¬G.Adj u v → f u v = 0 := by
    intro u v huv
    have hupper := hfcap u v
    change f u v ≤ (cap u v : ℝ) at hupper
    rw [hsupport u v huv, Nat.cast_zero] at hupper
    exact le_antisymm hupper (hf0 u v)
  let a := DirectedFlowIncidence.signed G o f
  have ha : (incidence G o).mulVecLin a = fun v => (b v : ℝ) := by
    dsimp only [a]
    rw [DirectedFlowIncidence.signed_divergence G o ho f hf]
    exact funext hfdiv
  have hint : ∀ v, (incidence G o).mulVecLin a v ∈ Set.range (Int.cast : ℤ → ℝ) := by
    intro v
    rw [ha]
    exact ⟨b v, rfl⟩
  have hbox : ∀ e,
      (-(cap (o e).snd (o e).fst : ℤ) : ℝ) ≤ a e ∧
      a e ≤ ((cap (o e).fst (o e).snd : ℤ) : ℝ) := by
    intro e
    dsimp [a]
    rw [DirectedFlowIncidence.signed_entry G o ho]
    push_cast
    constructor <;> linarith [hf0 (o e).fst (o e).snd, hf0 (o e).snd (o e).fst,
      hfcap (o e).fst (o e).snd, hfcap (o e).snd (o e).fst]
  obtain ⟨z, hz, hzb⟩ := NetworkFlowRounding.round_box G o ho a
    (fun e => -(cap (o e).snd (o e).fst : ℤ))
    (fun e => (cap (o e).fst (o e).snd : ℤ))
    (by simpa only [Int.cast_neg] using hbox) hint
  exact ⟨z, hz.trans ha, hzb⟩

/-- Incoming cut capacity at least the smaller side can route every zero-sum
unit demand integrally. The network itself is fixed before the demand. -/
theorem integer_current_of_unit_expansion (cap : V → V → ℕ)
    (hsupport : ∀ u v, ¬G.Adj u v → cap u v = 0)
    (hexp : ∀ S : Finset V, min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
      ∑ u ∈ Sᶜ, ∑ v ∈ S, (cap u v : ℝ))
    (b : V → ℤ) (hsum : ∑ v, b v = 0) (hb : ∀ v, |(b v : ℝ)| ≤ 1) :
    ∃ z : G.edgeSet → ℤ,
      (incidence G o).mulVecLin (fun e => (z e : ℝ)) = (fun v => (b v : ℝ)) ∧
      ∀ e, -(cap (o e).snd (o e).fst : ℤ) ≤ z e ∧
        z e ≤ (cap (o e).fst (o e).snd : ℤ) :=
  integer_current_of_cut G o ho cap hsupport b hsum
    (fun S => (unit_demand_cut b hsum hb S).trans (hexp S))

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PortFlow
