/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module


@[expose] public section

/-
# Nibble — feasible flows in a finite network (Gale–Hoffman / max-flow–min-cut)

A self-contained, reusable feasibility theorem for finite capacitated networks, in *divergence*
form:

  given nonnegative capacities `cap x y` on the arcs of a finite complete digraph and a balanced
  demand vector `b` (`∑ b = 0`), there is a flow `0 ≤ f ≤ cap` whose divergence is exactly `b`
  **iff** every vertex cut satisfies `∑_{x ∈ S} b x ≤ ∑_{x ∉ S} ∑_{y ∈ S} cap x y`.

* `Nibble.Flow.netFlow` — the divergence (net inflow) of a flow at a node.
* `Nibble.Flow.IsFeasible` — a flow within the capacities with prescribed divergence.
* `Nibble.Flow.cut_le_of_feasible` — the easy direction.
* `Nibble.Flow.exists_feasible_of_cut` — **the theorem**: the cut condition suffices.

The proof is the usual augmenting-path argument, run on a minimiser of the total unmet demand over
the (compact) box of sub-capacity flows.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic

open Finset

namespace Nibble.Flow

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The **divergence** of `f` at `x`: total inflow minus total outflow. -/
def netFlow (f : N → N → ℝ) (x : N) : ℝ := (∑ y, f y x) - (∑ y, f x y)

omit [DecidableEq N] in
/-- Divergences always sum to zero. -/
theorem sum_netFlow (f : N → N → ℝ) : ∑ x, netFlow f x = 0 := by
  classical
  simp only [netFlow, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp

/-- **The divergence of a set** is the net flow entering it from outside. -/
theorem sum_netFlow_eq (f : N → N → ℝ) (S : Finset N) :
    ∑ x ∈ S, netFlow f x = (∑ x ∈ Sᶜ, ∑ y ∈ S, f x y) - (∑ y ∈ S, ∑ x ∈ Sᶜ, f y x) := by
  classical
  have h1 : ∀ x, netFlow f x = (∑ y ∈ S, f y x) + (∑ y ∈ Sᶜ, f y x)
      - ((∑ y ∈ S, f x y) + (∑ y ∈ Sᶜ, f x y)) := by
    intro x
    rw [netFlow, ← Finset.sum_add_sum_compl S (fun y => f y x),
      ← Finset.sum_add_sum_compl S (fun y => f x y)]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ x ∈ S, ∑ y ∈ S, f y x = ∑ x ∈ S, ∑ y ∈ S, f x y := Finset.sum_comm
  have h3 : ∑ x ∈ S, ∑ y ∈ Sᶜ, f y x = ∑ y ∈ Sᶜ, ∑ x ∈ S, f y x := Finset.sum_comm
  rw [h2, h3]
  ring

/-- `f` is a **feasible flow** for capacities `cap` and demands `b`. -/
def IsFeasible (cap : N → N → ℝ) (b : N → ℝ) (f : N → N → ℝ) : Prop :=
  (∀ x y, 0 ≤ f x y) ∧ (∀ x y, f x y ≤ cap x y) ∧ (∀ x, netFlow f x = b x)

/-! ### The easy direction -/

/-- **Necessity of the cut condition.** -/
theorem cut_le_of_feasible {cap : N → N → ℝ} {b : N → ℝ} {f : N → N → ℝ}
    (hf : IsFeasible cap b f) (S : Finset N) :
    ∑ x ∈ S, b x ≤ ∑ x ∈ Sᶜ, ∑ y ∈ S, cap x y := by
  classical
  obtain ⟨hnn, hle, hdiv⟩ := hf
  have hb : ∑ x ∈ S, b x = ∑ x ∈ S, netFlow f x :=
    Finset.sum_congr rfl (fun x _ => (hdiv x).symm)
  rw [hb, sum_netFlow_eq f S]
  have h3 : (0:ℝ) ≤ ∑ y ∈ S, ∑ x ∈ Sᶜ, f y x :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => hnn y x
  have h4 : ∑ x ∈ Sᶜ, ∑ y ∈ S, f x y ≤ ∑ x ∈ Sᶜ, ∑ y ∈ S, cap x y :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hle x y
  linarith only [h3, h4]

/-! ### Arc updates -/

/-- Add `t` to the flow on the single arc `p → q`. -/
def addArc (f : N → N → ℝ) (p q : N) (t : ℝ) : N → N → ℝ :=
  fun x y => f x y + (if x = p ∧ y = q then t else 0)

theorem netFlow_addArc (f : N → N → ℝ) (p q : N) (t : ℝ) (x : N) :
    netFlow (addArc f p q t) x
      = netFlow f x + (if x = q then t else 0) - (if x = p then t else 0) := by
  classical
  simp only [netFlow, addArc, Finset.sum_add_distrib]
  have h1 : ∑ y : N, (if y = p ∧ x = q then t else 0) = (if x = q then t else 0) := by
    by_cases hx : x = q
    · simp [hx]
    · simp [hx]
  have h2 : ∑ y : N, (if x = p ∧ y = q then t else 0) = (if x = p then t else 0) := by
    by_cases hx : x = p
    · simp [hx]
    · simp [hx]
  rw [h1, h2]
  ring

/-! ### The augmenting-path argument -/

omit [Fintype N] in
theorem addArc_apply (f : N → N → ℝ) (p q x y : N) (t : ℝ) :
    addArc f p q t x y = f x y + (if x = p ∧ y = q then t else 0) := rfl

/-- `residual cap f z y` holds when the node `y` can send *additional* net flow to the node `z`:
either the arc `y → z` is unsaturated, or the arc `z → y` carries flow that can be cancelled. -/
def residual (cap f : N → N → ℝ) (z y : N) : Prop := f y z < cap y z ∨ 0 < f z y

/-- **Augmentation along a residual chain.**  If `y` can reach `x₀` through residual arcs, then an
arbitrarily small amount of divergence can be moved from `y` to `x₀` while staying in the box. -/
theorem exists_augment {cap f : N → N → ℝ} (hnn : ∀ x y, 0 ≤ f x y) (hle : ∀ x y, f x y ≤ cap x y)
    {x₀ y : N} (hreach : Relation.ReflTransGen (residual cap f) x₀ y) :
    ∀ ε : ℝ, 0 < ε → ∃ (t : ℝ) (f' : N → N → ℝ), 0 < t ∧ t ≤ ε ∧
      (∀ p q, |f' p q - f p q| ≤ ε) ∧ (∀ p q, 0 ≤ f' p q) ∧ (∀ p q, f' p q ≤ cap p q) ∧
      (∀ z, netFlow f' z
        = netFlow f z + (if z = x₀ then t else 0) - (if z = y then t else 0)) := by
  classical
  induction hreach with
  | refl =>
      intro ε hε
      refine ⟨ε, f, hε, le_rfl, fun p q => by simp [hε.le], hnn, hle, fun z => by ring⟩
  | @tail y z hxy hyz ih =>
      intro ε hε
      by_cases hzy : z = y
      · subst hzy
        exact ih ε hε
      have hyz' : ¬ (y = z) := fun h => hzy h.symm
      -- the positive amount of room on the arc we are about to modify
      set s : ℝ := if f z y < cap z y then cap z y - f z y else f y z with hs
      have hspos : 0 < s := by
        rw [hs]
        rcases hyz with h | h
        · rw [if_pos h]; linarith only [h]
        · by_cases h' : f z y < cap z y
          · rw [if_pos h']; linarith only [h']
          · rw [if_neg h']; exact h
      set ε' : ℝ := min ε s / 2 with hε'
      have hε'pos : 0 < ε' := by
        rw [hε']
        have : 0 < min ε s := lt_min hε hspos
        linarith only [this]
      have hε'ε : 2 * ε' ≤ ε := by
        rw [hε']; have := min_le_left ε s; linarith only [this]
      have hε's : 2 * ε' ≤ s := by
        rw [hε']; have := min_le_right ε s; linarith only [this]
      obtain ⟨t, f', ht, htε, hdist, hnn', hle', hdiv'⟩ := ih ε' hε'pos
      by_cases hfree : f z y < cap z y
      · -- the arc `z → y` is unsaturated: push `t` along it
        have hsval : s = cap z y - f z y := by rw [hs, if_pos hfree]
        refine ⟨t, addArc f' z y t, ht, by linarith, ?_, ?_, ?_, ?_⟩
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = z ∧ q = y
          · rw [if_pos hpq]
            have h1 : |f' p q + t - f p q| ≤ |f' p q - f p q| + |t| := by
              have he : f' p q + t - f p q = (f' p q - f p q) + t := by ring
              rw [he]; exact abs_add_le _ _
            rw [abs_of_pos ht] at h1
            have := hdist p q
            linarith only [hε'ε, htε, h1, this]
          · rw [if_neg hpq, add_zero]
            have := hdist p q
            linarith only [hε'ε, ht, htε, this]
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = z ∧ q = y
          · rw [if_pos hpq]; linarith only [hnn' p q, ht.le]
          · rw [if_neg hpq, add_zero]; exact hnn' p q
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = z ∧ q = y
          · rw [if_pos hpq]
            obtain ⟨rfl, rfl⟩ := hpq
            have h2 : f' p q ≤ f p q + ε' := by
              have := (abs_le.mp (hdist p q)).2; linarith only [this]
            linarith only [hε's, htε, hsval, h2]
          · rw [if_neg hpq, add_zero]; exact hle' p q
        · intro u
          rw [netFlow_addArc, hdiv' u]
          split_ifs <;> ring
      · -- the arc `y → z` carries flow: cancel `t` of it
        have hback : 0 < f y z := by
          rcases hyz with h | h
          · exact absurd h hfree
          · exact h
        have hsval : s = f y z := by rw [hs, if_neg hfree]
        refine ⟨t, addArc f' y z (-t), ht, by linarith, ?_, ?_, ?_, ?_⟩
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = y ∧ q = z
          · rw [if_pos hpq]
            have h1 : |f' p q + -t - f p q| ≤ |f' p q - f p q| + |(-t)| := by
              have he : f' p q + -t - f p q = (f' p q - f p q) + (-t) := by ring
              rw [he]; exact abs_add_le _ _
            rw [abs_neg, abs_of_pos ht] at h1
            have := hdist p q
            linarith only [hε'ε, htε, h1, this]
          · rw [if_neg hpq, add_zero]
            have := hdist p q
            linarith only [hε'ε, ht, htε, this]
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = y ∧ q = z
          · rw [if_pos hpq]
            obtain ⟨rfl, rfl⟩ := hpq
            have h2 : f p q - ε' ≤ f' p q := by
              have := (abs_le.mp (hdist p q)).1; linarith only [this]
            linarith only [hε's, htε, hsval, h2]
          · rw [if_neg hpq, add_zero]; exact hnn' p q
        · intro p q
          rw [addArc_apply]
          by_cases hpq : p = y ∧ q = z
          · rw [if_pos hpq]; linarith only [hle' p q, ht.le]
          · rw [if_neg hpq, add_zero]; exact hle' p q
        · intro u
          rw [netFlow_addArc, hdiv' u]
          split_ifs <;> ring

/-! ### The theorem -/

/-- **Sufficiency of the cut condition** (Gale–Hoffman feasibility, the max-flow–min-cut theorem in
divergence form).  If the demands `b` are balanced and every cut has enough capacity, then a
feasible flow exists. -/
theorem exists_feasible_of_cut (cap : N → N → ℝ) (b : N → ℝ)
    (hcapnn : ∀ x y, 0 ≤ cap x y) (hsum : ∑ x, b x = 0)
    (hcut : ∀ S : Finset N, ∑ x ∈ S, b x ≤ ∑ x ∈ Sᶜ, ∑ y ∈ S, cap x y) :
    ∃ f, IsFeasible cap b f := by
  classical
  set K : Set (N → N → ℝ) := {f | ∀ x y, f x y ∈ Set.Icc (0:ℝ) (cap x y)} with hKdef
  have hKcomp : IsCompact K :=
    isCompact_pi_infinite (fun x => isCompact_pi_infinite (fun _ => isCompact_Icc))
  have hKne : (0 : N → N → ℝ) ∈ K := fun x y => ⟨le_rfl, hcapnn x y⟩
  have hnetcont : ∀ x : N, Continuous (fun f : N → N → ℝ => netFlow f x) := by
    intro x
    refine Continuous.sub ?_ ?_
    · exact continuous_finset_sum _ (fun y _ => (continuous_apply x).comp (continuous_apply y))
    · exact continuous_finset_sum _ (fun y _ => (continuous_apply y).comp (continuous_apply x))
  set Ψ : (N → N → ℝ) → ℝ := fun f => ∑ x, max (b x - netFlow f x) 0 with hΨdef
  have hcont : Continuous Ψ :=
    continuous_finset_sum _ (fun x _ => ((continuous_const.sub (hnetcont x)).max continuous_const))
  obtain ⟨f, hfK, hmin⟩ := hKcomp.exists_isMinOn ⟨0, hKne⟩ hcont.continuousOn
  have hnn : ∀ x y, 0 ≤ f x y := fun x y => (hfK x y).1
  have hle : ∀ x y, f x y ≤ cap x y := fun x y => (hfK x y).2
  refine ⟨f, hnn, hle, ?_⟩
  -- the key point: no node is starved
  have key : ∀ x, b x ≤ netFlow f x := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x₀, hx₀⟩ := hcon
    set R : Finset N := Finset.univ.filter (fun y => Relation.ReflTransGen (residual cap f) x₀ y)
      with hRdef
    have hmemR : ∀ y, y ∈ R ↔ Relation.ReflTransGen (residual cap f) x₀ y := by
      intro y; simp [hRdef]
    have hx₀R : x₀ ∈ R := (hmemR x₀).mpr Relation.ReflTransGen.refl
    -- no reachable node carries a surplus
    have hnosur : ∀ y ∈ R, netFlow f y ≤ b y := by
      intro y hy
      by_contra hsur
      push_neg at hsur
      have hreach := (hmemR y).mp hy
      have hxy : x₀ ≠ y := by
        intro h
        rw [h] at hx₀
        linarith only [hx₀, hsur]
      set ε : ℝ := min (b x₀ - netFlow f x₀) (netFlow f y - b y) with hεdef
      have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
      obtain ⟨t, f', ht, htε, -, hnn', hle', hdiv'⟩ := exists_augment hnn hle hreach ε hεpos
      have hf'K : f' ∈ K := fun p q => ⟨hnn' p q, hle' p q⟩
      have hterm : ∀ x, max (b x - netFlow f' x) 0
          = max (b x - netFlow f x) 0 + (if x = x₀ then -t else 0) := by
        intro x
        rcases eq_or_ne x x₀ with rfl | hxx₀
        · rw [if_pos rfl, hdiv' x, if_pos rfl, if_neg hxy]
          have h1 : b x - (netFlow f x + t - 0) = (b x - netFlow f x) - t := by ring
          rw [h1]
          have ht1 : t ≤ b x - netFlow f x := le_trans htε (min_le_left _ _)
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          ring
        · rw [if_neg hxx₀, add_zero, hdiv' x, if_neg hxx₀]
          rcases eq_or_ne x y with rfl | hxy'
          · rw [if_pos rfl]
            have ht2 : t ≤ netFlow f x - b x := le_trans htε (min_le_right _ _)
            rw [max_eq_right (by linarith), max_eq_right (by linarith)]
          · rw [if_neg hxy']
            norm_num
      have hΨ : Ψ f' = Ψ f - t := by
        have hcong : ∑ x, max (b x - netFlow f' x) 0
            = ∑ x, (max (b x - netFlow f x) 0 + (if x = x₀ then -t else 0)) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
        show ∑ x, max (b x - netFlow f' x) 0 = (∑ x, max (b x - netFlow f x) 0) - t
        rw [hcong, Finset.sum_add_distrib]
        simp
        ring
      have hle2 : Ψ f ≤ Ψ f' := hmin hf'K
      linarith only [ht, hΨ, hle2]
    -- the cut `R` is saturated
    have hsat : ∀ y ∈ R, ∀ z ∈ Rᶜ, f z y = cap z y ∧ f y z = 0 := by
      intro y hy z hz
      have hznot : ¬ Relation.ReflTransGen (residual cap f) x₀ z := by
        intro h
        exact absurd ((hmemR z).mpr h) (by simpa using hz)
      have hnres : ¬ residual cap f y z := by
        intro hres
        exact hznot (Relation.ReflTransGen.tail ((hmemR y).mp hy) hres)
      rw [residual, not_or, not_lt] at hnres
      exact ⟨le_antisymm (hle z y) hnres.1, le_antisymm (by linarith only [not_lt.mp hnres.2]) (hnn y z)⟩
    have hsum1 : ∑ y ∈ R, netFlow f y = ∑ x ∈ Rᶜ, ∑ y ∈ R, cap x y := by
      rw [sum_netFlow_eq f R]
      have h1 : ∑ x ∈ Rᶜ, ∑ y ∈ R, f x y = ∑ x ∈ Rᶜ, ∑ y ∈ R, cap x y :=
        Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => (hsat y hy x hx).1))
      have h2 : ∑ y ∈ R, ∑ x ∈ Rᶜ, f y x = 0 := by
        refine Finset.sum_eq_zero (fun y hy => Finset.sum_eq_zero (fun x hx => (hsat y hy x hx).2))
      rw [h1, h2, sub_zero]
    have hlt : ∑ y ∈ R, netFlow f y < ∑ y ∈ R, b y :=
      Finset.sum_lt_sum (fun i hi => hnosur i hi) ⟨x₀, hx₀R, hx₀⟩
    have := hcut R
    linarith [hsum1 ▸ hlt]
  -- and then the divergences agree with the demands
  intro x
  by_contra hne
  have hlt : b x < netFlow f x := lt_of_le_of_ne (key x) (Ne.symm hne)
  have : ∑ y, b y < ∑ y, netFlow f y :=
    Finset.sum_lt_sum (fun i _ => key i) ⟨x, Finset.mem_univ x, hlt⟩
  rw [hsum, sum_netFlow] at this
  exact lt_irrefl 0 this

end Nibble.Flow
