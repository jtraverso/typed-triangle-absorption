/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Robust.RMBGEvents
public import PartitionedTriangleAbsorption.BlowupB.Robust.RMBGBounds

@[expose] public section

/-!
# Robustly matchable bipartite graphs exist (Montgomery), with explicit constant degree

`exists_robust`: for every `m ≥ 1` there is a configuration of `2 · 2000` permutations of
`Fin (m + m)` whose bipartite graph on `(X ⊔ Y, Z)` (`|X| = |Z| = 2m`, `|Y| = m`, all degrees
`≤ 4000`) is robustly matchable: for every `X' ⊆ X` with `|X'| = m`, `X' ⊔ Y` has an injection into `Z`
along edges (a perfect matching).

Proof: union bound over the three bad families (`Bad1`, `Bad3`, `Bad4`), whose total size is at most
`(2/100 + 2/100 + 1/2)` times the number of configurations (no probability theory: counting only).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

open Finset

variable {d m : ℕ}

def Bad1 (d m : ℕ) : Finset (Conf d m) :=
  (univ.filter fun A : Finset (Fin (m + m)) => 1 ≤ #A ∧ 10 * #A ≤ m).biUnion fun A =>
    (powersetCard (2 * #A - 1) (univ : Finset (Fin (m + m)))).biUnion fun W => E1 d m A W

def Bad3 (d m : ℕ) : Finset (Conf d m) :=
  (univ.filter fun C : Finset (Fin (m + m)) => 1 ≤ #C ∧ 10 * #C ≤ m).biUnion fun C =>
    (powersetCard (#C - 1) (univ : Finset (Fin m))).biUnion fun U => E3 d m C (dup U)

def Bad4 (d m : ℕ) : Finset (Conf d m) :=
  (univ : Finset (Finset (Fin (m + m)))).biUnion fun A1 =>
    (univ : Finset (Finset (Fin m))).biUnion fun A2 =>
      (univ.filter fun C : Finset (Fin (m + m)) => m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C).biUnion
        fun C => E4 d m A1 A2 C

theorem good_of_not_bad (c : Conf d m) (h1 : c ∉ Bad1 d m) (h3 : c ∉ Bad3 d m)
    (h4 : c ∉ Bad4 d m) : Good c := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    obtain ⟨A, W, hA1, hA10, hW, hc⟩ := mem_bad1_of_not_P1 c h
    exact h1 (mem_biUnion.mpr ⟨A, mem_filter.mpr ⟨mem_univ _, hA1, hA10⟩,
      mem_biUnion.mpr ⟨W, mem_powersetCard.mpr ⟨subset_univ _, hW⟩, hc⟩⟩)
  · by_contra h
    obtain ⟨C, U, hC1, hC10, hU, hc⟩ := mem_bad3_of_not_P3 c h
    exact h3 (mem_biUnion.mpr ⟨C, mem_filter.mpr ⟨mem_univ _, hC1, hC10⟩,
      mem_biUnion.mpr ⟨U, mem_powersetCard.mpr ⟨subset_univ _, hU⟩, hc⟩⟩)
  · by_contra h
    obtain ⟨A1, A2, C, hA, hC, hc⟩ := mem_bad4_of_not_P4 c h
    exact h4 (mem_biUnion.mpr ⟨A1, mem_univ _, mem_biUnion.mpr ⟨A2, mem_univ _,
      mem_biUnion.mpr ⟨C, mem_filter.mpr ⟨mem_univ _, hA, hC⟩, hc⟩⟩⟩)

/-! ### Real bounds on the bad events -/

/-- The number of configurations, as a real. -/
noncomputable def TT (d m : ℕ) : ℝ := (((m + m).factorial ^ d) ^ 2 : ℕ)

theorem TT_pos : 0 < TT d m := by unfold TT; positivity

theorem real_of_nat_bound {E w k n T : ℕ} (hn : 0 < n) (h : E * n ^ k ≤ w ^ k * T) :
    (E : ℝ) ≤ ((w : ℝ) / n) ^ k * T := by
  have hnk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  have h' : (E : ℝ) * (n : ℝ) ^ k ≤ (w : ℝ) ^ k * T := by exact_mod_cast h
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hnk]
  linarith

theorem E1_real (hm : 1 ≤ m) (A W : Finset (Fin (m + m))) :
    (#(E1 d m A W) : ℝ) ≤ ((#W : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A * d) * TT d m := by
  unfold TT
  exact real_of_nat_bound (by omega) (card_E1_le A W)

theorem E3_real (hm : 1 ≤ m) (C W : Finset (Fin (m + m))) :
    (#(E3 d m C W) : ℝ) ≤ ((#W : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#C * d) * TT d m := by
  unfold TT
  exact real_of_nat_bound (by omega) (card_E3_le C W)

/-- Grouping a sum over subsets by cardinality. -/
theorem sum_filter_card_eq {α : Type*} [Fintype α] [DecidableEq α] (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → ℝ) :
    ∑ A ∈ (univ : Finset (Finset α)).filter (fun A => P #A), g #A =
      ∑ a ∈ range (Fintype.card α + 1), ((Fintype.card α).choose a : ℝ) * (if P a then g a else 0) := by
  rw [sum_filter, ← powerset_univ]
  have h := sum_powerset_apply_card (fun k => if P k then g k else 0) (x := (univ : Finset α))
  beta_reduce at h
  rw [h, card_univ]
  exact sum_congr rfl fun a _ => nsmul_eq_mul _ _

theorem card_bad1_le (hd : 2000 ≤ d) (hm : 1 ≤ m) : (#(Bad1 d m) : ℝ) ≤ 2 / 100 * TT d m := by
  classical
  have hstep : (#(Bad1 d m) : ℝ) ≤ ∑ A ∈ (univ : Finset (Finset (Fin (m + m)))).filter
      (fun A => 1 ≤ #A ∧ 10 * #A ≤ m),
      (((m + m).choose (2 * #A - 1) : ℝ) * (((2 * #A - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A * d) * TT d m) := by
    calc (#(Bad1 d m) : ℝ) ≤ ∑ A ∈ (univ : Finset (Finset (Fin (m + m)))).filter
          (fun A => 1 ≤ #A ∧ 10 * #A ≤ m),
          ((#((powersetCard (2 * #A - 1) (univ : Finset (Fin (m + m)))).biUnion
            fun W => E1 d m A W) : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ _ := by
          refine sum_le_sum fun A _ => ?_
          calc ((#((powersetCard (2 * #A - 1) (univ : Finset (Fin (m + m)))).biUnion
                fun W => E1 d m A W) : ℕ) : ℝ)
              ≤ ∑ W ∈ powersetCard (2 * #A - 1) (univ : Finset (Fin (m + m))), (#(E1 d m A W) : ℝ) := by
                exact_mod_cast card_biUnion_le
            _ ≤ ∑ W ∈ powersetCard (2 * #A - 1) (univ : Finset (Fin (m + m))),
                ((((2 * #A - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A * d) * TT d m) := by
                refine sum_le_sum fun W hW => ?_
                have hWc := (mem_powersetCard.mp hW).2
                have := E1_real (d := d) hm A W
                rw [hWc] at this
                exact this
            _ = _ := by
                rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hgroup := sum_filter_card_eq (α := Fin (m + m)) (fun a => 1 ≤ a ∧ 10 * a ≤ m)
    (fun a => ((m + m).choose (2 * a - 1) : ℝ) * (((2 * a - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (a * d) * TT d m)
  rw [hgroup, Fintype.card_fin] at hstep
  have hterm : ∀ a ∈ range ((m + m) + 1), ((m + m).choose a : ℝ) * (if 1 ≤ a ∧ 10 * a ≤ m then
      ((m + m).choose (2 * a - 1) : ℝ) * (((2 * a - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (a * d) * TT d m else 0) ≤
      (if 1 ≤ a then (1 / 100 : ℝ) ^ a else 0) * TT d m := by
    intro a _
    split_ifs with h h'
    · have := term1_le m a d h.1 h.2 (by omega)
      have hT := (TT_pos (d := d) (m := m)).le
      calc ((m + m).choose a : ℝ) * (((m + m).choose (2 * a - 1) : ℝ) *
            (((2 * a - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (a * d) * TT d m)
          = (((m + m).choose a : ℝ) * ((m + m).choose (2 * a - 1) : ℝ) *
            (((2 * a - 1 : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (a * d)) * TT d m := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hT
    · exact absurd h.1 h'
    · rw [mul_zero]; exact mul_nonneg (pow_nonneg (by norm_num) _) (TT_pos (d := d) (m := m)).le
    · simp
  have hsum : ∑ a ∈ range ((m + m) + 1), (if 1 ≤ a then (1 / 100 : ℝ) ^ a else 0) * TT d m ≤
      2 / 100 * TT d m := by
    rw [← sum_mul, sum_range_succ']
    simp only [Nat.le_add_left, ite_true, show ¬ (1 ≤ 0) from by norm_num, ite_false, add_zero]
    have := geom_sum_le_two_mul (1 / 100) (by norm_num) (by norm_num) (m + m)
    have hT := (TT_pos (d := d) (m := m)).le
    have : (∑ a ∈ range (m + m), (1 / 100 : ℝ) ^ (a + 1)) * TT d m ≤ 2 * (1 / 100) * TT d m :=
      mul_le_mul_of_nonneg_right this hT
    linarith
  exact hstep.trans ((sum_le_sum hterm).trans hsum)

theorem card_bad3_le (hd : 2000 ≤ d) (hm : 1 ≤ m) : (#(Bad3 d m) : ℝ) ≤ 2 / 100 * TT d m := by
  classical
  have hstep : (#(Bad3 d m) : ℝ) ≤ ∑ C ∈ (univ : Finset (Finset (Fin (m + m)))).filter
      (fun C => 1 ≤ #C ∧ 10 * #C ≤ m),
      ((m.choose (#C - 1) : ℝ) * (((2 * (#C - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#C * d) * TT d m) := by
    calc (#(Bad3 d m) : ℝ) ≤ ∑ C ∈ (univ : Finset (Finset (Fin (m + m)))).filter
          (fun C => 1 ≤ #C ∧ 10 * #C ≤ m),
          ((#((powersetCard (#C - 1) (univ : Finset (Fin m))).biUnion
            fun U => E3 d m C (dup U)) : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ _ := by
          refine sum_le_sum fun C _ => ?_
          calc ((#((powersetCard (#C - 1) (univ : Finset (Fin m))).biUnion
                fun U => E3 d m C (dup U)) : ℕ) : ℝ)
              ≤ ∑ U ∈ powersetCard (#C - 1) (univ : Finset (Fin m)), (#(E3 d m C (dup U)) : ℝ) := by
                exact_mod_cast card_biUnion_le
            _ ≤ ∑ U ∈ powersetCard (#C - 1) (univ : Finset (Fin m)),
                ((((2 * (#C - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#C * d) * TT d m) := by
                refine sum_le_sum fun U hU => ?_
                have hUc := (mem_powersetCard.mp hU).2
                have := E3_real (d := d) hm C (dup U)
                rw [card_dup, hUc] at this
                exact this
            _ = _ := by
                rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hgroup := sum_filter_card_eq (α := Fin (m + m)) (fun c => 1 ≤ c ∧ 10 * c ≤ m)
    (fun c => (m.choose (c - 1) : ℝ) * (((2 * (c - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (c * d) * TT d m)
  rw [hgroup, Fintype.card_fin] at hstep
  have hterm : ∀ c ∈ range ((m + m) + 1), ((m + m).choose c : ℝ) * (if 1 ≤ c ∧ 10 * c ≤ m then
      (m.choose (c - 1) : ℝ) * (((2 * (c - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (c * d) * TT d m else 0) ≤
      (if 1 ≤ c then (1 / 100 : ℝ) ^ c else 0) * TT d m := by
    intro c _
    split_ifs with h h'
    · have := term3_le m c d h.1 h.2 (by omega)
      have hT := (TT_pos (d := d) (m := m)).le
      calc ((m + m).choose c : ℝ) * ((m.choose (c - 1) : ℝ) *
            (((2 * (c - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (c * d) * TT d m)
          = (((m + m).choose c : ℝ) * (m.choose (c - 1) : ℝ) *
            (((2 * (c - 1) : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (c * d)) * TT d m := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hT
    · exact absurd h.1 h'
    · rw [mul_zero]; exact mul_nonneg (pow_nonneg (by norm_num) _) (TT_pos (d := d) (m := m)).le
    · simp
  have hsum : ∑ c ∈ range ((m + m) + 1), (if 1 ≤ c then (1 / 100 : ℝ) ^ c else 0) * TT d m ≤
      2 / 100 * TT d m := by
    rw [← sum_mul, sum_range_succ']
    simp only [Nat.le_add_left, ite_true, show ¬ (1 ≤ 0) from by norm_num, ite_false, add_zero]
    have := geom_sum_le_two_mul (1 / 100) (by norm_num) (by norm_num) (m + m)
    have hT := (TT_pos (d := d) (m := m)).le
    have : (∑ c ∈ range (m + m), (1 / 100 : ℝ) ^ (c + 1)) * TT d m ≤ 2 * (1 / 100) * TT d m :=
      mul_le_mul_of_nonneg_right this hT
    linarith
  exact hstep.trans ((sum_le_sum hterm).trans hsum)

theorem E4_real (hd : 2000 ≤ d) (hm : 1 ≤ m) (A1 : Finset (Fin (m + m))) (A2 : Finset (Fin m))
    (C : Finset (Fin (m + m))) (hA : m ≤ 10 * (#A1 + #A2)) (hC : m ≤ 10 * #C) :
    (#(E4 d m A1 A2 C) : ℝ) ≤ ((19 / 20 : ℝ) ^ 200) ^ m * TT d m := by
  have hn : 0 < (m + m) := by omega
  have hnR : (0 : ℝ) < ((m + m : ℕ) : ℝ) := by exact_mod_cast hn
  have hCn : #C ≤ (m + m) := by simpa using card_le_univ C
  have h := card_E4_le (d := d) A1 A2 C
  rw [card_dup] at h
  have hpow : (0 : ℝ) < ((m + m : ℕ) : ℝ) ^ (#A1 * d) * ((m + m : ℕ) : ℝ) ^ (2 * #A2 * d) := by positivity
  have h' : (#(E4 d m A1 A2 C) : ℝ) * (((m + m : ℕ) : ℝ) ^ (#A1 * d) * ((m + m : ℕ) : ℝ) ^ (2 * #A2 * d)) ≤
      ((((m + m) - #C : ℕ) : ℝ) ^ (#A1 * d) * (((m + m) - #C : ℕ) : ℝ) ^ (2 * #A2 * d)) * TT d m := by
    unfold TT; exact_mod_cast h
  have hq : (((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ) ≤ 19 / 20 := by
    rw [Nat.cast_sub hCn, div_le_iff₀ hnR]
    have : (m : ℝ) ≤ 10 * (#C : ℝ) := by exact_mod_cast hC
    have hn' : ((m + m : ℕ) : ℝ) = m + m := by push_cast; ring
    rw [hn']; linarith
  have hq0 : (0 : ℝ) ≤ (((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ) := by positivity
  have hE : (#(E4 d m A1 A2 C) : ℝ) ≤
      (((((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A1 * d) * ((((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (2 * #A2 * d)) * TT d m := by
    rw [div_pow, div_pow, div_mul_div_comm, div_mul_eq_mul_div, le_div_iff₀ hpow]
    linarith
  have hd1 : #A1 * 2000 ≤ #A1 * d := Nat.mul_le_mul_left _ hd
  have hd2 : 2 * #A2 * 2000 ≤ 2 * #A2 * d := Nat.mul_le_mul_left _ hd
  have hexp : 200 * m ≤ #A1 * d + 2 * #A2 * d := by omega
  have hbase : (((((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A1 * d) * ((((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (2 * #A2 * d))
      ≤ ((19 / 20 : ℝ) ^ 200) ^ m := by
    rw [← pow_add, ← pow_mul]
    calc ((((m + m) - #C : ℕ) : ℝ) / ((m + m : ℕ) : ℝ)) ^ (#A1 * d + 2 * #A2 * d)
        ≤ (19 / 20 : ℝ) ^ (#A1 * d + 2 * #A2 * d) := pow_le_pow_left₀ hq0 hq _
      _ ≤ (19 / 20 : ℝ) ^ (200 * m) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  exact hE.trans (mul_le_mul_of_nonneg_right hbase (TT_pos (d := d) (m := m)).le)

theorem card_bad4_le (hd : 2000 ≤ d) (hm : 1 ≤ m) : (#(Bad4 d m) : ℝ) ≤ 1 / 2 * TT d m := by
  classical
  have hT := (TT_pos (d := d) (m := m)).le
  have hstep : (#(Bad4 d m) : ℝ) ≤ ∑ _A1 : Finset (Fin (m + m)), ∑ _A2 : Finset (Fin m),
      ∑ _C : Finset (Fin (m + m)), ((19 / 20 : ℝ) ^ 200) ^ m * TT d m := by
    calc (#(Bad4 d m) : ℝ) ≤ ∑ A1 : Finset (Fin (m + m)), ((#((univ : Finset (Finset (Fin m))).biUnion fun A2 =>
          (univ.filter fun C : Finset (Fin (m + m)) => m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C).biUnion
            fun C => E4 d m A1 A2 C) : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ _ := by
          refine sum_le_sum fun A1 _ => ?_
          calc ((#((univ : Finset (Finset (Fin m))).biUnion fun A2 =>
                (univ.filter fun C : Finset (Fin (m + m)) => m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C).biUnion
                  fun C => E4 d m A1 A2 C) : ℕ) : ℝ)
              ≤ ∑ A2 : Finset (Fin m), ((#((univ.filter fun C : Finset (Fin (m + m)) =>
                  m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C).biUnion fun C => E4 d m A1 A2 C) : ℕ) : ℝ) := by
                exact_mod_cast card_biUnion_le
            _ ≤ _ := by
                refine sum_le_sum fun A2 _ => ?_
                calc ((#((univ.filter fun C : Finset (Fin (m + m)) =>
                      m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C).biUnion fun C => E4 d m A1 A2 C) : ℕ) : ℝ)
                    ≤ ∑ C ∈ univ.filter (fun C : Finset (Fin (m + m)) => m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C),
                        (#(E4 d m A1 A2 C) : ℝ) := by
                      exact_mod_cast card_biUnion_le
                  _ ≤ ∑ C ∈ univ.filter (fun C : Finset (Fin (m + m)) => m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C),
                        ((19 / 20 : ℝ) ^ 200) ^ m * TT d m := by
                      refine sum_le_sum fun C hC => ?_
                      obtain ⟨-, hA, hCc⟩ := mem_filter.mp hC
                      exact E4_real hd hm A1 A2 C hA hCc
                  _ ≤ ∑ _C : Finset (Fin (m + m)), ((19 / 20 : ℝ) ^ 200) ^ m * TT d m :=
                      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                        (fun _ _ _ => mul_nonneg (by positivity) hT)
  have hcount : (∑ _A1 : Finset (Fin (m + m)), ∑ _A2 : Finset (Fin m),
      ∑ _C : Finset (Fin (m + m)), ((19 / 20 : ℝ) ^ 200) ^ m * TT d m) =
      ((32 : ℝ) * (19 / 20) ^ 200) ^ m * TT d m := by
    simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_pow]
    have h32 : (32 : ℝ) ^ m = 2 ^ (m + m) * 2 ^ m * 2 ^ (m + m) := by
      rw [← pow_add, ← pow_add, show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_mul]; congr 1; ring
    rw [h32]; ring
  have hgeo : ((32 : ℝ) * (19 / 20) ^ 200) ^ m ≤ 1 / 2 := by
    calc ((32 : ℝ) * (19 / 20) ^ 200) ^ m ≤ (1 / 2 : ℝ) ^ m :=
          pow_le_pow_left₀ (by positivity) ratio_pow_le m
      _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1 / 2 := by norm_num
  rw [hcount] at hstep
  exact hstep.trans (mul_le_mul_of_nonneg_right hgeo hT)

/-- **Good configurations exist** (for every `m ≥ 1`, with `d = 2000`). -/
theorem exists_good (hd : 2000 ≤ d) (hm : 1 ≤ m) : ∃ c : Conf d m, Good c := by
  classical
  by_contra hno
  push Not at hno
  have hcover : (univ : Finset (Conf d m)) ⊆ Bad1 d m ∪ Bad3 d m ∪ Bad4 d m := by
    intro c _
    by_contra hc
    simp only [mem_union, not_or] at hc
    exact hno c (good_of_not_bad c hc.1.1 hc.1.2 hc.2)
  have hcard := card_le_card hcover
  have hU : (#(univ : Finset (Conf d m)) : ℝ) = TT d m := by
    rw [card_univ, card_conf]; rfl
  have h1 := card_bad1_le hd hm
  have h3 := card_bad3_le hd hm
  have h4 := card_bad4_le hd hm
  have hu : (#(Bad1 d m ∪ Bad3 d m ∪ Bad4 d m) : ℝ) ≤ #(Bad1 d m) + #(Bad3 d m) + #(Bad4 d m) := by
    have := (card_union_le (Bad1 d m ∪ Bad3 d m) (Bad4 d m)).trans
      (Nat.add_le_add_right (card_union_le (Bad1 d m) (Bad3 d m)) _)
    exact_mod_cast this
  have hc' : (#(univ : Finset (Conf d m)) : ℝ) ≤ #(Bad1 d m ∪ Bad3 d m ∪ Bad4 d m) := by
    exact_mod_cast hcard
  have hT := TT_pos (d := d) (m := m)
  rw [hU] at hc'
  linarith

/-- **Montgomery's robustly matchable bipartite graph**, degree `≤ 4000`. -/
theorem exists_robust (hm : 1 ≤ m) : ∃ c : Conf 2000 m, Robust c := by
  obtain ⟨c, hc⟩ := exists_good (d := 2000) le_rfl hm
  exact ⟨c, robust_of_good c (by norm_num) hc⟩

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.exists_robust
