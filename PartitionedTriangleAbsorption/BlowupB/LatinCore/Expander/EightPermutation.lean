/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.PermutationExpander

/-!
# Eight permutations with unit directed cut capacity

For every `n` (including `0` and `1`) there are eight permutations `σ 0, …, σ 7` of `Fin n`
such that for every `S : Finset (Fin n)`
`min |S| |Sᶜ| ≤ ∑ j, |{u ∈ S | σ j u ∉ S}|`.

Finite counting proof (no probability library):

* `sum_choose_inCount_mul` : for a fixed `S` with `|S| = s`,
  `∑_σ C(I(σ),k) · C(n,k) = n! · C(s,k)²`, where `I(σ) = |{u ∈ S | σ u ∈ S}|`
  (factorial moments, via `permCount_mul`);
* `sum_pow_inCount_le` : `∑_σ λ^{I(σ)} ≤ n! (1 + p(λ-1))^s`, `p = s/n`, for `λ ≥ 1`;
* `badTuples_card_le` : with `λ = 4/p`, Markov gives
  `#{σ : Fin 8 → Perm | ∑ⱼ outCount < s} ≤ (n!)^8 (5-p)^{8s} (p/4)^{7s}`;
* the union over `C(n,s) ≤ (3/p)^s` sets of size `s` gives `(n!)^8 r(p)^s` with
  `r(p) = 3 (5-p)^8 p^6 / 4^7 ≤ 1/2` for `0 < p ≤ 1/2`, and `∑_{s ≥ 1} (1/2)^s < 1`;
* complements: `outCount σ Sᶜ = outCount σ S` for a permutation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.EightPerm

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of points of `S` that `σ` keeps inside `S`. -/
def inCount (σ : Equiv.Perm V) (S : Finset V) : ℕ := (S.filter (fun u => σ u ∈ S)).card

/-- Number of points of `S` that `σ` sends out of `S` (outgoing cut arcs of `σ`). -/
def outCount (σ : Equiv.Perm V) (S : Finset V) : ℕ := (S.filter (fun u => σ u ∉ S)).card

omit [Fintype V] in
theorem inCount_add_outCount (σ : Equiv.Perm V) (S : Finset V) :
    inCount σ S + outCount σ S = S.card :=
  card_filter_add_card_filter_not _

omit [Fintype V] in
theorem inCount_le (σ : Equiv.Perm V) (S : Finset V) : inCount σ S ≤ S.card :=
  card_filter_le _ _

/-- A permutation has as many arcs leaving `S` as arcs leaving `Sᶜ`. -/
theorem outCount_compl (σ : Equiv.Perm V) (S : Finset V) :
    outCount σ Sᶜ = outCount σ S := by
  have hpre : (univ.filter (fun u => σ u ∈ S)).card = S.card := by
    have : univ.filter (fun u => σ u ∈ S) = S.map σ.symm.toEmbedding := by
      ext u; simp
    rw [this, card_map]
  have h1 := card_filter_add_card_filter_not (s := univ.filter (fun u => σ u ∈ S))
    (fun u => u ∈ S)
  have e1 : (univ.filter (fun u => σ u ∈ S)).filter (fun u => u ∈ S) = S.filter (fun u => σ u ∈ S) := by
    ext u; simp [and_comm]
  have e2 : (univ.filter (fun u => σ u ∈ S)).filter (fun u => u ∉ S) = Sᶜ.filter (fun u => σ u ∉ Sᶜ) := by
    ext u; simp [and_comm]
  rw [e1, e2, hpre] at h1
  have h2 := inCount_add_outCount σ S
  unfold inCount outCount at h2
  unfold outCount
  omega


theorem powersetCard_filter_eq (k : ℕ) (S : Finset V) (P : V → Prop) [DecidablePred P] :
    powersetCard k (S.filter P) = (powersetCard k S).filter (fun K => ∀ u ∈ K, P u) := by
  ext K
  simp only [mem_powersetCard, mem_filter, subset_iff]
  constructor
  · rintro ⟨h, hk⟩; exact ⟨⟨fun x hx => (h hx).1, hk⟩, fun x hx => (h hx).2⟩
  · rintro ⟨⟨h, hk⟩, hP⟩; exact ⟨fun x hx => ⟨h hx, hP x hx⟩, hk⟩

/-- Factorial moments of `inCount`. -/
theorem sum_choose_inCount_mul (S : Finset V) (k : ℕ) :
    (∑ σ : Equiv.Perm V, (inCount σ S).choose k) * (Fintype.card V).choose k
      = (Fintype.card V).factorial * (S.card.choose k) ^ 2 := by
  have h1 : ∀ σ : Equiv.Perm V, (inCount σ S).choose k =
      ∑ K ∈ powersetCard k S, if K.map σ.toEmbedding ⊆ S then 1 else 0 := by
    intro σ
    rw [inCount, ← card_powersetCard, powersetCard_filter_eq, card_filter]
    refine sum_congr rfl fun K _ => ?_
    congr 1
    apply propext
    simp only [subset_iff, mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro h _ ⟨u, hu, rfl⟩; exact h u hu
    · intro h u hu; exact h ⟨u, hu, rfl⟩
  simp_rw [h1]
  rw [sum_comm]
  have h2 : ∀ K ∈ powersetCard k S,
      (∑ σ : Equiv.Perm V, if K.map σ.toEmbedding ⊆ S then 1 else 0) = permCount K S := by
    intro K _
    rw [permCount, card_filter]
  rw [sum_congr rfl h2, sum_mul]
  calc ∑ K ∈ powersetCard k S, permCount K S * (Fintype.card V).choose k
      = ∑ K ∈ powersetCard k S, (Fintype.card V).factorial * S.card.choose k :=
        sum_congr rfl (fun K hK => by
          have := permCount_mul K S
          rw [(mem_powersetCard.1 hK).2] at this; exact this)
    _ = _ := by rw [sum_const, card_powersetCard, smul_eq_mul]; ring

theorem sum_choose_inCount_le (S : Finset V) (k : ℕ) (hn : 0 < Fintype.card V) :
    (∑ σ : Equiv.Perm V, ((inCount σ S).choose k : ℝ))
      ≤ (Fintype.card V).factorial * S.card.choose k
          * ((S.card : ℝ) / Fintype.card V) ^ k := by
  rcases le_or_gt k S.card with hk | hk
  · have hsn : S.card ≤ Fintype.card V := card_le_univ S
    have hpos : (0:ℝ) < (Fintype.card V).choose k := by
      exact_mod_cast Nat.choose_pos (hk.trans hsn)
    have hnpos : (0:ℝ) < (Fintype.card V : ℝ) ^ k := by positivity
    have hm : (∑ σ : Equiv.Perm V, ((inCount σ S).choose k : ℝ)) * (Fintype.card V).choose k
        = (Fintype.card V).factorial * (S.card.choose k : ℝ) ^ 2 := by
      exact_mod_cast sum_choose_inCount_mul S k
    have hc : (S.card.choose k : ℝ) * (Fintype.card V : ℝ) ^ k
        ≤ (Fintype.card V).choose k * (S.card : ℝ) ^ k := by
      exact_mod_cast choose_mul_pow_le _ _ hsn k
    have hf : (0:ℝ) ≤ (Fintype.card V).factorial * (S.card.choose k : ℝ) := by positivity
    rw [div_pow]
    rw [← mul_le_mul_iff_of_pos_right (mul_pos hpos hnpos)]
    have e : (Fintype.card V).factorial * (S.card.choose k : ℝ)
        * ((S.card : ℝ) ^ k / (Fintype.card V : ℝ) ^ k)
        * ((Fintype.card V).choose k * (Fintype.card V : ℝ) ^ k)
        = (Fintype.card V).factorial * (S.card.choose k : ℝ)
          * ((Fintype.card V).choose k * (S.card : ℝ) ^ k) := by
      field_simp
    rw [e, ← mul_assoc, hm]
    calc (Fintype.card V).factorial * (S.card.choose k : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ k
        = (Fintype.card V).factorial * (S.card.choose k : ℝ)
          * ((S.card.choose k : ℝ) * (Fintype.card V : ℝ) ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hf
  · have h0 : ∀ σ : Equiv.Perm V, ((inCount σ S).choose k : ℝ) = 0 := fun σ => by
      rw [Nat.choose_eq_zero_of_lt (lt_of_le_of_lt (inCount_le σ S) hk)]; simp
    simp only [h0, sum_const_zero]
    positivity

theorem pow_eq_sum_choose (x : ℝ) (i s : ℕ) (his : i ≤ s) :
    x ^ i = ∑ k ∈ range (s + 1), (i.choose k : ℝ) * (x - 1) ^ k := by
  have : x = (x - 1) + 1 := by ring
  conv_lhs => rw [this, add_pow]
  simp only [one_pow, mul_one]
  rw [← sum_subset (range_subset_range.2 (by omega : i + 1 ≤ s + 1))]
  · exact sum_congr rfl fun k _ => by ring
  · intro k _ hk
    simp only [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Exponential moment of `inCount`. -/
theorem sum_pow_inCount_le (S : Finset V) (lam : ℝ) (hlam : 1 ≤ lam)
    (hn : 0 < Fintype.card V) :
    (∑ σ : Equiv.Perm V, lam ^ inCount σ S)
      ≤ (Fintype.card V).factorial
          * (1 + (S.card : ℝ) / Fintype.card V * (lam - 1)) ^ S.card := by
  set p : ℝ := (S.card : ℝ) / Fintype.card V
  have hp : 0 ≤ p := by positivity
  have hl : 0 ≤ lam - 1 := by linarith
  calc (∑ σ : Equiv.Perm V, lam ^ inCount σ S)
      = ∑ σ : Equiv.Perm V, ∑ k ∈ range (S.card + 1),
          ((inCount σ S).choose k : ℝ) * (lam - 1) ^ k :=
        sum_congr rfl fun σ _ => pow_eq_sum_choose lam _ _ (inCount_le σ S)
    _ = ∑ k ∈ range (S.card + 1),
          (∑ σ : Equiv.Perm V, ((inCount σ S).choose k : ℝ)) * (lam - 1) ^ k := by
        rw [sum_comm]; exact sum_congr rfl fun k _ => by rw [sum_mul]
    _ ≤ ∑ k ∈ range (S.card + 1),
          ((Fintype.card V).factorial * S.card.choose k * p ^ k) * (lam - 1) ^ k :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (sum_choose_inCount_le S k hn)
          (pow_nonneg hl k)
    _ = (Fintype.card V).factorial * (p * (lam - 1) + 1) ^ S.card := by
        rw [add_pow, mul_sum]
        exact sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_pow]; ring
    _ = _ := by rw [add_comm]


/-- Tuples of eight permutations that are bad for `S`. -/
def badTuples (S : Finset V) : Finset (Fin 8 → Equiv.Perm V) :=
  univ.filter (fun σ => ∑ j, outCount (σ j) S < S.card)

theorem badTuples_card_mul_le (S : Finset V) (lam : ℝ) (hlam : 1 ≤ lam)
    (hn : 0 < Fintype.card V) :
    ((badTuples S).card : ℝ) * lam ^ (7 * S.card)
      ≤ ((Fintype.card V).factorial : ℝ) ^ 8
          * (1 + (S.card : ℝ) / Fintype.card V * (lam - 1)) ^ (8 * S.card) := by
  have hl0 : 0 ≤ lam := by linarith
  have hbad : ∀ τ ∈ badTuples S, lam ^ (7 * S.card) ≤ ∏ j, lam ^ inCount (τ j) S := by
    intro τ hτ
    rw [prod_pow_eq_pow_sum]
    apply pow_le_pow_right₀ hlam
    have h1 : ∑ j, outCount (τ j) S < S.card := (mem_filter.1 hτ).2
    have h2 : ∑ j : Fin 8, (inCount (τ j) S + outCount (τ j) S) = 8 * S.card := by
      simp [inCount_add_outCount]
    rw [sum_add_distrib] at h2
    omega
  calc ((badTuples S).card : ℝ) * lam ^ (7 * S.card)
      = ∑ τ ∈ badTuples S, lam ^ (7 * S.card) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ τ ∈ badTuples S, ∏ j, lam ^ inCount (τ j) S := sum_le_sum hbad
    _ ≤ ∑ τ : Fin 8 → Equiv.Perm V, ∏ j, lam ^ inCount (τ j) S :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun _ _ _ => prod_nonneg fun _ _ => pow_nonneg hl0 _)
    _ = ∏ _j : Fin 8, ∑ σ : Equiv.Perm V, lam ^ inCount σ S := by
        rw [Fintype.prod_sum]
    _ = (∑ σ : Equiv.Perm V, lam ^ inCount σ S) ^ 8 := by simp
    _ ≤ ((Fintype.card V).factorial
          * (1 + (S.card : ℝ) / Fintype.card V * (lam - 1)) ^ S.card) ^ 8 :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ => pow_nonneg hl0 _)
          (sum_pow_inCount_le S lam hlam hn) 8
    _ = _ := by rw [mul_pow, ← pow_mul, mul_comm S.card 8]

theorem badTuples_card_le (S : Finset V) (hs : 1 ≤ S.card)
    (hsn : 2 * S.card ≤ Fintype.card V) :
    ((badTuples S).card : ℝ)
      ≤ ((Fintype.card V).factorial : ℝ) ^ 8
          * ((5 - (S.card : ℝ) / Fintype.card V) ^ 8
              * ((S.card : ℝ) / Fintype.card V / 4) ^ 7) ^ S.card := by
  have hs0 : (0:ℝ) < S.card := by exact_mod_cast hs
  have hn0 : (0:ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hsn' : (2:ℝ) * S.card ≤ Fintype.card V := by exact_mod_cast hsn
  set lam : ℝ := 4 * Fintype.card V / S.card with hlam
  have hlam1 : 1 ≤ lam := by
    rw [hlam, le_div_iff₀ hs0]; linarith
  have h := badTuples_card_mul_le S lam hlam1 (by omega)
  have e1 : 1 + (S.card : ℝ) / Fintype.card V * (lam - 1) = 5 - (S.card : ℝ) / Fintype.card V := by
    rw [hlam]; field_simp; ring
  rw [e1] at h
  have e2 : lam * ((S.card : ℝ) / Fintype.card V / 4) = 1 := by
    rw [hlam]; field_simp
  have hq : 0 ≤ ((S.card : ℝ) / Fintype.card V / 4) ^ (7 * S.card) := by positivity
  calc ((badTuples S).card : ℝ)
      = ((badTuples S).card : ℝ) * lam ^ (7 * S.card)
          * ((S.card : ℝ) / Fintype.card V / 4) ^ (7 * S.card) := by
        rw [mul_assoc, ← mul_pow, e2, one_pow, mul_one]
    _ ≤ ((Fintype.card V).factorial : ℝ) ^ 8 * (5 - (S.card : ℝ) / Fintype.card V) ^ (8 * S.card)
          * ((S.card : ℝ) / Fintype.card V / 4) ^ (7 * S.card) :=
        mul_le_mul_of_nonneg_right h hq
    _ = _ := by rw [mul_pow, pow_mul, pow_mul, mul_assoc, ← pow_mul, ← pow_mul, mul_comm 8, mul_comm 7]

end General

/-- The scalar estimate `3 (5-p)^8 p^6 / 4^7 ≤ 1/2` on `0 ≤ p ≤ 1/2`. -/
theorem ratio_le_half (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1 / 2) :
    3 * (5 - p) ^ 8 * p ^ 6 / 4 ^ 7 ≤ 1 / 2 := by
  have h : p ^ 3 * (5 - p) ^ 4 ≤ 52 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), pow_nonneg h0 2, pow_nonneg h0 3,
      mul_nonneg (pow_nonneg h0 2) (sub_nonneg.2 h1),
      mul_nonneg (pow_nonneg h0 3) (sub_nonneg.2 h1),
      mul_nonneg (pow_nonneg h0 4) (sub_nonneg.2 h1),
      mul_nonneg (pow_nonneg h0 5) (sub_nonneg.2 h1),
      mul_nonneg (pow_nonneg h0 6) (sub_nonneg.2 h1)]
  have h' : 0 ≤ p ^ 3 * (5 - p) ^ 4 := by
    have : 0 ≤ 5 - p := by linarith
    positivity
  have h2 : (5 - p) ^ 8 * p ^ 6 = (p ^ 3 * (5 - p) ^ 4) ^ 2 := by ring
  rw [mul_assoc, h2]
  nlinarith

/-- Sum over all `S` of size `s` (with `1 ≤ s`, `2 s ≤ n`) of the bad tuples. -/
theorem sum_badTuples_card_le (n s : ℕ) (hs : 1 ≤ s) (hsn : 2 * s ≤ n) :
    (∑ S ∈ powersetCard s (univ : Finset (Fin n)), ((badTuples S).card : ℝ))
      ≤ ((n.factorial : ℝ)) ^ 8 * (1 / 2) ^ s := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hn0 : (0:ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  set p : ℝ := (s : ℝ) / n with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ hn0]
    have : (2:ℝ) * s ≤ n := by exact_mod_cast hsn
    linarith
  have hterm : ∀ S ∈ powersetCard s (univ : Finset (Fin n)), ((badTuples S).card : ℝ)
      ≤ ((n.factorial : ℝ)) ^ 8 * ((5 - p) ^ 8 * (p / 4) ^ 7) ^ s := by
    intro S hS
    have hc := (mem_powersetCard.1 hS).2
    have h := badTuples_card_le S (by omega) (by simpa [hc] using hsn)
    simpa [hc, Fintype.card_fin] using h
  have hX : 0 ≤ (5 - p) ^ 8 * (p / 4) ^ 7 := by
    have : 0 ≤ 5 - p := by linarith
    positivity
  calc (∑ S ∈ powersetCard s (univ : Finset (Fin n)), ((badTuples S).card : ℝ))
      ≤ ∑ S ∈ powersetCard s (univ : Finset (Fin n)),
          ((n.factorial : ℝ)) ^ 8 * ((5 - p) ^ 8 * (p / 4) ^ 7) ^ s := sum_le_sum hterm
    _ = (n.choose s : ℝ) * (((n.factorial : ℝ)) ^ 8 * ((5 - p) ^ 8 * (p / 4) ^ 7) ^ s) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (3 * n / s) ^ s * (((n.factorial : ℝ)) ^ 8 * ((5 - p) ^ 8 * (p / 4) ^ 7) ^ s) :=
        mul_le_mul_of_nonneg_right (choose_le_three_mul_div_pow n s hs)
          (by positivity)
    _ = ((n.factorial : ℝ)) ^ 8 * (3 * (5 - p) ^ 8 * p ^ 6 / 4 ^ 7) ^ s := by
        rw [← mul_assoc, mul_comm _ ((n.factorial : ℝ) ^ 8), mul_assoc, ← mul_pow]
        congr 2
        rw [hp]; field_simp
    _ ≤ ((n.factorial : ℝ)) ^ 8 * (1 / 2) ^ s := by
        have h5 : 0 ≤ 5 - p := by linarith
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (ratio_le_half p hp0.le hp1) s) (by positivity)

/-- **Primary target.** Eight permutations of `Fin n` with unit directed cut capacity. -/
theorem exists_eight_perm_cut (n : ℕ) :
    ∃ σ : Fin 8 → Equiv.Perm (Fin n), ∀ S : Finset (Fin n),
      min S.card Sᶜ.card ≤ ∑ j : Fin 8, (S.filter (fun u => σ j u ∉ S)).card := by
  set m := n / 2
  let Bad : Finset (Fin 8 → Equiv.Perm (Fin n)) :=
    (range m).biUnion (fun t => (powersetCard (t + 1) univ).biUnion badTuples)
  have hcard : (Bad.card : ℝ) < ((n.factorial : ℝ)) ^ 8 := by
    have hf : (0:ℝ) < (n.factorial : ℝ) ^ 8 := by positivity
    calc (Bad.card : ℝ)
        ≤ ∑ t ∈ range m, (((powersetCard (t + 1) univ).biUnion badTuples).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ t ∈ range m, ∑ S ∈ powersetCard (t + 1) (univ : Finset (Fin n)),
            ((badTuples S).card : ℝ) :=
          sum_le_sum fun t _ => by exact_mod_cast card_biUnion_le
      _ ≤ ∑ t ∈ range m, ((n.factorial : ℝ)) ^ 8 * (1 / 2) ^ (t + 1) :=
          sum_le_sum fun t ht => sum_badTuples_card_le n (t + 1) (by omega)
            (by have := mem_range.1 ht; omega)
      _ = ((n.factorial : ℝ)) ^ 8 * (1 - (1 / 2) ^ m) := by
          rw [← mul_sum, sum_half_pow]
      _ < _ := by
          have : (0:ℝ) < (1 / 2) ^ m := by positivity
          nlinarith
  have hlt : Bad.card < (univ : Finset (Fin 8 → Equiv.Perm (Fin n))).card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast hcard
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card hlt
  have good : ∀ T : Finset (Fin n), 1 ≤ T.card → 2 * T.card ≤ n →
      T.card ≤ ∑ j, outCount (σ j) T := by
    intro T h1 h2
    by_contra hc
    apply hσ
    refine mem_biUnion.2 ⟨T.card - 1, mem_range.2 (by omega), mem_biUnion.2 ⟨T, ?_, ?_⟩⟩
    · exact mem_powersetCard.2 ⟨subset_univ _, by omega⟩
    · exact mem_filter.2 ⟨mem_univ _, by omega⟩
  refine ⟨σ, fun S => ?_⟩
  have hcomp : Sᶜ.card = n - S.card := by rw [card_compl, Fintype.card_fin]
  have hSn : S.card ≤ n := by simpa using card_le_univ S
  change min S.card Sᶜ.card ≤ ∑ j, outCount (σ j) S
  by_cases h2 : 2 * S.card ≤ n
  · rcases Nat.eq_zero_or_pos S.card with h0 | h0
    · simp [h0]
    · exact (min_le_left _ _).trans (good S h0 h2)
  · rcases Nat.eq_zero_or_pos Sᶜ.card with h0 | h0
    · simp [h0]
    · have := good Sᶜ h0 (by omega)
      simp only [outCount_compl] at this
      exact (min_le_right _ _).trans this

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.EightPerm

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.EightPerm.exists_eight_perm_cut
