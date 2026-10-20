/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs

@[expose] public section

/-!
# Section B: short directed cycles have bounded multiplicity

In a digraph `Z` of maximum degree `≤ D`, every arc lies in at most `2 ^ (D (D+1)^K)` directed
simple cycles with at most `K` arcs (`card_cycles_through_le`). Hence the library of *all* short
directed cycles of `Z` has bounded edge multiplicity and at most `2 ^ (D (D+1)^K) |Z|` members
(`card_cycles_le`): no separate library producer is needed (`ARISTOTLE_CRUX_…`, section B).

The proof: a directed simple cycle through the arc `a` is strongly connected, so every one of
its arcs has its tail within `K` steps of `a.1`; the number of arcs of `Z` with tail in that
ball is at most `D (D+1)^K`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

variable {W : Type*} [DecidableEq W]

/-- Vertices reachable from `x` in at most `i` steps along arcs of `E`. -/
def reachBall (E : Finset (W × W)) (x : W) : ℕ → Finset W
  | 0 => {x}
  | i + 1 => reachBall E x i ∪ (E.filter (fun e => e.1 ∈ reachBall E x i)).image Prod.snd

lemma ball_mono_step (E : Finset (W × W)) (x : W) (i : ℕ) : reachBall E x i ⊆ reachBall E x (i + 1) :=
  Finset.subset_union_left

lemma ball_mono (E : Finset (W × W)) (x : W) {i j : ℕ} (h : i ≤ j) : reachBall E x i ⊆ reachBall E x j := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (ball_mono_step E x _)

lemma ball_mono_arcs {E F : Finset (W × W)} (hEF : E ⊆ F) (x : W) (i : ℕ) :
    reachBall E x i ⊆ reachBall F x i := by
  induction i with
  | zero => exact Finset.Subset.refl _
  | succ i ih =>
    simp only [reachBall]
    refine Finset.union_subset_union ih ?_
    refine Finset.image_subset_image ?_
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨hEF he.1, ih he.2⟩

lemma card_filter_tail_le {E : Finset (W × W)} {D : ℕ} (hD : MaxDegLE E D) (S : Finset W) :
    (E.filter (fun e => e.1 ∈ S)).card ≤ D * S.card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := E.filter (fun e => e.1 ∈ S)) (f := Prod.fst) (t := S)
    (fun e he => (mem_filter.1 he).2),
    mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun v _ => ?_
  calc ((E.filter (fun e => e.1 ∈ S)).filter (fun e => e.1 = v)).card
      ≤ (E.filter (fun e => e.1 = v)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    _ = outDeg E v := rfl
    _ ≤ D := le_trans (Nat.le_add_left _ _) (hD v)

lemma card_ball_le {E : Finset (W × W)} {D : ℕ} (hD : MaxDegLE E D) (x : W) (i : ℕ) :
    (reachBall E x i).card ≤ (D + 1) ^ i := by
  induction i with
  | zero => simp [reachBall]
  | succ i ih =>
    simp only [reachBall]
    calc (reachBall E x i ∪ (E.filter (fun e => e.1 ∈ reachBall E x i)).image Prod.snd).card
        ≤ (reachBall E x i).card + ((E.filter (fun e => e.1 ∈ reachBall E x i)).image Prod.snd).card :=
          Finset.card_union_le _ _
      _ ≤ (reachBall E x i).card + D * (reachBall E x i).card :=
          Nat.add_le_add_left (Finset.card_image_le.trans (card_filter_tail_le hD _)) _
      _ = (D + 1) * (reachBall E x i).card := by ring
      _ ≤ (D + 1) * (D + 1) ^ i := Nat.mul_le_mul_left _ ih
      _ = (D + 1) ^ (i + 1) := by ring

/-- The arcs of `E` whose tail is reachable from `x` within `i` steps. -/
def arcBall (E : Finset (W × W)) (x : W) (i : ℕ) : Finset (W × W) :=
  E.filter (fun e => e.1 ∈ reachBall E x i)

lemma card_arcBall_le {E : Finset (W × W)} {D : ℕ} (hD : MaxDegLE E D) (x : W) (i : ℕ) :
    (arcBall E x i).card ≤ D * (D + 1) ^ i :=
  (card_filter_tail_le hD _).trans (Nat.mul_le_mul_left _ (card_ball_le hD x i))

lemma ball_subset_heads (E : Finset (W × W)) (x : W) (i : ℕ) :
    reachBall E x i ⊆ insert x (E.image Prod.snd) := by
  induction i with
  | zero => simp [reachBall]
  | succ i ih =>
    simp only [reachBall]
    refine Finset.union_subset ih ?_
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.1 he).1)

lemma ball_stable_of_eq (E : Finset (W × W)) (x : W) {i : ℕ}
    (h : reachBall E x i = reachBall E x (i + 1)) : ∀ j, i ≤ j → reachBall E x j = reachBall E x i := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih =>
    rename_i m _
    simp only [reachBall]
    rw [ih]
    conv_rhs => rw [h]
    simp only [reachBall]

/-- The reachBall of radius `|E|` is closed under the arcs of `E`. -/
lemma ball_closed (E : Finset (W × W)) (x : W) {K : ℕ} (hK : E.card ≤ K) :
    reachBall E x (K + 1) = reachBall E x K := by
  by_contra hne
  have hstrict : ∀ i ≤ K, reachBall E x i ≠ reachBall E x (i + 1) := by
    intro i hi heq
    apply hne
    rw [ball_stable_of_eq E x heq (K + 1) (by omega), ball_stable_of_eq E x heq K hi]
  have hgrow : ∀ i ≤ K + 1, i + 1 ≤ (reachBall E x i).card := by
    intro i hi
    induction i with
    | zero => simp [reachBall]
    | succ i ih =>
      have h1 := ih (by omega)
      have hss : reachBall E x i ⊂ reachBall E x (i + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨ball_mono_step E x i, hstrict i (by omega)⟩
      have := Finset.card_lt_card hss
      omega
  have h1 := hgrow (K + 1) le_rfl
  have h2 := Finset.card_le_card (ball_subset_heads E x (K + 1))
  have h3 := Finset.card_insert_le x (E.image Prod.snd)
  have h4 : (E.image Prod.snd).card ≤ K := Finset.card_image_le.trans hK
  omega

lemma sum_inDeg_eq_card {E : Finset (W × W)} {S : Finset W} (h : ∀ e ∈ E, e.2 ∈ S) :
    ∑ v ∈ S, inDeg E v = E.card :=
  (Finset.card_eq_sum_card_fiberwise (f := Prod.snd) h).symm

lemma sum_outDeg_eq_card {E : Finset (W × W)} {S : Finset W} (h : ∀ e ∈ E, e.1 ∈ S) :
    ∑ v ∈ S, outDeg E v = E.card :=
  (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) h).symm

/-- **A directed simple cycle is strongly connected**: if `a ∈ p` then every arc of `p` has its
tail within `|p|` steps of `a.1` along arcs of `p`. -/
lemma IsDirCycle.tails_in_ball {p : Finset (W × W)} (hp : IsDirCycle p) {a : W × W}
    (ha : a ∈ p) {K : ℕ} (hK : p.card ≤ K) : ∀ e ∈ p, e.1 ∈ reachBall p a.1 K := by
  set S := reachBall p a.1 K with hS
  have hclosed : ∀ e ∈ p, e.1 ∈ S → e.2 ∈ S := by
    intro e he h1
    rw [hS, ← ball_closed p a.1 hK]
    simp only [reachBall]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨he, h1⟩, rfl⟩)
  set F := p.filter (fun e => e.1 ∈ S) with hF
  have hFp : F ⊆ p := Finset.filter_subset _ _
  have haS : a.1 ∈ S := ball_mono p a.1 (Nat.zero_le K) (by simp [reachBall])
  have hFne : F.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, haS⟩⟩
  have hFheads : ∀ e ∈ F, e.2 ∈ S := fun e he =>
    hclosed e (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he).2
  have hFtails : ∀ e ∈ F, e.1 ∈ S := fun e he => (Finset.mem_filter.1 he).2
  have hout : ∀ v ∈ S, outDeg F v = outDeg p v := by
    intro v hv
    unfold outDeg
    congr 1
    ext e
    simp only [hF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, h' ▸ hv⟩, h'⟩
  have hinle : ∀ v, inDeg F v ≤ inDeg p v := fun v =>
    Finset.card_le_card (Finset.filter_subset_filter _ hFp)
  have hsum : ∑ v ∈ S, inDeg F v = ∑ v ∈ S, inDeg p v := by
    have h1 : ∑ v ∈ S, inDeg F v = ∑ v ∈ S, outDeg F v := by
      rw [sum_inDeg_eq_card hFheads, sum_outDeg_eq_card hFtails]
    have h2 : ∑ v ∈ S, outDeg F v = ∑ v ∈ S, inDeg p v := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hout v hv, hp.2.1 v]
    rw [h1, h2]
  have hin : ∀ v ∈ S, inDeg F v = inDeg p v := by
    intro v hv
    by_contra hne
    have hlt : inDeg F v < inDeg p v := lt_of_le_of_ne (hinle v) hne
    have := Finset.sum_lt_sum (fun w _ => hinle w) ⟨v, hv, hlt⟩
    omega
  have hFbal : Balanced F := by
    intro v
    by_cases hv : v ∈ S
    · rw [hin v hv, hout v hv, hp.2.1 v]
    · have h1 : inDeg F v = 0 := by
        rw [inDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h; exact hv (h ▸ hFheads e he)
      have h2 : outDeg F v = 0 := by
        rw [outDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h; exact hv (h ▸ hFtails e he)
      rw [h1, h2]
  have hFeq : F = p := hp.2.2 F hFp hFne hFbal
  intro e he
  rw [← hFeq] at he
  exact (Finset.mem_filter.1 he).2

/-- Every short directed cycle of `Z` through `a` lies in the arc reachBall of `a`. -/
lemma IsDirCycle.subset_arcBall {Z p : Finset (W × W)} (hp : IsDirCycle p) (hpZ : p ⊆ Z)
    {a : W × W} (ha : a ∈ p) {K : ℕ} (hK : p.card ≤ K) : p ⊆ arcBall Z a.1 K := by
  intro e he
  exact Finset.mem_filter.2 ⟨hpZ he, ball_mono_arcs hpZ a.1 K (hp.tails_in_ball ha hK e he)⟩

/-- **Bounded multiplicity.** At most `2 ^ (D (D+1)^K)` short directed cycles of `Z` contain a
given arc. -/
theorem card_cycles_through_le {Z : Finset (W × W)} {D K : ℕ} (hD : MaxDegLE Z D)
    (𝒞 : Finset (Finset (W × W))) (h𝒞 : ∀ p ∈ 𝒞, IsDirCycle p ∧ p ⊆ Z ∧ p.card ≤ K)
    (a : W × W) : (𝒞.filter (fun p => a ∈ p)).card ≤ 2 ^ (D * (D + 1) ^ K) := by
  calc (𝒞.filter (fun p => a ∈ p)).card ≤ (arcBall Z a.1 K).powerset.card := by
        refine Finset.card_le_card ?_
        intro p hp
        obtain ⟨hp𝒞, hap⟩ := Finset.mem_filter.1 hp
        obtain ⟨hcyc, hpZ, hK⟩ := h𝒞 p hp𝒞
        exact Finset.mem_powerset.2 (hcyc.subset_arcBall hpZ hap hK)
    _ = 2 ^ (arcBall Z a.1 K).card := Finset.card_powerset _
    _ ≤ 2 ^ (D * (D + 1) ^ K) := Nat.pow_le_pow_right (by norm_num) (card_arcBall_le hD _ _)

/-- **Linear library size.** A family of short directed cycles of `Z` has at most
`2 ^ (D (D+1)^K) |Z|` members. -/
theorem card_cycles_le {Z : Finset (W × W)} {D K : ℕ} (hD : MaxDegLE Z D)
    (𝒞 : Finset (Finset (W × W))) (h𝒞 : ∀ p ∈ 𝒞, IsDirCycle p ∧ p ⊆ Z ∧ p.card ≤ K) :
    𝒞.card ≤ 2 ^ (D * (D + 1) ^ K) * Z.card := by
  classical
  calc 𝒞.card ≤ (Z.biUnion fun a => 𝒞.filter (fun p => a ∈ p)).card := by
        refine Finset.card_le_card ?_
        intro p hp
        obtain ⟨⟨a, ha⟩, -, -⟩ := (h𝒞 p hp).1
        exact Finset.mem_biUnion.2 ⟨a, (h𝒞 p hp).2.1 ha, Finset.mem_filter.2 ⟨hp, ha⟩⟩
    _ ≤ ∑ a ∈ Z, (𝒞.filter (fun p => a ∈ p)).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Z, 2 ^ (D * (D + 1) ^ K) :=
        Finset.sum_le_sum fun a _ => card_cycles_through_le hD 𝒞 h𝒞 a
    _ = 2 ^ (D * (D + 1) ^ K) * Z.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
