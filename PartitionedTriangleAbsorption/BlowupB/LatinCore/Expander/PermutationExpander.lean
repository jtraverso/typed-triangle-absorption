/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.BinomialEstimates

/-!
# Existence of bounded-degree edge expanders (finite counting proof)

For every `n` there are four permutations `σ₀,…,σ₃` of `Fin n` such that the **simple** graph
`permGraph σ` (with `x ~ y` iff `x ≠ y` and `σⱼ x = y` or `σⱼ y = x` for some `j`) has

* maximum degree `≤ 8`, and
* `min (|S|, |Sᶜ|) ≤ 20 · |∂S|` for **every** vertex subset `S`,

where `∂S = edgeBoundary H S` is the finset of edges of `H` with exactly one end in `S`.

Loops and parallel edges are handled explicitly: a fixed point `σⱼ x = x` produces no edge
(`x ≠ y` is part of the adjacency relation), and parallel edges coming from different `j` or
from `σⱼ x = y`, `σⱼ y = x` simultaneously collapse to a single `Sym2` edge.  The expansion
bound is proved directly for this simple graph: for a fixed `j`, the map
`x ↦ s(x, σⱼ x)` from `{x ∈ S | σⱼ x ∉ S}` into `∂S` is injective.

The proof is a finite union bound (no probability library):

* `permCount_mul` : exactly `n! · C(|W|,s) / C(n,s)` permutations map a fixed `s`-set into `W`
  (double counting plus transitivity of `Perm` on `s`-sets);
* `badPerms_card_mul` : few permutations move at most `r` points of `S` out of `S`;
* `BinomialEstimates.union_term_le` : summing over all `S` with `1 ≤ |S| ≤ n/2` and
  `r = (|S|-1)/20` gives total weight `< (n!)^4`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander

open Finset

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Perm V` acts transitively on subsets of a fixed size. -/
theorem exists_perm_map_eq (S S' : Finset V) (h : S.card = S'.card) :
    ∃ τ : Equiv.Perm V, S.map τ.toEmbedding = S' := by
  have e1 : {x // x ∈ S} ≃ {x // x ∈ S'} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // ¬ x ∈ S} ≃ {x // ¬ x ∈ S'} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  have hap : ∀ x (hx : x ∈ S), Equiv.subtypeCongr e1 e2 x = e1 ⟨x, hx⟩ := by
    intro x hx; simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  ext y
  simp only [mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hap x hx]; exact (e1 ⟨x, hx⟩).2
  · intro hy
    refine ⟨(e1.symm ⟨y, hy⟩ : V), (e1.symm ⟨y, hy⟩).2, ?_⟩
    rw [hap _ (e1.symm ⟨y, hy⟩).2]; simp

/-- Number of permutations mapping `S` into `W`. -/
def permCount (S W : Finset V) : ℕ :=
  (univ.filter (fun σ : Equiv.Perm V => S.map σ.toEmbedding ⊆ W)).card

omit [Fintype V] [DecidableEq V] in
theorem map_perm_mul (σ τ : Equiv.Perm V) (S : Finset V) :
    S.map (σ * τ).toEmbedding = (S.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]; rfl

theorem permCount_congr (S S' W : Finset V) (h : S.card = S'.card) :
    permCount S W = permCount S' W := by
  obtain ⟨τ, hτ⟩ := exists_perm_map_eq S' S h.symm
  unfold permCount
  refine Finset.card_bij (fun σ _ => σ * τ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rwa [map_perm_mul, hτ]
  · intro a _ b _ hab; exact mul_right_cancel hab
  · intro σ hσ
    refine ⟨σ * τ⁻¹, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [← hτ, ← map_perm_mul]; simpa using hσ

theorem sum_permCount (s : ℕ) (W : Finset V) :
    ∑ S ∈ powersetCard s (univ : Finset V), permCount S W
      = (Fintype.card V).factorial * W.card.choose s := by
  unfold permCount
  simp_rw [card_filter]
  rw [Finset.sum_comm]
  have : ∀ σ : Equiv.Perm V,
      (∑ S ∈ powersetCard s (univ : Finset V), if S.map σ.toEmbedding ⊆ W then 1 else 0)
        = W.card.choose s := by
    intro σ
    rw [← card_filter, ← card_powersetCard]
    refine Finset.card_bij' (fun S _ => S.map σ.toEmbedding)
      (fun T _ => T.map σ.symm.toEmbedding) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powersetCard] at hS ⊢
      exact ⟨hS.2, by simpa using hS.1.2⟩
    · intro T hT
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hT ⊢
      refine ⟨by simpa using hT.2, ?_⟩
      rw [Finset.map_map]; intro x hx; simp at hx; exact hT.1 (by simpa using hx)
    · intro S _; rw [Finset.map_map]; ext; simp
    · intro T _; rw [Finset.map_map]; ext; simp
  rw [Finset.sum_congr rfl (fun σ _ => this σ), sum_const, card_univ, Fintype.card_perm,
    smul_eq_mul]

/-- **Exact count**: `permCount S W · C(n,|S|) = n! · C(|W|,|S|)`. -/
theorem permCount_mul (S W : Finset V) :
    permCount S W * (Fintype.card V).choose S.card
      = (Fintype.card V).factorial * W.card.choose S.card := by
  rw [← sum_permCount S.card W]
  rw [Finset.sum_congr rfl (fun S' hS' => permCount_congr S' S W (mem_powersetCard.mp hS').2)]
  rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, mul_comm]

/-- Permutations sending at most `r` points of `S` outside `S`. -/
def badPerms (S : Finset V) (r : ℕ) : Finset (Equiv.Perm V) :=
  univ.filter (fun σ => (S.filter (fun x => σ x ∉ S)).card ≤ r)

/-- `|badPerms S r| · C(n,s) ≤ C(n,r) · C(s+r,s) · n!` (with `s = |S|`, `s + r ≤ n`). -/
theorem badPerms_card_mul (S : Finset V) (r : ℕ) (hsr : S.card + r ≤ Fintype.card V) :
    (badPerms S r).card * (Fintype.card V).choose S.card
      ≤ (Fintype.card V).choose r * (S.card + r).choose S.card * (Fintype.card V).factorial := by
  set n := Fintype.card V with hn
  set s := S.card with hs
  set Ws := (powersetCard (s + r) (univ : Finset V)).filter (fun W => S ⊆ W) with hWs_def
  have hsub : badPerms S r ⊆ Ws.biUnion
      (fun W => univ.filter (fun σ : Equiv.Perm V => S.map σ.toEmbedding ⊆ W)) := by
    intro σ hσ
    simp only [badPerms, mem_filter, mem_univ, true_and] at hσ
    have hU : (S ∪ S.map σ.toEmbedding).card ≤ s + r := by
      have : S ∪ S.map σ.toEmbedding ⊆ S ∪ (S.filter (fun x => σ x ∉ S)).map σ.toEmbedding := by
        intro y hy
        simp only [mem_union, mem_map, Equiv.coe_toEmbedding, mem_filter] at hy ⊢
        rcases hy with hy | ⟨x, hx, rfl⟩
        · exact Or.inl hy
        · by_cases h : σ x ∈ S
          · exact Or.inl h
          · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩
      calc _ ≤ _ := card_le_card this
        _ ≤ s + ((S.filter (fun x => σ x ∉ S)).map σ.toEmbedding).card := card_union_le _ _
        _ ≤ s + r := by rw [card_map]; omega
    obtain ⟨W, hUW, hW⟩ := exists_superset_card_eq hU hsr
    simp only [Ws, mem_biUnion, mem_filter, mem_powersetCard, subset_univ, true_and, mem_univ]
    exact ⟨W, ⟨hW, subset_union_left.trans hUW⟩, subset_union_right.trans hUW⟩
  have hWs : Ws.card ≤ n.choose r := by
    have hc : (powersetCard r (univ : Finset V)).card = n.choose r := by
      rw [card_powersetCard, card_univ]
    rw [← hc]
    refine card_le_card_of_injOn (fun W => W \ S) ?_ ?_
    · intro W hW
      rw [mem_coe] at hW ⊢
      simp only [Ws, mem_filter, mem_powersetCard, subset_univ, true_and] at hW
      simp only [mem_powersetCard, subset_univ, true_and]
      rw [card_sdiff_of_subset hW.2, hW.1]; omega
    · intro W1 h1 W2 h2 heq
      simp only [Ws, coe_filter, mem_powersetCard, Set.mem_setOf_eq, subset_univ,
        true_and] at h1 h2
      dsimp only at heq
      rw [← union_sdiff_of_subset h1.2, ← union_sdiff_of_subset h2.2, heq]
  calc (badPerms S r).card * n.choose s
        ≤ (∑ W ∈ Ws, permCount S W) * n.choose s := by
          gcongr; exact (card_le_card hsub).trans card_biUnion_le
    _ = ∑ W ∈ Ws, permCount S W * n.choose s := Finset.sum_mul _ _ _
    _ = ∑ W ∈ Ws, n.factorial * (s + r).choose s := by
          refine sum_congr rfl (fun W hW => ?_)
          simp only [Ws, mem_filter, mem_powersetCard] at hW
          rw [permCount_mul, hW.1.2]
    _ = Ws.card * (n.factorial * (s + r).choose s) := by rw [sum_const, smul_eq_mul]
    _ ≤ n.choose r * (n.factorial * (s + r).choose s) := by gcongr
    _ = n.choose r * (s + r).choose s * n.factorial := by ring

end Counting

/-- `∑_{t<m} 2^{-(t+1)} = 1 - 2^{-m}`. -/
theorem sum_half_pow (m : ℕ) :
    ∑ t ∈ range m, ((1:ℝ) / 2) ^ (t + 1) = 1 - (1 / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring

/-- **Union bound.** There are four permutations of `Fin n` such that every `S` with
`1 ≤ |S|` and `2|S| ≤ n` has some `j` with more than `(|S|-1)/20` points `x ∈ S` satisfying
`σⱼ x ∉ S`. -/
theorem exists_good_perms (n : ℕ) :
    ∃ σ : Fin 4 → Equiv.Perm (Fin n), ∀ S : Finset (Fin n), 1 ≤ S.card → 2 * S.card ≤ n →
      ∃ j, (S.card - 1) / 20 < (S.filter (fun x => σ j x ∉ S)).card := by
  by_contra hcon
  push_neg at hcon
  have hsub : (univ : Finset (Fin 4 → Equiv.Perm (Fin n))) ⊆
      (range (n / 2)).biUnion (fun t => (powersetCard (t + 1) (univ : Finset (Fin n))).biUnion
        (fun S => Fintype.piFinset (fun _ : Fin 4 => badPerms S (t / 20)))) := by
    intro σ _
    obtain ⟨S, h1, h2, h3⟩ := hcon σ
    simp only [mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and,
      Fintype.mem_piFinset, badPerms, mem_filter, mem_univ]
    refine ⟨S.card - 1, by omega, S, by omega, fun j => ?_⟩
    exact h3 j
  have hcard := card_le_card hsub
  rw [card_univ, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin] at hcard
  have hcard' := hcard.trans (card_biUnion_le)
  -- bound each block in `ℝ`
  have hblock : ∀ t ∈ range (n / 2),
      ((((powersetCard (t + 1) (univ : Finset (Fin n))).biUnion
        (fun S => Fintype.piFinset (fun _ : Fin 4 => badPerms S (t / 20)))).card : ℕ) : ℝ)
        ≤ ((n.factorial : ℝ) ^ 4) * (1 / 2) ^ (t + 1) := by
    intro t ht
    rw [mem_range] at ht
    set s := t + 1 with hs
    set r := t / 20 with hr
    have hs1 : 1 ≤ s := by omega
    have hsn : 2 * s ≤ n := by omega
    have hrs : r * 20 ≤ s := by omega
    have hCpos : (0:ℝ) < (n.choose s : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hb : ∀ S ∈ powersetCard s (univ : Finset (Fin n)),
        ((badPerms S r).card : ℝ) ≤ n.factorial *
          (((n.choose r : ℝ) * ((s + r).choose s : ℝ)) / n.choose s) := by
      intro S hS
      rw [mem_powersetCard] at hS
      have h := badPerms_card_mul S r (by rw [hS.2, Fintype.card_fin]; omega)
      rw [hS.2, Fintype.card_fin] at h
      have h' : ((badPerms S r).card : ℝ) * (n.choose s : ℝ)
          ≤ (n.choose r : ℝ) * ((s + r).choose s : ℝ) * (n.factorial : ℝ) := by
        exact_mod_cast h
      rw [mul_div_assoc', le_div_iff₀ hCpos]; linarith
    calc ((((powersetCard s (univ : Finset (Fin n))).biUnion
          (fun S => Fintype.piFinset (fun _ : Fin 4 => badPerms S r))).card : ℕ) : ℝ)
        ≤ ((∑ S ∈ powersetCard s (univ : Finset (Fin n)),
            (Fintype.piFinset (fun _ : Fin 4 => badPerms S r)).card : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ((badPerms S r).card : ℝ) ^ 4 := by
          push_cast
          refine sum_congr rfl (fun S _ => ?_)
          rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]; push_cast; ring
      _ ≤ ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ((n.factorial : ℝ) *
            (((n.choose r : ℝ) * ((s + r).choose s : ℝ)) / n.choose s)) ^ 4 := by
          refine sum_le_sum (fun S hS => ?_)
          exact pow_le_pow_left₀ (by positivity) (hb S hS) 4
      _ = ((n.factorial : ℝ) ^ 4) * ((n.choose s : ℝ) *
            (((n.choose r : ℝ) * ((s + r).choose s : ℝ)) / n.choose s) ^ 4) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ((n.factorial : ℝ) ^ 4) * (1 / 2) ^ s := by
          gcongr; exact union_term_le n s r hs1 hsn hrs
  have hR : ((n.factorial ^ 4 : ℕ) : ℝ) ≤ ((n.factorial : ℝ) ^ 4) * (1 - (1 / 2) ^ (n / 2)) := by
    calc ((n.factorial ^ 4 : ℕ) : ℝ) ≤ ((∑ t ∈ range (n / 2),
          ((powersetCard (t + 1) (univ : Finset (Fin n))).biUnion
            (fun S => Fintype.piFinset (fun _ : Fin 4 => badPerms S (t / 20)))).card : ℕ) : ℝ) := by
          exact_mod_cast hcard'
      _ = ∑ t ∈ range (n / 2), ((((powersetCard (t + 1) (univ : Finset (Fin n))).biUnion
            (fun S => Fintype.piFinset (fun _ : Fin 4 => badPerms S (t / 20)))).card : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ t ∈ range (n / 2), ((n.factorial : ℝ) ^ 4) * (1 / 2) ^ (t + 1) := sum_le_sum hblock
      _ = ((n.factorial : ℝ) ^ 4) * (1 - (1 / 2) ^ (n / 2)) := by
          rw [← mul_sum, sum_half_pow]
  have hpos : (0:ℝ) < (n.factorial : ℝ) ^ 4 := by positivity
  have hhalf : (0:ℝ) < (1 / 2) ^ (n / 2) := by positivity
  push_cast at hR
  nlinarith

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The simple graph generated by a family of permutations: `x ~ y` iff `x ≠ y` and some
`σⱼ` maps one to the other.  Fixed points (would-be loops) give no edge; parallel edges
collapse. -/
def permGraph {d : ℕ} (σ : Fin d → Equiv.Perm V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ j, σ j x = y ∨ σ j y = x
  symm := ⟨fun _ _ ⟨h, j, hj⟩ => ⟨h.symm, j, hj.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

instance permGraph.decRel {d : ℕ} (σ : Fin d → Equiv.Perm V) :
    DecidableRel (permGraph σ).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ∃ j, σ j x = y ∨ σ j y = x))

/-- The edge boundary: edges of `G` with one end in `S` and the other outside `S`. -/
def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ x ∈ S, ∃ y ∉ S, e = s(x, y))

theorem edgeBoundary_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgeBoundary G Sᶜ = edgeBoundary G S := by
  ext e
  simp only [edgeBoundary, mem_filter, mem_compl, not_not]
  constructor
  · rintro ⟨he, x, hx, y, hy, rfl⟩; exact ⟨he, y, hy, x, hx, Sym2.eq_swap⟩
  · rintro ⟨he, x, hx, y, hy, rfl⟩; exact ⟨he, y, hy, x, hx, Sym2.eq_swap⟩

theorem permGraph_degree_le {d : ℕ} (σ : Fin d → Equiv.Perm V) (x : V) :
    (permGraph σ).degree x ≤ 2 * d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (permGraph σ).neighborFinset x ⊆
      (univ.image (fun j => σ j x)) ∪ (univ.image (fun j => (σ j).symm x)) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨_, j, hj⟩ := hy
    rcases hj with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨j, mem_univ _, h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨j, mem_univ _, (Equiv.symm_apply_eq _).mpr h.symm⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ.image (fun j => σ j x)).card + (univ.image (fun j => (σ j).symm x)).card :=
        card_union_le _ _
    _ ≤ (univ : Finset (Fin d)).card + (univ : Finset (Fin d)).card :=
        add_le_add card_image_le card_image_le
    _ = 2 * d := by rw [card_univ, Fintype.card_fin]; ring

/-- For each `j`, the points of `S` sent outside `S` by `σⱼ` inject into the edge boundary. -/
theorem card_filter_le_edgeBoundary {d : ℕ} (σ : Fin d → Equiv.Perm V) (j : Fin d)
    (S : Finset V) :
    (S.filter (fun x => σ j x ∉ S)).card ≤ (edgeBoundary (permGraph σ) S).card := by
  refine card_le_card_of_injOn (fun x => s(x, σ j x)) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_filter] at hx
    rw [mem_coe]
    simp only [edgeBoundary, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    refine ⟨⟨fun h => hx.2 (h ▸ hx.1), j, Or.inl rfl⟩, x, hx.1, σ j x, hx.2, rfl⟩
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq] at hx hy
    dsimp only at hxy
    rcases Sym2.eq_iff.mp hxy with h | h
    · exact h.1
    · exact absurd (h.1 ▸ hx.1) hy.2

end Graph

/-- **Expansion of a suitable permutation graph on `Fin n`.** -/
theorem exists_permGraph_expander (n : ℕ) :
    ∃ σ : Fin 4 → Equiv.Perm (Fin n), ∀ S : Finset (Fin n),
      min S.card Sᶜ.card ≤ 20 * (edgeBoundary (permGraph σ) S).card := by
  obtain ⟨σ, hσ⟩ := exists_good_perms n
  refine ⟨σ, fun S => ?_⟩
  have key : ∀ T : Finset (Fin n), 2 * T.card ≤ n →
      T.card ≤ 20 * (edgeBoundary (permGraph σ) T).card := by
    intro T hT
    rcases Nat.eq_zero_or_pos T.card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨j, hj⟩ := hσ T hpos hT
      have := card_filter_le_edgeBoundary σ j T
      omega
  have hc : Sᶜ.card = n - S.card := by rw [card_compl, Fintype.card_fin]
  have hSle : S.card ≤ n := by simpa using card_le_univ S
  by_cases h : 2 * S.card ≤ n
  · exact (min_le_left _ _).trans (key S h)
  · have h2 : 2 * Sᶜ.card ≤ n := by omega
    have := key Sᶜ h2
    rw [edgeBoundary_compl] at this
    exact (min_le_right _ _).trans this

/-- **Explicit bounded-degree expander family.** For every `N` there is a simple graph on
`Fin N` (so `|V(H)| = N`) of maximum degree `≤ 8` with
`|∂_H S| ≥ (1/20) · min(|S|, |V(H) \ S|)` for every vertex subset `S`. -/
theorem exists_expander_fin (N : ℕ) :
    ∃ (H : SimpleGraph (Fin N)) (_ : DecidableRel H.Adj),
      (∀ v, H.degree v ≤ 8) ∧
      ∀ S : Finset (Fin N), (1 / 20 : ℝ) * (min S.card Sᶜ.card : ℕ) ≤ (edgeBoundary H S).card := by
  obtain ⟨σ, hσ⟩ := exists_permGraph_expander N
  refine ⟨permGraph σ, inferInstance, fun v => ?_, fun S => ?_⟩
  · simpa using permGraph_degree_le σ v
  · have := hσ S
    have h' : ((min S.card Sᶜ.card : ℕ) : ℝ) ≤ 20 * ((edgeBoundary (permGraph σ) S).card : ℝ) := by
      exact_mod_cast this
    linarith

/-- **Expander existence in the form required by §9.** There are absolute constants
`δ = 8`, `h = 1/20 > 0`, `p = 1` such that for every `N ≥ 1` there is a finite simple graph `H`
with `N ≤ |V(H)| ≤ p N`, maximum degree `≤ δ`, and `|∂_H S| ≥ h · min(|S|, |V(H) \ S|)` for
every vertex subset `S`. -/
theorem exists_bounded_degree_expander :
    ∃ (δ : ℕ) (h : ℝ) (p : ℕ), 0 < h ∧ 1 ≤ p ∧ ∀ N : ℕ, 1 ≤ N →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : SimpleGraph V)
        (_ : DecidableRel H.Adj),
        N ≤ Fintype.card V ∧ Fintype.card V ≤ p * N ∧ (∀ v, H.degree v ≤ δ) ∧
        ∀ S : Finset V, h * (min S.card (univ \ S).card : ℕ) ≤ (edgeBoundary H S).card := by
  refine ⟨8, 1 / 20, 1, by norm_num, le_rfl, fun N _ => ?_⟩
  obtain ⟨H, hdec, hdeg, hexp⟩ := exists_expander_fin N
  refine ⟨Fin N, inferInstance, inferInstance, H, hdec, by simp, by simp, hdeg, fun S => ?_⟩
  have := hexp S
  rwa [compl_eq_univ_sdiff] at this

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander
