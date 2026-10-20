/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.UnitChannelRouting
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.EightPermutation

@[expose] public section

/-!
# The directed eight-permutation unit-capacity channel network

For `σ : Fin 8 → Equiv.Perm (Fin n)` the channels are the indexed pairs
`E_σ = {(j, u) : Fin 8 × Fin n // σ j u ≠ u}` with `src (j,u) = u`, `dst (j,u) = σ j u`.
Fixed points (loops) are dropped; different indices with the same endpoints remain
different channels (no merging, no bidirected copies).

* at most `8` outgoing and `8` incoming channels per port (total port degree `≤ 16`);
* for the permutations of `Expander.EightPerm.exists_eight_perm_cut`, every cut has incoming
  channel capacity `≥ min |S| |Sᶜ|`;
* hence (via `UnitChannelRouting.exists_unit_routing`) every zero-sum demand
  `b : Fin n → ℤ` with `|b v| ≤ 1` is realized by a set `T` of distinct channels with
  `#(T ending at v) - #(T starting at v) = b v`.

This module does not embed the channels physically.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.EightPermChannels

open Finset ChannelSelection

variable {n : ℕ}

/-- Indexed nonloop directed channels of eight permutations. -/
abbrev Channel (σ : Fin 8 → Equiv.Perm (Fin n)) : Type :=
  {p : Fin 8 × Fin n // σ p.1 p.2 ≠ p.2}

/-- Tail of a channel `(j, u)`: the port `u`. -/
def src (σ : Fin 8 → Equiv.Perm (Fin n)) (e : Channel σ) : Fin n := e.1.2

/-- Head of a channel `(j, u)`: the port `σ j u`. -/
def dst (σ : Fin 8 → Equiv.Perm (Fin n)) (e : Channel σ) : Fin n := σ e.1.1 e.1.2

theorem src_ne_dst (σ : Fin 8 → Equiv.Perm (Fin n)) (e : Channel σ) :
    src σ e ≠ dst σ e := fun h => e.2 h.symm

/-- At most eight outgoing channels per port. -/
theorem out_degree_le (σ : Fin 8 → Equiv.Perm (Fin n)) (u : Fin n) :
    (univ.filter (fun e : Channel σ => src σ e = u)).card ≤ 8 := by
  have h := card_le_card_of_injOn (fun e : Channel σ => e.1.1)
    (s := univ.filter (fun e : Channel σ => src σ e = u))
    (t := (univ : Finset (Fin 8))) (fun _ _ => mem_coe.2 (mem_univ _)) (by
      intro e he e' he' hj
      have he := (mem_filter.1 (mem_coe.1 he)).2
      have he' := (mem_filter.1 (mem_coe.1 he')).2
      apply Subtype.ext
      exact Prod.ext hj (he.trans he'.symm))
  simpa using h

/-- At most eight incoming channels per port. -/
theorem in_degree_le (σ : Fin 8 → Equiv.Perm (Fin n)) (v : Fin n) :
    (univ.filter (fun e : Channel σ => dst σ e = v)).card ≤ 8 := by
  have h := card_le_card_of_injOn (fun e : Channel σ => e.1.1)
    (s := univ.filter (fun e : Channel σ => dst σ e = v))
    (t := (univ : Finset (Fin 8))) (fun _ _ => mem_coe.2 (mem_univ _)) (by
      intro e he e' he' hj
      have he := (mem_filter.1 (mem_coe.1 he)).2
      have he' := (mem_filter.1 (mem_coe.1 he')).2
      apply Subtype.ext
      refine Prod.ext hj ?_
      have h2 : σ e.1.1 e.1.2 = σ e.1.1 e'.1.2 := by
        have : σ e'.1.1 e'.1.2 = σ e.1.1 e'.1.2 := by
          simp only at hj
          rw [hj]
        exact (he.trans he'.symm).trans this
      exact (σ e.1.1).injective h2)
  simpa using h

/-- Total port degree at most `16`. -/
theorem total_degree_le (σ : Fin 8 → Equiv.Perm (Fin n)) (u : Fin n) :
    (univ.filter (fun e : Channel σ => src σ e = u)).card +
      (univ.filter (fun e : Channel σ => dst σ e = u)).card ≤ 16 := by
  have := out_degree_le σ u
  have := in_degree_le σ u
  omega

/-- Channel capacity from `A` to `B` counts channels with tail in `A` and head in `B`. -/
theorem sum_capacity_eq (σ : Fin 8 → Equiv.Perm (Fin n)) (A B : Finset (Fin n)) :
    ∑ u ∈ A, ∑ v ∈ B, capacity (src σ) (dst σ) u v
      = (univ.filter (fun e : Channel σ => src σ e ∈ A ∧ dst σ e ∈ B)).card := by
  have h1 : ∀ u, ∑ v ∈ B, capacity (src σ) (dst σ) u v
      = ((univ.filter (fun e : Channel σ => dst σ e ∈ B)).filter (fun e => src σ e = u)).card := by
    intro u
    have := sum_card_fiberwise_eq_card_filter
      (univ.filter (fun e : Channel σ => src σ e = u)) B (dst σ)
    simp only [filter_filter] at this
    unfold capacity
    rw [this]
    congr 1
    ext e; simp [and_comm]
  rw [sum_congr rfl fun u _ => h1 u, sum_card_fiberwise_eq_card_filter, filter_filter]
  congr 1; ext e; simp [and_comm]


/-- Channels crossing a cut dominate the permutation arcs crossing it. -/
theorem sum_outCount_le_capacity (σ : Fin 8 → Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    ∑ j : Fin 8, (A.filter (fun u => σ j u ∉ A)).card
      ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, capacity (src σ) (dst σ) u v := by
  rw [sum_capacity_eq]
  let P : Finset (Fin 8 × Fin n) := univ.filter (fun p => p.2 ∈ A ∧ σ p.1 p.2 ∉ A)
  have hP : P.card = ∑ j : Fin 8, (A.filter (fun u => σ j u ∉ A)).card := by
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun j _ => ?_
    rw [card_filter, ← sum_subset (subset_univ A) (fun x _ hx => by simp [hx])]
    exact sum_congr rfl fun x hx => by simp [hx]
  have hsub : P ⊆ (univ.filter (fun e : Channel σ => src σ e ∈ A ∧ dst σ e ∈ Aᶜ)).map
      (Function.Embedding.subtype _) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hp
    refine mem_map.2 ⟨⟨p, fun h => h2 (by rw [h]; exact h1)⟩, mem_filter.2 ⟨mem_univ _, h1, ?_⟩, rfl⟩
    simpa [dst] using h2
  rw [← hP]
  exact (card_le_card hsub).trans (card_map _).le

/-- Incoming cut capacity from the unit directed cut property of the permutations. -/
theorem incoming_cut_of_perm_cut (σ : Fin 8 → Equiv.Perm (Fin n))
    (hσ : ∀ S : Finset (Fin n),
      min S.card Sᶜ.card ≤ ∑ j : Fin 8, (S.filter (fun u => σ j u ∉ S)).card)
    (S : Finset (Fin n)) :
    min S.card Sᶜ.card ≤ ∑ u ∈ Sᶜ, ∑ v ∈ S, capacity (src σ) (dst σ) u v := by
  have h := (hσ Sᶜ).trans (sum_outCount_le_capacity σ Sᶜ)
  rwa [compl_compl, min_comm] at h

/-- Unit routing on any eight-permutation network with unit directed cut capacity. -/
theorem unit_routing_of_perm_cut (σ : Fin 8 → Equiv.Perm (Fin n))
    (hσ : ∀ S : Finset (Fin n),
      min S.card Sᶜ.card ≤ ∑ j : Fin 8, (S.filter (fun u => σ j u ∉ S)).card)
    (b : Fin n → ℤ) (hsum : ∑ v, b v = 0) (hb : ∀ v, |b v| ≤ 1) :
    ∃ T : Finset (Channel σ), ∀ v,
      ((T.filter (fun e => dst σ e = v)).card : ℤ) -
        ((T.filter (fun e => src σ e = v)).card : ℤ) = b v := by
  apply UnitChannelRouting.exists_unit_routing (src σ) (dst σ) (src_ne_dst σ) _ b hsum
  · intro v
    exact_mod_cast hb v
  · intro S
    have h := incoming_cut_of_perm_cut σ hσ S
    have h' : ((min S.card Sᶜ.card : ℕ) : ℝ)
        ≤ ((∑ u ∈ Sᶜ, ∑ v ∈ S, capacity (src σ) (dst σ) u v : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    exact h'

/-- **Second target.** The fixed directed eight-permutation channel network: port degrees
`≤ 8` in and `≤ 8` out, incoming cut capacity `≥ min |S| |Sᶜ|`, and an integral channel
selection for every zero-sum unit demand. The network is chosen before the demand. -/
theorem exists_eight_perm_channel_network (n : ℕ) :
    ∃ σ : Fin 8 → Equiv.Perm (Fin n),
      (∀ S : Finset (Fin n),
        min S.card Sᶜ.card ≤ ∑ j : Fin 8, (S.filter (fun u => σ j u ∉ S)).card) ∧
      (∀ u, (univ.filter (fun e : Channel σ => src σ e = u)).card ≤ 8) ∧
      (∀ v, (univ.filter (fun e : Channel σ => dst σ e = v)).card ≤ 8) ∧
      (∀ S : Finset (Fin n),
        min S.card Sᶜ.card ≤ ∑ u ∈ Sᶜ, ∑ v ∈ S, capacity (src σ) (dst σ) u v) ∧
      ∀ b : Fin n → ℤ, ∑ v, b v = 0 → (∀ v, |b v| ≤ 1) →
        ∃ T : Finset (Channel σ), ∀ v,
          ((T.filter (fun e => dst σ e = v)).card : ℤ) -
            ((T.filter (fun e => src σ e = v)).card : ℤ) = b v := by
  obtain ⟨σ, hσ⟩ := Expander.EightPerm.exists_eight_perm_cut n
  exact ⟨σ, hσ, out_degree_le σ, in_degree_le σ, incoming_cut_of_perm_cut σ hσ,
    fun b hsum hb => unit_routing_of_perm_cut σ hσ b hsum hb⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.EightPermChannels

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.EightPermChannels.exists_eight_perm_channel_network
