/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Physical private channels (§7 of `DENSE_EXPANDER_INTEGER_FILLING_20261015.md`)

For a reference arc `e = (u, v)` of a cyclically tripartite digraph `Q` on `H`, a sign
`b : Bool` and an index `i : Fin T`, the channel `chan e b i` is a directed path on
`H ⊕ Priv H T` with private interior vertices `inr (e, b, i, j)`:

* positive (`b = true`):  `u → p₀ → p₁ → p₂ → v`        (4 arcs),
* negative (`b = false`): `v → q₀ → q₁ → q₂ → q₃ → u`   (5 arcs).

The lengths are `3 + (colour difference mod 3)`, so the private colouring `privColor`
makes every channel cyclically tripartite.  This file proves the per-channel facts used by the
exact-cover theorem: colouring, arc-disjointness of distinct channels, disjointness from lifted
base arcs, cardinality, and the net degree `in − out = [end] − [start]`.

The arc vocabulary (`IsCyc`, `inDeg`, `outDeg`, `Balanced`, `liftArc`) is the one of
`LatinCore/Cycles/Defs.lean`, so the results are stated in the format of `DenseRefinerWith`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization

open Finset PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

/-! ### Generic degree bookkeeping -/

section Generic

variable {W : Type*} [DecidableEq W]

/-- Net degree `in − out` of an arc set at a vertex, in `ℤ`. -/
def net (E : Finset (W × W)) (x : W) : ℤ := (inDeg E x : ℤ) - outDeg E x

theorem balanced_iff_net (E : Finset (W × W)) : Cycles.Balanced E ↔ ∀ x, net E x = 0 := by
  unfold Cycles.Balanced net
  constructor
  · intro h x; rw [h x]; ring
  · intro h x; have := h x; omega

theorem inDeg_union_of_disjoint {A B : Finset (W × W)} (h : Disjoint A B) (x : W) :
    inDeg (A ∪ B) x = inDeg A x + inDeg B x := by
  unfold inDeg; rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem outDeg_union_of_disjoint {A B : Finset (W × W)} (h : Disjoint A B) (x : W) :
    outDeg (A ∪ B) x = outDeg A x + outDeg B x := by
  unfold outDeg; rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem net_union_of_disjoint {A B : Finset (W × W)} (h : Disjoint A B) (x : W) :
    net (A ∪ B) x = net A x + net B x := by
  unfold net; rw [inDeg_union_of_disjoint h, outDeg_union_of_disjoint h]; push_cast; ring

theorem net_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Finset (W × W))
    (h : (s : Set ι).PairwiseDisjoint f) (x : W) :
    net (s.biUnion f) x = ∑ i ∈ s, net (f i) x := by
  unfold net inDeg outDeg
  rw [filter_biUnion, filter_biUnion, card_biUnion, card_biUnion]
  · push_cast; rw [← sum_sub_distrib]
  · intro i hi j hj hij; exact disjoint_filter_filter (h hi hj hij)
  · intro i hi j hj hij; exact disjoint_filter_filter (h hi hj hij)

/-- The arc set of a walk `v 0 → v 1 → ⋯ → v m` whose arcs are pairwise distinct. -/
def pathArcs (v : ℕ → W) (m : ℕ) : Finset (W × W) := (range m).image (fun j => (v j, v (j + 1)))

theorem net_pathArcs (v : ℕ → W) (m : ℕ)
    (hinj : Set.InjOn (fun j => (v j, v (j + 1))) (range m : Set ℕ)) (x : W) :
    net (pathArcs v m) x = (if v m = x then 1 else 0) - (if v 0 = x then 1 else 0) := by
  have hin : (inDeg (pathArcs v m) x : ℤ) = ∑ j ∈ range m, (if v (j + 1) = x then 1 else 0) := by
    unfold inDeg pathArcs
    rw [filter_image, card_image_of_injOn (hinj.mono (by intro j hj; simp at hj ⊢; exact hj.1))]
    rw [card_filter]; push_cast; rfl
  have hout : (outDeg (pathArcs v m) x : ℤ) = ∑ j ∈ range m, (if v j = x then 1 else 0) := by
    unfold outDeg pathArcs
    rw [filter_image, card_image_of_injOn (hinj.mono (by intro j hj; simp at hj ⊢; exact hj.1))]
    rw [card_filter]; push_cast; rfl
  unfold net; rw [hin, hout, ← sum_sub_distrib]
  exact sum_range_sub (fun j => (if v j = x then (1:ℤ) else 0)) m

theorem card_pathArcs_le (v : ℕ → W) (m : ℕ) : (pathArcs v m).card ≤ m := by
  unfold pathArcs; exact card_image_le.trans (by simp)

end Generic

/-! ### Channels -/

variable {H : Type} [DecidableEq H] {T : ℕ}

/-- Private vertices: `(arc, sign, index, position)`. -/
abbrev Priv (H : Type) (T : ℕ) := (H × H) × Bool × Fin T × Fin 4

/-- Vertices of the extended digraph. -/
abbrev XV (H : Type) (T : ℕ) := H ⊕ Priv H T

instance instDecEqXV : DecidableEq (XV H T) := instDecidableEqSum

instance instDecEqXVArc : DecidableEq (XV H T × XV H T) := instDecidableEqProd

/-- Number of arcs of a channel: `4` (positive) or `5` (negative). -/
def chanLen (b : Bool) : ℕ := if b then 4 else 5

/-- Start of a channel: tail of `e` (positive) or head of `e` (negative). -/
def chanStart (e : H × H) (b : Bool) : H := if b then e.1 else e.2

/-- End of a channel. -/
def chanEnd (e : H × H) (b : Bool) : H := if b then e.2 else e.1

/-- The `j`-th vertex of the channel `(e, b, i)`. -/
def chanVert (e : H × H) (b : Bool) (i : Fin T) (j : ℕ) : XV H T :=
  if j = 0 then Sum.inl (chanStart e b)
  else if j < chanLen b then Sum.inr (e, b, i, ⟨(j - 1) % 4, Nat.mod_lt _ (by norm_num)⟩)
  else Sum.inl (chanEnd e b)

/-- The arc set of the channel `(e, b, i)`. -/
def chan (e : H × H) (b : Bool) (i : Fin T) : Finset (XV H T × XV H T) :=
  pathArcs (chanVert e b i) (chanLen b)

/-- Colour of a private vertex. -/
def privColor (c : H → ZMod 3) : Priv H T → ZMod 3 :=
  fun p => c (chanStart p.1 p.2.1) + ((p.2.2.2 : ℕ) + 1 : ℕ)

/-- The token `(arc, sign, index)` of a private vertex. -/
def privTok (p : Priv H T) : (H × H) × Bool × Fin T := (p.1, p.2.1, p.2.2.1)

theorem chanLen_ge (b : Bool) : 4 ≤ chanLen b := by cases b <;> simp [chanLen]

theorem chanLen_le (b : Bool) : chanLen b ≤ 5 := by cases b <;> simp [chanLen]

omit [DecidableEq H] in
theorem chanVert_injOn (e : H × H) (b : Bool) (i : Fin T) :
    Set.InjOn (chanVert e b i) (range (chanLen b) : Set ℕ) := by
  intro j hj k hk hjk
  simp only [coe_range, Set.mem_Iio] at hj hk
  have h5 := chanLen_le b
  unfold chanVert at hjk
  by_cases hj0 : j = 0 <;> by_cases hk0 : k = 0
  · omega
  · simp [hj0, hk0, hk] at hjk
  · simp [hj0, hk0, hj] at hjk
  · simp only [hj0, hk0, hj, hk, if_false, if_true, Sum.inr.injEq, Prod.mk.injEq,
      Fin.mk.injEq, true_and] at hjk
    omega

omit [DecidableEq H] in
theorem chan_arc_injOn (e : H × H) (b : Bool) (i : Fin T) :
    Set.InjOn (fun j => (chanVert e b i j, chanVert e b i (j + 1)))
      (range (chanLen b) : Set ℕ) := by
  intro j hj k hk hjk
  exact chanVert_injOn e b i hj hk (Prod.mk.inj hjk).1

theorem mem_chan {e : H × H} {b : Bool} {i : Fin T} {α : XV H T × XV H T} :
    α ∈ chan e b i ↔ ∃ j < chanLen b, (chanVert e b i j, chanVert e b i (j + 1)) = α := by
  simp [chan, pathArcs]

omit [DecidableEq H] in
/-- Every vertex of a channel is either a base vertex or one of its own private vertices. -/
theorem chanVert_cases (e : H × H) (b : Bool) (i : Fin T) (j : ℕ) :
    (∃ x, chanVert e b i j = Sum.inl x) ∨
      ∃ p : Priv H T, chanVert e b i j = Sum.inr p ∧ privTok p = (e, b, i) := by
  unfold chanVert
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

/-- Every arc of a channel has a private endpoint, and all private endpoints carry the
channel's token. -/
theorem chan_arc_priv {e : H × H} {b : Bool} {i : Fin T} {α : XV H T × XV H T}
    (hα : α ∈ chan e b i) :
    (∃ p : Priv H T, α.1 = Sum.inr p ∨ α.2 = Sum.inr p) ∧
      (∀ p, α.1 = Sum.inr p → privTok p = (e, b, i)) ∧
      (∀ p, α.2 = Sum.inr p → privTok p = (e, b, i)) := by
  obtain ⟨j, hj, rfl⟩ := mem_chan.mp hα
  have h4 := chanLen_ge b
  refine ⟨?_, ?_, ?_⟩
  · by_cases hj0 : j = 0
    · refine ⟨(e, b, i, ⟨(j + 1 - 1) % 4, Nat.mod_lt _ (by norm_num)⟩), Or.inr ?_⟩
      simp only [chanVert, hj0]; simp; omega
    · refine ⟨(e, b, i, ⟨(j - 1) % 4, Nat.mod_lt _ (by norm_num)⟩), Or.inl ?_⟩
      simp [chanVert, hj0, hj]
  · intro p hp
    rcases chanVert_cases e b i j with ⟨x, hx⟩ | ⟨q, hq, hqt⟩
    · rw [hx] at hp; cases hp
    · rw [hq] at hp; cases hp; exact hqt
  · intro p hp
    rcases chanVert_cases e b i (j + 1) with ⟨x, hx⟩ | ⟨q, hq, hqt⟩
    · rw [hx] at hp; cases hp
    · rw [hq] at hp; cases hp; exact hqt

/-- Distinct channels are arc-disjoint. -/
theorem chan_eq_of_mem {t t' : (H × H) × Bool × Fin T} {α : XV H T × XV H T}
    (h : α ∈ chan t.1 t.2.1 t.2.2) (h' : α ∈ chan t'.1 t'.2.1 t'.2.2) : t = t' := by
  obtain ⟨⟨p, hp⟩, h1, h2⟩ := chan_arc_priv h
  obtain ⟨-, h1', h2'⟩ := chan_arc_priv h'
  rcases hp with hp | hp
  · simpa using (h1 p hp).symm.trans (h1' p hp)
  · simpa using (h2 p hp).symm.trans (h2' p hp)

theorem chan_disjoint {t t' : (H × H) × Bool × Fin T} (hne : t ≠ t') :
    Disjoint (chan t.1 t.2.1 t.2.2) (chan t'.1 t'.2.1 t'.2.2) := by
  rw [Finset.disjoint_left]
  intro α h h'
  exact hne (chan_eq_of_mem h h')

/-- Lifted base arcs never lie in a channel. -/
theorem inl_inl_not_mem_chan (e : H × H) (b : Bool) (i : Fin T) (x y : H) :
    ((Sum.inl x, Sum.inl y) : XV H T × XV H T) ∉ chan e b i := by
  intro h
  obtain ⟨⟨p, hp⟩, -, -⟩ := chan_arc_priv h
  rcases hp with hp | hp <;> cases hp

theorem liftArc_not_mem_chan (e : H × H) (b : Bool) (i : Fin T) (f : H × H) :
    liftArc H (Priv H T) f ∉ chan e b i :=
  inl_inl_not_mem_chan e b i f.1 f.2

theorem chan_card_le (e : H × H) (b : Bool) (i : Fin T) : (chan e b i).card ≤ 5 :=
  (card_pathArcs_le _ _).trans (chanLen_le b)

theorem chan_nonempty (e : H × H) (b : Bool) (i : Fin T) : (chan e b i).Nonempty :=
  ⟨_, mem_chan.mpr ⟨0, by have := chanLen_ge b; omega, rfl⟩⟩

omit [DecidableEq H] in
theorem chanVert_zero (e : H × H) (b : Bool) (i : Fin T) :
    chanVert e b i 0 = Sum.inl (chanStart e b) := by simp [chanVert]

theorem chanVert_len (e : H × H) (b : Bool) (i : Fin T) :
    chanVert e b i (chanLen b) = Sum.inl (chanEnd e b) := by
  have := chanLen_ge b
  simp [chanVert]; omega

/-- **Net degree of a channel**: `in − out = [end] − [start]`. -/
theorem net_chan (e : H × H) (b : Bool) (i : Fin T) (x : XV H T) :
    net (chan e b i) x =
      (if Sum.inl (chanEnd e b) = x then 1 else 0) -
        (if Sum.inl (chanStart e b) = x then 1 else 0) := by
  unfold chan
  rw [net_pathArcs _ _ (chan_arc_injOn e b i), chanVert_zero, chanVert_len]

omit [DecidableEq H] in
/-- Colours along a channel: the `j`-th vertex has colour `c(start) + j`. -/
theorem chanVert_color (c : H → ZMod 3) (e : H × H) (he : c e.2 = c e.1 + 1) (b : Bool)
    (i : Fin T) (j : ℕ) (hj : j ≤ chanLen b) :
    Sum.elim c (privColor c) (chanVert e b i j) = c (chanStart e b) + (j : ZMod 3) := by
  unfold chanVert
  split_ifs with h0 hlt
  · subst h0; simp
  · simp only [Sum.elim_inr, privColor]
    have : (j - 1) % 4 + 1 = j := by have := chanLen_le b; omega
    rw [this]
  · have hj' : j = chanLen b := by omega
    subst hj'
    cases b
    · simp only [chanEnd, chanStart, chanLen, Bool.false_eq_true, if_false, Sum.elim_inl, he]
      push_cast
      have : (5 : ZMod 3) = 2 := by decide
      rw [this]; ring_nf
      have : (3 : ZMod 3) = 0 := by decide
      calc c e.1 = c e.1 + 3 := by rw [this, add_zero]
        _ = _ := by ring
    · simp only [chanEnd, chanStart, chanLen, if_true, Sum.elim_inl, he]
      push_cast
      have : (4 : ZMod 3) = 1 := by decide
      rw [this]

/-- Every channel over an arc of a cyclically tripartite digraph is cyclically tripartite. -/
theorem chan_isCyc (c : H → ZMod 3) (e : H × H) (he : c e.2 = c e.1 + 1) (b : Bool)
    (i : Fin T) : IsCyc (Sum.elim c (privColor c)) (chan e b i) := by
  intro α hα
  obtain ⟨j, hj, rfl⟩ := mem_chan.mp hα
  rw [chanVert_color c e he b i j hj.le, chanVert_color c e he b i (j + 1) hj]
  push_cast; ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization
