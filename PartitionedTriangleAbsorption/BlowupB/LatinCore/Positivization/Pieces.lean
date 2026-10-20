/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.Channels

@[expose] public section

/-!
# Catalogue pieces of the physical positivization (§7)

* A *face* is a signed `{±1}`-valued circulation on arcs of `Q` (`Face.IsCirc`): triangles
  `a → b → c → a` (all signs `+1`) and the signed rectangles of §§4–6 are faces.
* `facePiece F s f` is the traversal of `F` with global sign `s`, using on each arc `e` of `F`
  the channel with index `f e`; an arc whose orientation agrees with `s` uses its positive
  channel, otherwise its negative channel.
* `pairPiece e i j` (class 2) is a positive channel together with a negative channel of the
  same arc; `tailPiece e` (class 3) is the base arc `e` together with its negative channel `0`.

All pieces are balanced, nonempty, cyclically tripartite and have at most `5 |F|`, `9`, `6`
arcs respectively.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization

open Finset PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

variable {H : Type} [DecidableEq H] {T : ℕ}

/-- A face: a support of reference arcs together with the orientation (`true = +1`) of each. -/
structure Face (H : Type) where
  /-- The arcs of `Q` used by the face. -/
  supp : Finset (H × H)
  /-- Orientation of each arc inside the face (`true` = traversed forwards). -/
  ori : H × H → Bool

/-- `true ↦ 1`, `false ↦ -1`. -/
def oriSign (b : Bool) : ℤ := if b then 1 else -1

/-- The signed incidence vector of a face. -/
def Face.val (F : Face H) (e : H × H) : ℤ := if e ∈ F.supp then oriSign (F.ori e) else 0

/-- A face is a circulation: signed in-flow equals signed out-flow at every vertex. -/
def Face.IsCirc (F : Face H) : Prop :=
  ∀ v : H, ∑ e ∈ F.supp, oriSign (F.ori e) * (if e.2 = v then 1 else 0)
    = ∑ e ∈ F.supp, oriSign (F.ori e) * (if e.1 = v then 1 else 0)

/-- The channel sign used on an arc of orientation `o` by a traversal of sign `s`. -/
def useDir (s o : Bool) : Bool := (s == o)

/-- Traversal of a face with sign `s` and channel choice `f`. -/
def facePiece (F : Face H) (s : Bool) (f : {e // e ∈ F.supp} → Fin T) :
    Finset (XV H T × XV H T) :=
  F.supp.attach.biUnion (fun e => chan e.1 (useDir s (F.ori e.1)) (f e))

/-- Class 2: a positive and a negative channel of the same arc. -/
def pairPiece (e : H × H) (i j : Fin T) : Finset (XV H T × XV H T) :=
  chan e true i ∪ chan e false j

/-- Class 3: a base arc together with its negative channel number `0`. -/
def tailPiece (hT : 0 < T) (e : H × H) : Finset (XV H T × XV H T) :=
  insert (liftArc H (Priv H T) e) (chan e false ⟨0, hT⟩)

theorem mem_facePiece {F : Face H} {s : Bool} {f : {e // e ∈ F.supp} → Fin T}
    {α : XV H T × XV H T} :
    α ∈ facePiece F s f ↔ ∃ e, ∃ he : e ∈ F.supp, α ∈ chan e (useDir s (F.ori e)) (f ⟨e, he⟩) := by
  simp only [facePiece, mem_biUnion, mem_attach, true_and]
  constructor
  · rintro ⟨⟨e, he⟩, h⟩; exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨⟨e, he⟩, h⟩

theorem facePiece_pairwiseDisjoint (F : Face H) (s : Bool) (f : {e // e ∈ F.supp} → Fin T) :
    ((F.supp.attach : Finset {e // e ∈ F.supp}) : Set {e // e ∈ F.supp}).PairwiseDisjoint
      (fun e => chan e.1 (useDir s (F.ori e.1)) (f e)) := by
  intro e _ e' _ hne
  have hne' : ((e.1, useDir s (F.ori e.1), f e) : (H × H) × Bool × Fin T) ≠
      (e'.1, useDir s (F.ori e'.1), f e') := by
    intro h; exact hne (Subtype.ext (Prod.mk.inj h).1)
  exact chan_disjoint (t := (e.1, useDir s (F.ori e.1), f e))
    (t' := (e'.1, useDir s (F.ori e'.1), f e')) hne'

theorem net_singleton (a : XV H T × XV H T) (x : XV H T) :
    net ({a} : Finset (XV H T × XV H T)) x =
      (if a.2 = x then 1 else 0) - (if a.1 = x then 1 else 0) := by
  unfold net inDeg outDeg
  rw [filter_singleton, filter_singleton]
  split_ifs <;> simp

theorem net_chan_inr (e : H × H) (b : Bool) (i : Fin T) (p : Priv H T) :
    net (chan e b i) (Sum.inr p) = 0 := by
  rw [net_chan]; simp

theorem net_chan_inl (e : H × H) (b : Bool) (i : Fin T) (v : H) :
    net (chan e b i) (Sum.inl v) =
      oriSign b * ((if e.2 = v then 1 else 0) - (if e.1 = v then 1 else 0)) := by
  rw [net_chan]
  cases b <;> simp [chanEnd, chanStart, oriSign]

/-- **Face traversals are balanced.** -/
theorem facePiece_balanced (F : Face H) (hF : F.IsCirc) (s : Bool)
    (f : {e // e ∈ F.supp} → Fin T) : Cycles.Balanced (facePiece F s f) := by
  rw [balanced_iff_net]
  intro x
  unfold facePiece
  rw [net_biUnion _ _ (facePiece_pairwiseDisjoint F s f)]
  rcases x with v | p
  · simp only [net_chan_inl]
    rw [sum_attach F.supp (fun e => oriSign (useDir s (F.ori e)) *
      ((if e.2 = v then 1 else 0) - (if e.1 = v then 1 else 0)))]
    have key : ∀ e ∈ F.supp, oriSign (useDir s (F.ori e)) *
        ((if e.2 = v then (1:ℤ) else 0) - (if e.1 = v then 1 else 0)) =
        oriSign s * (oriSign (F.ori e) * (if e.2 = v then 1 else 0) -
          oriSign (F.ori e) * (if e.1 = v then 1 else 0)) := by
      intro e _
      cases s <;> cases F.ori e <;> simp [useDir, oriSign] <;> split_ifs <;> norm_num
    rw [sum_congr rfl key, ← mul_sum, sum_sub_distrib, hF v, sub_self, mul_zero]
  · simp [net_chan_inr]

/-- Class-2 pieces are balanced. -/
theorem pairPiece_balanced (e : H × H) (i j : Fin T) : Cycles.Balanced (pairPiece e i j) := by
  rw [balanced_iff_net]
  intro x
  have hd : Disjoint (chan e true i) (chan e false j) :=
    chan_disjoint (t := (e, true, i)) (t' := (e, false, j)) (by simp)
  unfold pairPiece
  rw [net_union_of_disjoint hd, net_chan, net_chan]
  simp [chanEnd, chanStart]

/-- Class-3 pieces are balanced. -/
theorem tailPiece_balanced (hT : 0 < T) (e : H × H) : Cycles.Balanced (tailPiece hT e) := by
  rw [balanced_iff_net]
  intro x
  have hd : Disjoint {liftArc H (Priv H T) e} (chan e false ⟨0, hT⟩) := by
    rw [disjoint_singleton_left]; exact liftArc_not_mem_chan _ _ _ _
  unfold tailPiece
  rw [insert_eq, net_union_of_disjoint hd, net_singleton, net_chan]
  change ((if Sum.inl e.2 = x then (1 : ℤ) else 0) -
      (if Sum.inl e.1 = x then 1 else 0)) +
    ((if Sum.inl e.1 = x then 1 else 0) - (if Sum.inl e.2 = x then 1 else 0)) = 0
  ring

theorem facePiece_card_le (F : Face H) (s : Bool) (f : {e // e ∈ F.supp} → Fin T) :
    (facePiece F s f).card ≤ 5 * F.supp.card := by
  unfold facePiece
  calc _ ≤ ∑ e ∈ F.supp.attach, (chan e.1 (useDir s (F.ori e.1)) (f e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ F.supp.attach, 5 := sum_le_sum (fun e _ => chan_card_le _ _ _)
    _ = 5 * F.supp.card := by rw [sum_const, card_attach, smul_eq_mul, mul_comm]

theorem pairPiece_card_le (e : H × H) (i j : Fin T) : (pairPiece e i j).card ≤ 10 := by
  unfold pairPiece
  calc _ ≤ (chan e true i).card + (chan e false j).card := card_union_le _ _
    _ ≤ 5 + 5 := add_le_add (chan_card_le _ _ _) (chan_card_le _ _ _)

theorem tailPiece_card_le (hT : 0 < T) (e : H × H) : (tailPiece hT e).card ≤ 6 := by
  unfold tailPiece
  calc _ ≤ (chan e false ⟨0, hT⟩).card + 1 := card_insert_le _ _
    _ ≤ 5 + 1 := by have := chan_card_le e false ⟨0, hT⟩; omega

theorem facePiece_nonempty (F : Face H) (hne : F.supp.Nonempty) (s : Bool)
    (f : {e // e ∈ F.supp} → Fin T) : (facePiece F s f).Nonempty := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨α, hα⟩ := chan_nonempty (T := T) e (useDir s (F.ori e)) (f ⟨e, he⟩)
  exact ⟨α, mem_facePiece.mpr ⟨e, he, hα⟩⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization
