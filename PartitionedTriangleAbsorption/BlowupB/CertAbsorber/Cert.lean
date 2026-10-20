/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Basic

/-! # Explicit signed certificates and the assignment of occurrences

A `SignedCert p F P` is an explicit finite list of `k` occurrences of allowed triangles on
`W`, each with a sign, whose integer boundary is exactly the indicator of `P`.  Occurrence
`i` has the three distinct corners `vtx i 0, vtx i 1, vtx i 2` (labels may coincide).

The *side* `(i, m)` of an occurrence is the edge opposite to the corner `m`, namely
`s(vtx i (m+1), vtx i (m+2))`.  Sides are physical copies: two occurrences may have the same
side edge, and are never merged.

`exists_matching` produces the assignment of occurrences: an injection `mu` from the negative
sides to the positive sides preserving the physical edge, such that the positive sides left
unmatched are in bijection with `P` through their edge.
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption

variable {W : Type*} [DecidableEq W] {t : ℕ}

/-- **Explicit signed certificate** of the edge set `P`. -/
structure SignedCert (p : W → Fin t) (F : Finset (Multiset (Fin t))) (P : Finset (Sym2 W)) where
  /-- number of occurrences -/
  k : ℕ
  /-- the corners of each occurrence -/
  vtx : Fin k → Fin 3 → W
  /-- the sign of each occurrence (`true` = `+1`, `false` = `-1`) -/
  pos : Fin k → Bool
  /-- the corners of an occurrence are distinct -/
  inj : ∀ i, Function.Injective (vtx i)
  /-- each occurrence is an allowed triangle -/
  typed : ∀ i, ({p (vtx i 0), p (vtx i 1), p (vtx i 2)} : Multiset (Fin t)) ∈ F
  /-- the integer boundary is exactly the indicator of `P` -/
  boundary : ∀ e : Sym2 W,
    ∑ i, (if pos i then (1 : ℤ) else -1) *
      (if e ∈ triEdges (univ.image (vtx i)) then 1 else 0) = if e ∈ P then 1 else 0

namespace SignedCert

variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable (c : SignedCert p F P)

/-- First endpoint of the side `s = (i, m)`. -/
def U (s : Fin c.k × Fin 3) : W := c.vtx s.1 (s.2 + 1)
/-- Second endpoint of the side `s = (i, m)`. -/
def V (s : Fin c.k × Fin 3) : W := c.vtx s.1 (s.2 + 2)
/-- The physical edge of the side `s = (i, m)` (opposite to corner `m`). -/
def side (s : Fin c.k × Fin 3) : Sym2 W := s(c.U s, c.V s)

/-- Number of occurrences containing the vertex `x`. -/
def occCount (x : W) : ℕ := (univ.filter fun i => x ∈ univ.image (c.vtx i)).card

/-- Number of negative occurrences. -/
def negCount : ℕ := (univ.filter fun i => c.pos i = false).card

lemma U_ne_V (s : Fin c.k × Fin 3) : c.U s ≠ c.V s := by
  intro h
  have := c.inj s.1 h
  revert this; generalize s.2 = m; revert m; decide

lemma side_injective (i : Fin c.k) : Function.Injective (fun m => c.side (i, m)) := by
  intro m m' h
  simp only [side, U, V, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' := c.inj i h1
    clear h1 h2
    revert h1'; revert m m'; decide
  · have h1' := c.inj i h1
    have h2' := c.inj i h2
    clear h1 h2
    revert h1' h2'; revert m m'; decide

lemma mem_triEdges_iff (i : Fin c.k) (e : Sym2 W) :
    e ∈ triEdges (univ.image (c.vtx i)) ↔ ∃ m, c.side (i, m) = e := by
  have himg : (univ.image (c.vtx i)) = {c.vtx i 0, c.vtx i 1, c.vtx i 2} := by
    ext x; simp [Fin.exists_fin_succ, eq_comm]
  have h01 : c.vtx i 0 ≠ c.vtx i 1 := fun h => by simpa using c.inj i h
  have h02 : c.vtx i 0 ≠ c.vtx i 2 := fun h => by simpa using c.inj i h
  have h12 : c.vtx i 1 ≠ c.vtx i 2 := fun h => by simpa using c.inj i h
  rw [himg, triEdges_three h01 h02 h12]
  simp only [mem_insert, mem_singleton, Fin.exists_fin_succ, side, U, V]
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.exists_iff,
    or_false]
  have e1 : (0 : Fin 3) + 1 = 1 := rfl
  have e2 : (0 : Fin 3) + 2 = 2 := rfl
  have e3 : (1 : Fin 3) + 1 = 2 := rfl
  have e4 : (1 : Fin 3) + 2 = 0 := rfl
  have e5 : (2 : Fin 3) + 1 = 0 := rfl
  have e6 : (2 : Fin 3) + 2 = 1 := rfl
  rw [e1, e2, e3, e4, e5, e6]
  constructor <;> rintro (h | h | h) <;> subst h <;> simp [Sym2.eq_swap]

/-- The boundary indicator of one occurrence counts its sides equal to `e`. -/
lemma indicator_eq_card (i : Fin c.k) (e : Sym2 W) :
    (if e ∈ triEdges (univ.image (c.vtx i)) then (1 : ℤ) else 0) =
      ((univ : Finset (Fin 3)).filter fun m => c.side (i, m) = e).card := by
  have hle : ((univ : Finset (Fin 3)).filter fun m => c.side (i, m) = e).card ≤ 1 := by
    refine card_le_one.mpr fun m hm m' hm' => ?_
    simp only [mem_filter] at hm hm'
    exact c.side_injective i (hm.2.trans hm'.2.symm)
  split_ifs with h
  · obtain ⟨m, hm⟩ := (c.mem_triEdges_iff i e).mp h
    have hpos : 0 < ((univ : Finset (Fin 3)).filter fun m => c.side (i, m) = e).card :=
      card_pos.mpr ⟨m, by simp [hm]⟩
    omega
  · have h0 : ((univ : Finset (Fin 3)).filter fun m => c.side (i, m) = e) = ∅ := by
      refine filter_eq_empty_iff.mpr fun m _ hm => h ((c.mem_triEdges_iff i e).mpr ⟨m, hm⟩)
    simp [h0]

/-- Positive sides with edge `e`. -/
def posSides (e : Sym2 W) : Finset (Fin c.k × Fin 3) :=
  univ.filter fun s => c.pos s.1 = true ∧ c.side s = e
/-- Negative sides with edge `e`. -/
def negSides (e : Sym2 W) : Finset (Fin c.k × Fin 3) :=
  univ.filter fun s => c.pos s.1 = false ∧ c.side s = e

private lemma card_sides (b : Bool) (e : Sym2 W) :
    ((univ.filter fun s : Fin c.k × Fin 3 => c.pos s.1 = b ∧ c.side s = e).card : ℤ) =
      ∑ i, if c.pos i = b then
        (((univ : Finset (Fin 3)).filter fun m => c.side (i, m) = e).card : ℤ) else 0 := by
  rw [card_filter, Nat.cast_sum, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with hb
  · rw [card_filter, Nat.cast_sum]
    refine sum_congr rfl fun m _ => ?_
    simp [hb]
  · simp [hb]

/-- **Boundary equality, side by side**: for each physical edge, the positive sides exceed
the negative sides by exactly one when the edge is in `P`, and by zero otherwise. -/
theorem card_posSides (e : Sym2 W) :
    (c.posSides e).card = (c.negSides e).card + if e ∈ P then 1 else 0 := by
  have hb := c.boundary e
  have hp := c.card_sides true e
  have hn := c.card_sides false e
  have key : ((c.posSides e).card : ℤ) - (c.negSides e).card = if e ∈ P then 1 else 0 := by
    rw [← hb]
    unfold posSides negSides
    rw [hp, hn, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [c.indicator_eq_card i e]
    cases c.pos i <;> simp
  split_ifs at key ⊢ <;> omega

end SignedCert

/-- **Assignment of occurrences.**  `mu` sends every negative side to a positive side with the
same physical edge, injectively.  (On positive sides `mu` is an irrelevant filler that only
satisfies `mu s ≠ s`.) -/
structure Matching {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
    (c : SignedCert p F P) where
  mu : Fin c.k × Fin 3 → Fin c.k × Fin 3
  ne : ∀ s, mu s ≠ s
  pos_mu : ∀ s, c.pos s.1 = false → c.pos (mu s).1 = true
  side_mu : ∀ s, c.pos s.1 = false → c.side (mu s) = c.side s
  inj : ∀ s s', c.pos s.1 = false → c.pos s'.1 = false → mu s = mu s' → s = s'

namespace Matching

variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable {c : SignedCert p F P} (M : Matching c)

/-- A positive side not used by any negative side. -/
abbrev Unmatched (s : Fin c.k × Fin 3) : Prop :=
  c.pos s.1 = true ∧ ∀ s', c.pos s'.1 = false → M.mu s' ≠ s

/-- Unmatched positive sides with edge `e`. -/
def unmatchedSides (e : Sym2 W) : Finset (Fin c.k × Fin 3) :=
  univ.filter fun s => M.Unmatched s ∧ c.side s = e

theorem card_unmatchedSides (e : Sym2 W) :
    (M.unmatchedSides e).card = if e ∈ P then 1 else 0 := by
  have hsplit : c.posSides e = (c.negSides e).image M.mu ∪ M.unmatchedSides e := by
    ext s
    simp only [SignedCert.posSides, SignedCert.negSides, unmatchedSides, Unmatched, mem_filter,
      mem_univ, true_and, mem_union, mem_image]
    constructor
    · rintro ⟨hp, hs⟩
      by_cases h : ∃ s', c.pos s'.1 = false ∧ M.mu s' = s
      · obtain ⟨s', hs', rfl⟩ := h
        exact Or.inl ⟨s', ⟨hs', (M.side_mu s' hs').symm.trans hs⟩, rfl⟩
      · push_neg at h
        exact Or.inr ⟨⟨hp, h⟩, hs⟩
    · rintro (⟨s', ⟨hs', he⟩, rfl⟩ | ⟨⟨hp, _⟩, hs⟩)
      · exact ⟨M.pos_mu s' hs', (M.side_mu s' hs').trans he⟩
      · exact ⟨hp, hs⟩
  have hdisj : Disjoint ((c.negSides e).image M.mu) (M.unmatchedSides e) := by
    rw [disjoint_left]
    intro s hs hs'
    obtain ⟨s', hs'n, rfl⟩ := mem_image.mp hs
    simp only [unmatchedSides, Unmatched, mem_filter, SignedCert.negSides] at hs' hs'n
    exact hs'.2.1.2 s' hs'n.2.1 rfl
  have hinj : ((c.negSides e).image M.mu).card = (c.negSides e).card := by
    refine card_image_of_injOn fun s hs s' hs' h => ?_
    simp only [SignedCert.negSides, coe_filter, Set.mem_setOf_eq] at hs hs'
    exact M.inj s s' hs.2.1 hs'.2.1 h
  have h1 := c.card_posSides e
  rw [hsplit, card_union_of_disjoint hdisj, hinj] at h1
  omega

theorem unmatched_side_mem {s : Fin c.k × Fin 3} (hs : M.Unmatched s) : c.side s ∈ P := by
  by_contra h
  have h0 := M.card_unmatchedSides (c.side s)
  rw [if_neg h, card_eq_zero] at h0
  have : s ∈ M.unmatchedSides (c.side s) := mem_filter.mpr ⟨mem_univ _, hs, rfl⟩
  simp [h0] at this

theorem unmatched_inj {s s' : Fin c.k × Fin 3} (hs : M.Unmatched s) (hs' : M.Unmatched s')
    (h : c.side s = c.side s') : s = s' := by
  have h1 := M.card_unmatchedSides (c.side s)
  have hle : (M.unmatchedSides (c.side s)).card ≤ 1 := by rw [h1]; split_ifs <;> omega
  exact card_le_one.mp hle s (mem_filter.mpr ⟨mem_univ _, hs, rfl⟩) s'
    (mem_filter.mpr ⟨mem_univ _, hs', h.symm⟩)

theorem unmatched_surj {e : Sym2 W} (he : e ∈ P) : ∃ s, M.Unmatched s ∧ c.side s = e := by
  have h1 := M.card_unmatchedSides e
  rw [if_pos he] at h1
  obtain ⟨s, hs⟩ := card_pos.mp (by omega : 0 < (M.unmatchedSides e).card)
  simp only [unmatchedSides, mem_filter] at hs
  exact ⟨s, hs.2⟩

end Matching

/-- **Existence of the assignment of occurrences** for every explicit certificate. -/
theorem exists_matching {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
    (c : SignedCert p F P) : Nonempty (Matching c) := by
  classical
  let f : {s : Fin c.k × Fin 3 // c.pos s.1 = false} → Sym2 W := fun s => c.side s.1
  let g : {s : Fin c.k × Fin 3 // c.pos s.1 = true} → Sym2 W := fun s => c.side s.1
  have hcard : ∀ e, Fintype.card {a // f a = e} ≤ Fintype.card {b // g b = e} := by
    intro e
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun s : Fin c.k × Fin 3 => c.pos s.1 = false) (fun s => c.side s = e)),
      Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun s : Fin c.k × Fin 3 => c.pos s.1 = true) (fun s => c.side s = e)),
      Fintype.card_subtype, Fintype.card_subtype]
    have := c.card_posSides e
    unfold SignedCert.posSides SignedCert.negSides at this
    omega
  obtain ⟨μ, hμ, hμs⟩ := exists_fiber_matching f g hcard
  refine ⟨{
    mu := fun s => if h : c.pos s.1 = false then (μ ⟨s, h⟩).1 else (s.1, s.2 + 1)
    ne := ?_, pos_mu := ?_, side_mu := ?_, inj := ?_ }⟩
  · intro s
    by_cases h : c.pos s.1 = false
    · rw [dif_pos h]
      intro he
      have := (μ ⟨s, h⟩).2
      rw [he, h] at this
      exact Bool.false_ne_true this
    · rw [dif_neg h]
      intro he
      have h2 : s.2 + 1 = s.2 := congrArg Prod.snd he
      revert h2; generalize s.2 = m; revert m; decide
  · intro s h
    rw [dif_pos h]
    exact (μ ⟨s, h⟩).2
  · intro s h
    rw [dif_pos h]
    exact hμs ⟨s, h⟩
  · intro s s' h h' he
    rw [dif_pos h, dif_pos h'] at he
    exact congrArg Subtype.val (hμ (Subtype.ext he))

end PaperII.CertAbsorber
