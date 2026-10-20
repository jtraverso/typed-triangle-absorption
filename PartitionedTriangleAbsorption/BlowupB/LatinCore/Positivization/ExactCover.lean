/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.Pieces

@[expose] public section

/-!
# Physical positivization with all unused channels covered (§7)

Fix, **before the demand**, a cyclically tripartite reference digraph `Q` on `H`, a digraph
`D ⊆ Q`, a family of faces `face : Φ → Face H` (signed circulations supported in `Q`) and the
channel multiplicity `T ≥ 1`.  The reserve `reserve Q T` consists of `T` positive and `T`
negative private channels over every arc of `Q`, and the catalogue `catalogue face Q D T`
consists of

1. every traversal of every face, with both signs and every choice of one channel per arc;
2. every pair (positive channel, negative channel) over an arc of `Q`;
3. every base arc `e ∈ D` together with its negative channel number `0`.

`positivization_exact_cover` : for **every** `L ⊆ D` and every integer filling `a : Φ → ℤ` of
`χ_L` (i.e. `∑ φ, a φ · face φ (e) = χ_L(e)` on `Q`) with per-arc load
`∑ φ, |a φ| |face φ (e)| ≤ T`, some pairwise disjoint subfamily of the catalogue has union
exactly `reserve Q T ∪ L`.  Every channel is used exactly once: by a face occurrence, by the
class-3 piece of an arc of `L`, or by a class-2 pair.

The proof is the bookkeeping of §7: with `p_e`, `n_e` the positive / negative uses,
`p_e − n_e = χ_L(e)` and `p_e ≤ T`; positive occurrences get indices `0, …, p_e − 1`,
negative occurrences get `χ_L(e), …, p_e − 1`, the class-3 piece takes negative index `0`
when `e ∈ L`, and the indices `p_e, …, T − 1` of both signs are paired by class-2 pieces.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization

open Finset PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

variable {H : Type} [Fintype H] [DecidableEq H] {T : ℕ}
variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]

/-! ### The reserve and the catalogue (independent of `L`) -/

/-- The reserve: all `2T` channels over every arc of `Q`. -/
def reserve (Q : Finset (H × H)) (T : ℕ) : Finset (XV H T × XV H T) :=
  (Q ×ˢ (univ : Finset (Bool × Fin T))).biUnion (fun t => chan t.1 t.2.1 t.2.2)

/-- Catalogue class 1: all face traversals. -/
def faceLib (face : Φ → Face H) (T : ℕ) : Finset (Finset (XV H T × XV H T)) :=
  (univ : Finset (Σ φ : Φ, Bool × ({e // e ∈ (face φ).supp} → Fin T))).image
    (fun x => facePiece (face x.1) x.2.1 x.2.2)

/-- Catalogue class 2: all pairs of a positive and a negative channel of the same arc. -/
def pairLib (Q : Finset (H × H)) (T : ℕ) : Finset (Finset (XV H T × XV H T)) :=
  (Q ×ˢ (univ : Finset (Fin T × Fin T))).image (fun x => pairPiece x.1 x.2.1 x.2.2)

/-- Catalogue class 3: base arc plus negative channel `0`. -/
def tailLib (D : Finset (H × H)) (hT : 0 < T) : Finset (Finset (XV H T × XV H T)) :=
  D.image (tailPiece hT)

/-- The fixed catalogue. -/
def catalogue (face : Φ → Face H) (Q D : Finset (H × H)) (hT : 0 < T) :
    Finset (Finset (XV H T × XV H T)) :=
  faceLib face T ∪ pairLib Q T ∪ tailLib D hT

/-! ### Occurrences of a filling -/

/-- Occurrences: `|a φ|` copies of each face `φ`. -/
abbrev Occ (a : Φ → ℤ) := Σ φ : Φ, Fin (a φ).natAbs

/-- The sign of the copies of `φ`. -/
def occSign (a : Φ → ℤ) (φ : Φ) : Bool := decide (0 < a φ)

/-- Occurrences using a channel of sign `b` over the arc `e`. -/
def OccSet (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) (b : Bool) : Finset (Occ a) :=
  (univ : Finset Φ).sigma (fun φ =>
    if e ∈ (face φ).supp ∧ useDir (occSign a φ) ((face φ).ori e) = b then univ else ∅)

omit [Fintype H] [DecidableEq Φ] in
theorem mem_OccSet {face : Φ → Face H} {a : Φ → ℤ} {e : H × H} {b : Bool} {o : Occ a} :
    o ∈ OccSet face a e b ↔
      e ∈ (face o.1).supp ∧ useDir (occSign a o.1) ((face o.1).ori e) = b := by
  unfold OccSet
  rw [mem_sigma]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (Finset.notMem_empty _)
  · intro h
    exact ⟨mem_univ _, by rw [if_pos h]; exact mem_univ _⟩

omit [Fintype H] [DecidableEq Φ] in
theorem card_OccSet (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) (b : Bool) :
    (OccSet face a e b).card =
      ∑ φ, if e ∈ (face φ).supp ∧ useDir (occSign a φ) ((face φ).ori e) = b
        then (a φ).natAbs else 0 := by
  unfold OccSet
  rw [card_sigma]
  refine sum_congr rfl (fun φ _ => ?_)
  split_ifs <;> simp

/-- Number of positive uses of `e`. -/
def pc (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) : ℕ := (OccSet face a e true).card

/-- Number of negative uses of `e`. -/
def nc (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) : ℕ := (OccSet face a e false).card

/-- `χ_L(e)`. -/
def chi (L : Finset (H × H)) (e : H × H) : ℕ := if e ∈ L then 1 else 0

omit [Fintype H] [DecidableEq Φ] in
theorem pc_sub_nc (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) :
    (pc face a e : ℤ) - nc face a e = ∑ φ, a φ * (face φ).val e := by
  unfold pc nc
  rw [card_OccSet, card_OccSet]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun φ _ => ?_)
  unfold Face.val occSign
  by_cases he : e ∈ (face φ).supp
  · simp only [he, true_and, if_true]
    rcases lt_trichotomy (a φ) 0 with h | h | h
    · have hn : ((a φ).natAbs : ℤ) = - a φ := by omega
      cases hori : (face φ).ori e <;>
        simp [useDir, oriSign, not_lt.mpr h.le, abs_of_neg h]
    · simp [h]
    · have hn : ((a φ).natAbs : ℤ) = a φ := by omega
      cases hori : (face φ).ori e <;> simp [useDir, oriSign, h, h.le]
  · simp [he]

omit [Fintype H] [DecidableEq Φ] in
theorem pc_add_nc (face : Φ → Face H) (a : Φ → ℤ) (e : H × H) :
    (pc face a e : ℤ) + nc face a e = ∑ φ, |a φ| * |(face φ).val e| := by
  unfold pc nc
  rw [card_OccSet, card_OccSet]
  push_cast
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun φ _ => ?_)
  unfold Face.val
  by_cases he : e ∈ (face φ).supp
  · simp only [he, true_and, if_true]
    cases useDir (occSign a φ) ((face φ).ori e) <;>
      cases (face φ).ori e <;> simp [oriSign]
  · simp [he]

/-! ### Index assignment and ownership -/

/-- Index of the channel of sign `b` over `e` used by the occurrence `o`. -/
noncomputable def idx (face : Φ → Face H) (a : Φ → ℤ) (L : Finset (H × H)) (e : H × H)
    (b : Bool) (o : Occ a) : ℕ :=
  if h : o ∈ OccSet face a e b then
    ((OccSet face a e b).equivFin ⟨o, h⟩ : ℕ) + (if b then 0 else chi L e)
  else 0

/-- Channel choice of an occurrence. -/
noncomputable def occChoice (face : Φ → Face H) (a : Φ → ℤ) (L : Finset (H × H)) (hT : 0 < T)
    (o : Occ a) : {e // e ∈ (face o.1).supp} → Fin T := fun e =>
  ⟨idx face a L e.1 (useDir (occSign a o.1) ((face o.1).ori e.1)) o % T, Nat.mod_lt _ hT⟩

/-- Piece labels: face occurrences, class-3 arcs, class-2 (arc, index). -/
abbrev Label (a : Φ → ℤ) (H : Type) (T : ℕ) := Occ a ⊕ (H × H) ⊕ ((H × H) × Fin T)

/-- The piece with a given label. -/
noncomputable def piece (face : Φ → Face H) (a : Φ → ℤ) (L : Finset (H × H)) (hT : 0 < T) :
    Label a H T → Finset (XV H T × XV H T)
  | Sum.inl o => facePiece (face o.1) (occSign a o.1) (occChoice face a L hT o)
  | Sum.inr (Sum.inl e) => tailPiece hT e
  | Sum.inr (Sum.inr x) => pairPiece x.1 x.2 x.2

/-- The owner of the channel `t = (e, b, i)`. -/
noncomputable def owner (face : Φ → Face H) (a : Φ → ℤ) (L : Finset (H × H))
    (t : (H × H) × Bool × Fin T) : Label a H T :=
  if t.2.1 then
    if h : t.2.2.val < pc face a t.1 then
      Sum.inl ((OccSet face a t.1 true).equivFin.symm ⟨t.2.2.val, h⟩).1
    else Sum.inr (Sum.inr (t.1, t.2.2))
  else
    if t.2.2.val < chi L t.1 then Sum.inr (Sum.inl t.1)
    else if h : t.2.2.val - chi L t.1 < nc face a t.1 then
      Sum.inl ((OccSet face a t.1 false).equivFin.symm ⟨t.2.2.val - chi L t.1, h⟩).1
    else Sum.inr (Sum.inr (t.1, t.2.2))

/-- Labels actually used for a given `L`. -/
def Valid (face : Φ → Face H) (a : Φ → ℤ) (L Q : Finset (H × H)) : Label a H T → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl e) => e ∈ L
  | Sum.inr (Sum.inr x) => x.1 ∈ Q ∧ pc face a x.1 ≤ x.2.val

section Hyp

variable {face : Φ → Face H} {a : Φ → ℤ} {L Q : Finset (H × H)} (hT : 0 < T)

/-- The arithmetic consequences of the filling at an arc of `Q`. -/
structure ArcFacts (face : Φ → Face H) (a : Φ → ℤ) (L : Finset (H × H)) (T : ℕ)
    (e : H × H) : Prop where
  pc_eq : pc face a e = nc face a e + chi L e
  pc_le : pc face a e ≤ T

omit [Fintype H] [DecidableEq Φ] in
theorem arcFacts_of_filling (e : H × H)
    (hfill : ∑ φ, a φ * (face φ).val e = if e ∈ L then 1 else 0)
    (hload : ∑ φ, |a φ| * |(face φ).val e| ≤ T) : ArcFacts face a L T e := by
  have h1 := pc_sub_nc face a e
  have h2 := pc_add_nc face a e
  rw [hfill] at h1
  rw [← h2] at hload
  constructor
  · unfold chi; split_ifs at h1 ⊢ <;> omega
  · omega

omit [Fintype H] in
theorem idx_lt (e : H × H) (hf : ArcFacts face a L T e) (b : Bool) (o : Occ a)
    (ho : o ∈ OccSet face a e b) : idx face a L e b o < T := by
  have hlt := ((OccSet face a e b).equivFin ⟨o, ho⟩).isLt
  unfold idx; rw [dif_pos ho]
  have := hf.pc_eq; have := hf.pc_le
  cases b
  · simp only [Bool.false_eq_true, if_false]; unfold nc at *; unfold pc at *; omega
  · simp only [if_true]; unfold pc at *; omega

omit [Fintype H] in
/-- (O1) An occurrence owns the channels it uses. -/
theorem owner_idx (e : H × H) (hf : ArcFacts face a L T e) (b : Bool) (o : Occ a)
    (ho : o ∈ OccSet face a e b) :
    owner face a L (e, b, (⟨idx face a L e b o % T, Nat.mod_lt _ hT⟩ : Fin T)) = Sum.inl o := by
  have hlt := idx_lt e hf b o ho
  have hmod : idx face a L e b o % T = idx face a L e b o := Nat.mod_eq_of_lt hlt
  have hk := ((OccSet face a e b).equivFin ⟨o, ho⟩).isLt
  have hpe := hf.pc_eq
  have hfin : (⟨idx face a L e b o % T, Nat.mod_lt _ hT⟩ : Fin T) = ⟨idx face a L e b o, hlt⟩ :=
    Fin.ext hmod
  rw [hfin]
  unfold owner
  dsimp only
  cases b
  · have hidx : idx face a L e false o =
        ((OccSet face a e false).equivFin ⟨o, ho⟩ : ℕ) + chi L e := by
      unfold idx; rw [dif_pos ho]; simp
    have h1 : ¬ (idx face a L e false o < chi L e) := by omega
    have h2 : idx face a L e false o - chi L e < nc face a e := by unfold nc; omega
    simp only [Bool.false_eq_true, if_false, if_neg h1, dif_pos h2]
    congr 1
    have : (⟨idx face a L e false o - chi L e, h2⟩ : Fin (OccSet face a e false).card) =
        (OccSet face a e false).equivFin ⟨o, ho⟩ := Fin.ext (by simp only; omega)
    rw [this, Equiv.symm_apply_apply]
  · have hidx : idx face a L e true o = ((OccSet face a e true).equivFin ⟨o, ho⟩ : ℕ) := by
      unfold idx; rw [dif_pos ho]; simp
    have h2 : idx face a L e true o < pc face a e := by unfold pc; omega
    simp only [if_true, dif_pos h2]
    congr 1
    have : (⟨idx face a L e true o, h2⟩ : Fin (OccSet face a e true).card) =
        (OccSet face a e true).equivFin ⟨o, ho⟩ := Fin.ext (by simp only; omega)
    rw [this, Equiv.symm_apply_apply]

omit [Fintype H] in
/-- (O2) Channels owned by an occurrence are the ones it uses. -/
theorem owner_eq_inl (t : (H × H) × Bool × Fin T) (o : Occ a) (h : owner face a L t = Sum.inl o) :
    o ∈ OccSet face a t.1 t.2.1 ∧
      (⟨idx face a L t.1 t.2.1 o % T, Nat.mod_lt _ hT⟩ : Fin T) = t.2.2 := by
  obtain ⟨e, b, i⟩ := t
  unfold owner at h
  dsimp only at h ⊢
  cases b
  · simp only [Bool.false_eq_true, if_false] at h
    split_ifs at h with h1 h2
    obtain rfl := Sum.inl.inj h
    have hq := ((OccSet face a e false).equivFin.symm ⟨i.val - chi L e, h2⟩).2
    refine ⟨hq, Fin.ext ?_⟩
    have : idx face a L e false
        ((OccSet face a e false).equivFin.symm ⟨i.val - chi L e, h2⟩).1 = i.val := by
      unfold idx; rw [dif_pos hq]; simp; omega
    simp only [this]; exact Nat.mod_eq_of_lt i.isLt
  · simp only [if_true] at h
    split_ifs at h with h1
    obtain rfl := Sum.inl.inj h
    have hq := ((OccSet face a e true).equivFin.symm ⟨i.val, h1⟩).2
    refine ⟨hq, Fin.ext ?_⟩
    have : idx face a L e true
        ((OccSet face a e true).equivFin.symm ⟨i.val, h1⟩).1 = i.val := by
      unfold idx; rw [dif_pos hq]; simp
    simp only [this]; exact Nat.mod_eq_of_lt i.isLt

omit [Fintype H] [DecidableEq Φ] in
/-- (O3) Only the negative channel `0` of an arc of `L` is owned by its class-3 piece. -/
theorem owner_eq_tail (t : (H × H) × Bool × Fin T) (e : H × H)
    (h : owner face a L t = Sum.inr (Sum.inl e)) :
    t.1 = e ∧ t.2.1 = false ∧ t.2.2.val < chi L e := by
  obtain ⟨e', b, i⟩ := t
  unfold owner at h
  dsimp only at h ⊢
  cases b
  · simp only [Bool.false_eq_true, if_false] at h
    split_ifs at h with h1 h2
    all_goals try (simp at h; done)
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h, rfl, h ▸ h1⟩
  · simp only [if_true] at h
    split_ifs at h
    simp at h

omit [Fintype H] [DecidableEq Φ] in
theorem owner_tail (e : H × H) (he : e ∈ L) :
    owner face a L (e, false, (⟨0, hT⟩ : Fin T)) = Sum.inr (Sum.inl e) := by
  unfold owner
  simp [chi, he]

omit [Fintype H] [DecidableEq Φ] in
/-- (O4) Channels owned by a class-2 label. -/
theorem owner_eq_pair (t : (H × H) × Bool × Fin T) (x : (H × H) × Fin T)
    (h : owner face a L t = Sum.inr (Sum.inr x)) : t.1 = x.1 ∧ t.2.2 = x.2 := by
  obtain ⟨e', b, i⟩ := t
  unfold owner at h
  dsimp only at h ⊢
  cases b
  · simp only [Bool.false_eq_true, if_false] at h
    split_ifs at h with h1 h2
    all_goals try (simp at h; done)
    simp only [Sum.inr.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  · simp only [if_true] at h
    split_ifs at h with h1
    simp only [Sum.inr.injEq] at h
    subst h; exact ⟨rfl, rfl⟩

omit [Fintype H] [DecidableEq Φ] in
theorem owner_pair (e : H × H) (hf : ArcFacts face a L T e) (b : Bool) (i : Fin T)
    (hi : pc face a e ≤ i.val) : owner face a L (e, b, i) = Sum.inr (Sum.inr (e, i)) := by
  have hpe := hf.pc_eq
  unfold owner
  dsimp only
  cases b
  · have h1 : ¬ i.val < chi L e := by omega
    have h2 : ¬ i.val - chi L e < nc face a e := by omega
    simp only [Bool.false_eq_true, if_false, if_neg h1, dif_neg h2]
  · have h1 : ¬ i.val < pc face a e := by omega
    simp only [if_true, dif_neg h1]

omit [Fintype H] [DecidableEq Φ] in
/-- (O5) Owners are valid labels. -/
theorem valid_owner (t : (H × H) × Bool × Fin T) (hQ : t.1 ∈ Q) (hf : ArcFacts face a L T t.1) :
    Valid face a L Q (owner face a L t) := by
  obtain ⟨e, b, i⟩ := t
  have hpe := hf.pc_eq
  dsimp only at hQ hpe
  unfold owner
  dsimp only
  cases b
  · simp only [Bool.false_eq_true, if_false]
    split_ifs with h1 h2
    · show e ∈ L
      unfold chi at h1; split_ifs at h1 with hL
      · exact hL
      · omega
    · trivial
    · exact ⟨hQ, by dsimp only; omega⟩
  · simp only [if_true]
    split_ifs with h1
    · trivial
    · exact ⟨hQ, by dsimp only; omega⟩

omit [Fintype H] in
/-- **Membership in a piece**: an arc lies in the piece with a valid label `ℓ` iff it is the
lifted arc of `ℓ` (class 3) or lies in a channel owned by `ℓ`. -/
theorem mem_piece (hLQ : L ⊆ Q) (hsupp : ∀ φ, (face φ).supp ⊆ Q)
    (hf : ∀ e ∈ Q, ArcFacts face a L T e) (ℓ : Label a H T) (hℓ : Valid face a L Q ℓ)
    (α : XV H T × XV H T) :
    α ∈ piece face a L hT ℓ ↔
      (∃ e ∈ L, α = liftArc H (Priv H T) e ∧ ℓ = Sum.inr (Sum.inl e)) ∨
        ∃ t : (H × H) × Bool × Fin T, t.1 ∈ Q ∧ α ∈ chan t.1 t.2.1 t.2.2 ∧
          owner face a L t = ℓ := by
  rcases ℓ with o | e | ⟨e, i⟩
  · show α ∈ facePiece _ _ _ ↔ _
    rw [mem_facePiece]
    constructor
    · rintro ⟨e, he, hα⟩
      right
      have ho : o ∈ OccSet face a e (useDir (occSign a o.1) ((face o.1).ori e)) :=
        mem_OccSet.mpr ⟨he, rfl⟩
      exact ⟨(e, useDir (occSign a o.1) ((face o.1).ori e), occChoice face a L hT o ⟨e, he⟩),
        hsupp _ he, hα, owner_idx hT e (hf e (hsupp _ he)) _ o ho⟩
    · rintro (⟨e, -, -, h⟩ | ⟨t, -, hα, ht⟩)
      · cases h
      · obtain ⟨ho, hidx⟩ := owner_eq_inl hT t o ht
        obtain ⟨he, hdir⟩ := mem_OccSet.mp ho
        refine ⟨t.1, he, ?_⟩
        have hc : occChoice face a L hT o ⟨t.1, he⟩ = t.2.2 := by
          unfold occChoice; simp only [hdir]; exact hidx
        rw [hdir, hc]; exact hα
  · change e ∈ L at hℓ
    show α ∈ tailPiece hT e ↔ _
    simp only [tailPiece, mem_insert]
    constructor
    · rintro (rfl | hα)
      · left; exact ⟨e, hℓ, rfl, rfl⟩
      · right; exact ⟨(e, false, ⟨0, hT⟩), hLQ hℓ, hα, owner_tail hT e hℓ⟩
    · rintro (⟨e', -, rfl, h⟩ | ⟨t, -, hα, ht⟩)
      · left; cases h; rfl
      · right
        obtain ⟨h1, h2, h3⟩ := owner_eq_tail t e ht
        have hchi : chi L e = 1 := by simp [chi, hℓ]
        obtain ⟨te, tb, ti⟩ := t
        simp only at h1 h2 h3
        subst h1; subst h2
        have : ti = ⟨0, hT⟩ := Fin.ext (by simp only; omega)
        subst this; exact hα
  · change e ∈ Q ∧ pc face a e ≤ i.val at hℓ
    show α ∈ pairPiece e i i ↔ _
    simp only [pairPiece, mem_union]
    constructor
    · rintro (hα | hα)
      · right; exact ⟨(e, true, i), hℓ.1, hα, owner_pair e (hf e hℓ.1) true i hℓ.2⟩
      · right; exact ⟨(e, false, i), hℓ.1, hα, owner_pair e (hf e hℓ.1) false i hℓ.2⟩
    · rintro (⟨e', -, -, h⟩ | ⟨t, -, hα, ht⟩)
      · cases h
      · obtain ⟨h1, h2⟩ := owner_eq_pair t (e, i) ht
        obtain ⟨te, tb, ti⟩ := t
        simp only at h1 h2
        subst h1; subst h2
        cases tb
        · right; exact hα
        · left; exact hα

end Hyp

/-! ### The exact cover -/

/-- **Physical positivization with every channel covered (§7).**  The reserve and the catalogue
depend only on `Q`, `D`, the faces and `T`; for every `L ⊆ D` and every integer face filling of
`χ_L` with per-arc load `≤ T`, a pairwise disjoint subfamily of the catalogue covers exactly
`reserve Q T ∪ L`. -/
theorem positivization_exact_cover (Q D : Finset (H × H)) (hDQ : D ⊆ Q) (hT : 0 < T)
    (face : Φ → Face H) (hsupp : ∀ φ, (face φ).supp ⊆ Q)
    (L : Finset (H × H)) (hLD : L ⊆ D) (a : Φ → ℤ)
    (hfill : ∀ e ∈ Q, ∑ φ, a φ * (face φ).val e = if e ∈ L then 1 else 0)
    (hload : ∀ e ∈ Q, ∑ φ, |a φ| * |(face φ).val e| ≤ T) :
    ∃ P ⊆ catalogue face Q D hT, (P : Set (Finset (XV H T × XV H T))).PairwiseDisjoint id ∧
      P.biUnion id = reserve Q T ∪ L.map (liftArc H (Priv H T)) := by
  classical
  have hLQ : L ⊆ Q := hLD.trans hDQ
  have hf : ∀ e ∈ Q, ArcFacts face a L T e :=
    fun e he => arcFacts_of_filling e (hfill e he) (hload e he)
  let Λ : Finset (Label a H T) := univ.filter (fun ℓ => Valid face a L Q ℓ)
  have hΛ : ∀ ℓ, ℓ ∈ Λ ↔ Valid face a L Q ℓ := by
    intro ℓ; simp [Λ]
  refine ⟨Λ.image (piece face a L hT), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hp
    rw [hΛ] at hℓ
    rcases ℓ with o | e | ⟨e, i⟩
    · apply mem_union_left; apply mem_union_left
      exact mem_image.mpr ⟨⟨o.1, occSign a o.1, occChoice face a L hT o⟩, mem_univ _, rfl⟩
    · apply mem_union_right
      exact mem_image.mpr ⟨e, hLD hℓ, rfl⟩
    · apply mem_union_left; apply mem_union_right
      exact mem_image.mpr ⟨(e, i, i), mem_product.mpr ⟨hℓ.1, mem_univ _⟩, rfl⟩
  · intro p hp p' hp' hne
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hp
    obtain ⟨ℓ', hℓ', rfl⟩ := mem_image.mp hp'
    rw [hΛ] at hℓ hℓ'
    have hll : ℓ ≠ ℓ' := fun h => hne (h ▸ rfl)
    simp only [Function.onFun, id]
    rw [Finset.disjoint_left]
    intro α h1 h2
    rw [mem_piece hT hLQ hsupp hf ℓ hℓ] at h1
    rw [mem_piece hT hLQ hsupp hf ℓ' hℓ'] at h2
    apply hll
    rcases h1 with ⟨e, -, rfl, rfl⟩ | ⟨t, -, ht, rfl⟩ <;>
      rcases h2 with ⟨e', -, h, rfl⟩ | ⟨t', -, ht', rfl⟩
    · rw [(liftArc H (Priv H T)).injective h]
    · exact absurd ht' (liftArc_not_mem_chan _ _ _ _)
    · rw [h] at ht; exact absurd ht (liftArc_not_mem_chan _ _ _ _)
    · rw [chan_eq_of_mem ht ht']
  · ext α
    simp only [mem_biUnion, mem_image, id, mem_union, mem_map]
    constructor
    · rintro ⟨p, ⟨ℓ, hℓ, rfl⟩, hα⟩
      rw [hΛ] at hℓ
      rcases (mem_piece hT hLQ hsupp hf ℓ hℓ α).mp hα with ⟨e, he, rfl, -⟩ | ⟨t, htQ, ht, -⟩
      · right; exact ⟨e, he, rfl⟩
      · left; unfold reserve; exact mem_biUnion.mpr ⟨t, mem_product.mpr ⟨htQ, mem_univ _⟩, ht⟩
    · rintro (hα | ⟨e, he, rfl⟩)
      · unfold reserve at hα
        obtain ⟨t, ht, hαt⟩ := mem_biUnion.mp hα
        have htQ := (mem_product.mp ht).1
        have hv := valid_owner t htQ (hf _ htQ)
        exact ⟨piece face a L hT (owner face a L t), ⟨owner face a L t, (hΛ _).mpr hv, rfl⟩,
          (mem_piece hT hLQ hsupp hf _ hv α).mpr (Or.inr ⟨t, htQ, hαt, rfl⟩)⟩
      · have hv : Valid face a L Q (Sum.inr (Sum.inl e) : Label a H T) := he
        exact ⟨piece face a L hT (Sum.inr (Sum.inl e)), ⟨_, (hΛ _).mpr hv, rfl⟩,
          (mem_piece hT hLQ hsupp hf _ hv _).mpr (Or.inl ⟨e, he, rfl, rfl⟩)⟩

omit [DecidableEq Φ] in
/-- For the empty demand the zero filling applies: the reserve alone is exactly partitioned
by class-2 pieces of the catalogue. -/
theorem positivization_empty (Q D : Finset (H × H)) (hDQ : D ⊆ Q) (hT : 0 < T)
    (face : Φ → Face H) (hsupp : ∀ φ, (face φ).supp ⊆ Q) :
    ∃ P ⊆ catalogue face Q D hT, (P : Set (Finset (XV H T × XV H T))).PairwiseDisjoint id ∧
      P.biUnion id = reserve Q T := by
  classical
  obtain ⟨P, hP, hdisj, hcov⟩ := positivization_exact_cover Q D hDQ hT face hsupp ∅
    (empty_subset _) (fun _ => 0) (fun e _ => by simp) (fun e _ => by simp)
  exact ⟨P, hP, hdisj, by rw [hcov]; simp⟩

/-! ### Properties of the reserve and of the catalogue -/

omit [Fintype H] in
theorem mem_reserve {Q : Finset (H × H)} {α : XV H T × XV H T} :
    α ∈ reserve Q T ↔ ∃ e ∈ Q, ∃ b i, α ∈ chan e b i := by
  unfold reserve
  rw [mem_biUnion]
  constructor
  · rintro ⟨⟨e, b, i⟩, ht, hα⟩; exact ⟨e, (mem_product.mp ht).1, b, i, hα⟩
  · rintro ⟨e, he, b, i, hα⟩; exact ⟨(e, b, i), mem_product.mpr ⟨he, mem_univ _⟩, hα⟩

omit [Fintype H] in
theorem reserve_isCyc (c : H → ZMod 3) (Q : Finset (H × H)) (hQ : IsCyc c Q) :
    IsCyc (Sum.elim c (privColor c)) (reserve Q T) := by
  intro α hα
  obtain ⟨e, he, b, i, hα⟩ := mem_reserve.mp hα
  exact chan_isCyc c e (hQ e he) b i α hα

omit [Fintype H] [DecidableEq H] in
theorem lift_isCyc (c : H → ZMod 3) (D : Finset (H × H)) (hD : IsCyc c D) :
    IsCyc (Sum.elim c (privColor c)) (D.map (liftArc H (Priv H T))) := by
  intro α hα
  obtain ⟨e, he, rfl⟩ := mem_map.mp hα
  exact hD e he

omit [Fintype H] in
theorem reserve_disjoint_lift (Q D : Finset (H × H)) :
    Disjoint (reserve Q T) (D.map (liftArc H (Priv H T))) := by
  rw [Finset.disjoint_left]
  intro α hα hα'
  obtain ⟨e, -, b, i, hα⟩ := mem_reserve.mp hα
  obtain ⟨f, -, rfl⟩ := mem_map.mp hα'
  exact liftArc_not_mem_chan e b i f hα

omit [Fintype H] [DecidableEq Φ] in
/-- **Catalogue properties**: every piece is nonempty, lies in `reserve ∪ D`, has at most
`max 10 (5k)` arcs (`k` = maximal face size; `20` for `k = 4`), is balanced and cyclically
tripartite. -/
theorem catalogue_props (c : H → ZMod 3) (Q D : Finset (H × H)) (hQ : IsCyc c Q)
    (hDQ : D ⊆ Q) (hT : 0 < T) (face : Φ → Face H) (hsupp : ∀ φ, (face φ).supp ⊆ Q)
    (hne : ∀ φ, (face φ).supp.Nonempty) (hcirc : ∀ φ, (face φ).IsCirc) (k : ℕ)
    (hk : ∀ φ, (face φ).supp.card ≤ k) :
    ∀ P ∈ catalogue face Q D hT, P.Nonempty ∧
      P ⊆ reserve Q T ∪ D.map (liftArc H (Priv H T)) ∧ P.card ≤ max 10 (5 * k) ∧
      Cycles.Balanced P ∧ IsCyc (Sum.elim c (privColor c)) P := by
  intro P hP
  have hsub : P ⊆ reserve Q T ∪ D.map (liftArc H (Priv H T)) := by
    rcases mem_union.mp hP with hP | hP
    · rcases mem_union.mp hP with hP | hP
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hP
        intro α hα
        obtain ⟨e, he, hαe⟩ := mem_facePiece.mp hα
        exact mem_union_left _ (mem_reserve.mpr ⟨e, hsupp _ he, _, _, hαe⟩)
      · obtain ⟨⟨e, i, j⟩, hx, rfl⟩ := mem_image.mp hP
        have he := (mem_product.mp hx).1
        intro α hα
        rcases mem_union.mp hα with hα | hα
        · exact mem_union_left _ (mem_reserve.mpr ⟨e, he, _, _, hα⟩)
        · exact mem_union_left _ (mem_reserve.mpr ⟨e, he, _, _, hα⟩)
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hP
      intro α hα
      rcases mem_insert.mp hα with rfl | hα
      · exact mem_union_right _ (mem_map_of_mem _ he)
      · exact mem_union_left _ (mem_reserve.mpr ⟨e, hDQ he, _, _, hα⟩)
  refine ⟨?_, hsub, ?_, ?_, ?_⟩
  · rcases mem_union.mp hP with hP | hP
    · rcases mem_union.mp hP with hP | hP
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hP
        exact facePiece_nonempty _ (hne _) _ _
      · obtain ⟨⟨e, i, j⟩, -, rfl⟩ := mem_image.mp hP
        obtain ⟨α, hα⟩ := chan_nonempty e true i
        exact ⟨α, mem_union_left _ hα⟩
    · obtain ⟨e, -, rfl⟩ := mem_image.mp hP
      exact ⟨_, mem_insert_self _ _⟩
  · rcases mem_union.mp hP with hP | hP
    · rcases mem_union.mp hP with hP | hP
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hP
        exact (facePiece_card_le _ _ _).trans
          ((Nat.mul_le_mul_left 5 (hk _)).trans (le_max_right _ _))
      · obtain ⟨⟨e, i, j⟩, -, rfl⟩ := mem_image.mp hP
        exact (pairPiece_card_le e i j).trans (le_max_left _ _)
    · obtain ⟨e, -, rfl⟩ := mem_image.mp hP
      exact (tailPiece_card_le hT e).trans (by omega)
  · rcases mem_union.mp hP with hP | hP
    · rcases mem_union.mp hP with hP | hP
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hP
        exact facePiece_balanced _ (hcirc _) _ _
      · obtain ⟨⟨e, i, j⟩, -, rfl⟩ := mem_image.mp hP
        exact pairPiece_balanced e i j
    · obtain ⟨e, -, rfl⟩ := mem_image.mp hP
      exact tailPiece_balanced hT e
  · exact ((reserve_isCyc c Q hQ).union (lift_isCyc c D (hQ.mono hDQ))).mono hsub

omit [Fintype H] [DecidableEq Φ] in
/-- **Catalogue size**: `|catalogue| ≤ ∑_φ 2 T^{|φ|} + |Q| T² + |D|`. -/
theorem catalogue_card_le (Q D : Finset (H × H)) (hT : 0 < T) (face : Φ → Face H) :
    (catalogue face Q D hT).card ≤
      (∑ φ, 2 * T ^ (face φ).supp.card) + Q.card * T ^ 2 + D.card := by
  unfold catalogue
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · unfold faceLib
    refine card_image_le.trans ?_
    rw [card_univ, Fintype.card_sigma]
    refine le_of_eq (sum_congr rfl (fun φ _ => ?_))
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe]
  · unfold pairLib
    refine card_image_le.trans ?_
    rw [card_product, card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  · exact card_image_le

/-- **§7 in the format of `DenseRefinerWith`**: fresh private vertices with colours, a
cyclically tripartite reserve disjoint from `D`, and a fixed catalogue of nonempty, balanced,
cyclically tripartite pieces with at most `max 10 (5k)` arcs inside `R ∪ D`, all chosen before
`L`, such that every `L ⊆ D` admitting an integer face filling with per-arc load `≤ T` gives an
exact positive partition of `R ∪ L` by catalogue pieces. -/
theorem positivization (c : H → ZMod 3) (Q D : Finset (H × H)) (hQ : IsCyc c Q)
    (hDQ : D ⊆ Q) (hT : 0 < T) (face : Φ → Face H) (hsupp : ∀ φ, (face φ).supp ⊆ Q)
    (hne : ∀ φ, (face φ).supp.Nonempty) (hcirc : ∀ φ, (face φ).IsCirc) (k : ℕ)
    (hk : ∀ φ, (face φ).supp.card ≤ k) :
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset ((H ⊕ U) × (H ⊕ U))) (lib : Finset (Finset ((H ⊕ U) × (H ⊕ U)))),
      IsCyc (Sum.elim c cU) R ∧ Disjoint R (D.map (liftArc H U)) ∧
      (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ D.map (liftArc H U) ∧ P.card ≤ max 10 (5 * k) ∧
        Cycles.Balanced P ∧ IsCyc (Sum.elim c cU) P) ∧
      ∀ L ⊆ D, ∀ a : Φ → ℤ,
        (∀ e ∈ Q, ∑ φ, a φ * (face φ).val e = if e ∈ L then 1 else 0) →
        (∀ e ∈ Q, ∑ φ, |a φ| * |(face φ).val e| ≤ T) →
        ∃ P ⊆ lib, (P : Set (Finset ((H ⊕ U) × (H ⊕ U)))).PairwiseDisjoint id ∧
          P.biUnion id = R ∪ L.map (liftArc H U) :=
  ⟨Priv H T, inferInstance, inferInstance, privColor c, reserve Q T, catalogue face Q D hT,
    reserve_isCyc c Q hQ, reserve_disjoint_lift Q D,
    catalogue_props c Q D hQ hDQ hT face hsupp hne hcirc k hk,
    fun L hLD a hfill hload =>
      positivization_exact_cover Q D hDQ hT face hsupp L hLD a hfill hload⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization
