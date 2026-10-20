/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.Chain
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The universal mod-`q` torsion chain as finite libraries

Generalization of `PaddedF12.TorsionFinite` (`q = 2`): finite library and token sets, their
cardinalities, the exact partition of the selected pieces, and the double-counting incidence bound
`∑_i ∑_{a ∈ atoms i} w a ≤ q ∑_j w (old j) + 4q ∑_{a ∈ tokens} w a`.
-/

namespace TorsionQ

open Finset

variable {q : Nat}

noncomputable def rawLibrary (q N : Nat) : Finset Index :=
  (((range N).product ({false, true} : Finset Bool)).product (range q)).image
    (fun x => ⟨x.1.1, x.1.2, x.2⟩)

noncomputable def library (q N : Nat) (eps : Nat → Nat) (r : Nat) : Finset Index :=
  by classical exact (rawLibrary q N).filter (Valid q N eps r)

theorem mem_rawLibrary {N : Nat} {i : Index} :
    i ∈ rawLibrary q N ↔ i.row < N ∧ i.before < q := by
  rcases i with ⟨j, s, b⟩
  constructor
  · intro hi
    obtain ⟨⟨⟨j', s'⟩, b'⟩, hmem, heq⟩ := mem_image.mp hi
    cases heq
    have hprod := mem_product.mp hmem
    exact ⟨mem_range.mp (mem_product.mp hprod.1).1, mem_range.mp hprod.2⟩
  · rintro ⟨hj, hb⟩
    refine mem_image.mpr ⟨((j, s), b), ?_, rfl⟩
    apply mem_product.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr hj, ?_⟩, mem_range.mpr hb⟩
    cases s <;> simp

theorem mem_library {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index} :
    i ∈ library q N eps r ↔ Valid q N eps r i := by
  simp only [library, mem_filter, mem_rawLibrary]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

theorem card_library_le (N : Nat) (eps : Nat → Nat) (r : Nat) :
    (library q N eps r).card ≤ 2 * q * N := by
  classical
  calc
    (library q N eps r).card ≤ (rawLibrary q N).card := card_filter_le _ _
    _ ≤ (((range N).product ({false, true} : Finset Bool)).product (range q)).card := card_image_le
    _ = 2 * q * N := by simp [card_product]; ring

/-- The wire tokens and the tail tokens. -/
noncomputable def tokens (q N r : Nat) : Finset Atom :=
  ((range (N - 1)) ×ˢ (range q)).image (fun x => Atom.wire x.1 x.2) ∪
    ((range q).filter (fun k => 0 < N ∧ 0 < r ∧ k + r < q)).image Atom.tail

theorem mem_tokens {N r : Nat} {a : Atom} :
    a ∈ tokens q N r ↔
      match a with
      | .old _ => False
      | .wire j k => j + 1 < N ∧ k < q
      | .tail k => 0 < N ∧ 0 < r ∧ k + r < q := by
  cases a with
  | old j => simp [tokens]
  | wire j k =>
    simp only [tokens, mem_union, mem_image, mem_product, mem_range, mem_filter, Prod.exists]
    constructor
    · rintro (⟨a, b, ⟨ha, hb⟩, he⟩ | ⟨k', -, he⟩)
      · cases he; omega
      · cases he
    · intro h
      exact Or.inl ⟨j, k, ⟨by omega, h.2⟩, rfl⟩
  | tail k =>
    simp only [tokens, mem_union, mem_image, mem_product, mem_range, mem_filter, Prod.exists]
    constructor
    · rintro (⟨a, b, -, he⟩ | ⟨k', ⟨-, h⟩, he⟩)
      · cases he
      · cases he; exact h
    · intro h
      exact Or.inr ⟨k, ⟨by omega, h⟩, rfl⟩

theorem card_tokens_le (N r : Nat) : (tokens q N r).card ≤ q * N := by
  rcases N with _ | N
  · have : tokens q 0 r = ∅ := by
      ext a; rw [mem_tokens]; cases a <;> simp
    rw [this]; simp
  · unfold tokens
    have ha : (((range (N + 1 - 1)) ×ˢ (range q)).image (fun x => Atom.wire x.1 x.2)).card ≤
        N * q := card_image_le.trans (by simp [card_product])
    have hb : (((range q).filter (fun k => 0 < N + 1 ∧ 0 < r ∧ k + r < q)).image Atom.tail).card
        ≤ q := card_image_le.trans ((card_filter_le _ _).trans (by simp))
    refine (card_union_le _ _).trans ?_
    have : N * q + q = q * (N + 1) := by ring
    omega

/-- Incoming, outgoing and tail tokens of a library piece. -/
noncomputable def inTok (q : Nat) (i : Index) : Finset Atom :=
  if 0 < i.row then ((range q).filter (fun k => q ≤ k + i.before)).image (Atom.wire (i.row - 1))
  else ∅

noncomputable def outTok (q N : Nat) (eps : Nat → Nat) (i : Index) : Finset Atom :=
  if i.row + 1 < N then
    ((range q).filter (fun k => k + after q eps i < q)).image (Atom.wire i.row)
  else ∅

noncomputable def tailTok (q N r : Nat) (i : Index) : Finset Atom :=
  if i.row + 1 = N ∧ 0 < r then ((range q).filter (fun k => k + r < q)).image Atom.tail else ∅

noncomputable def oldAtoms (i : Index) : Finset Atom :=
  if i.useOld then {Atom.old i.row} else ∅

noncomputable def tokenAtoms (q N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) : Finset Atom :=
  inTok q i ∪ outTok q N eps i ∪ tailTok q N r i

noncomputable def atoms (q N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) : Finset Atom :=
  oldAtoms i ∪ tokenAtoms q N eps r i

theorem mem_oldAtoms {i : Index} {a : Atom} :
    a ∈ oldAtoms i ↔ a = Atom.old i.row ∧ i.useOld = true := by
  unfold oldAtoms; split_ifs with h <;> simp [h]

theorem mem_inTok {i : Index} {a : Atom} :
    a ∈ inTok q i ↔ ∃ k, k < q ∧ q ≤ k + i.before ∧ 0 < i.row ∧ a = Atom.wire (i.row - 1) k := by
  unfold inTok; split_ifs with h
  · simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨k, ⟨hk, hk2⟩, rfl⟩; exact ⟨k, hk, hk2, h, rfl⟩
    · rintro ⟨k, hk, hk2, -, rfl⟩; exact ⟨k, ⟨hk, hk2⟩, rfl⟩
  · simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
    intro k _ _ h'; exact absurd h' h

theorem mem_outTok {N : Nat} {eps : Nat → Nat} {i : Index} {a : Atom} :
    a ∈ outTok q N eps i ↔
      ∃ k, k < q ∧ k + after q eps i < q ∧ i.row + 1 < N ∧ a = Atom.wire i.row k := by
  unfold outTok; split_ifs with h
  · simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨k, ⟨hk, hk2⟩, rfl⟩; exact ⟨k, hk, hk2, h, rfl⟩
    · rintro ⟨k, hk, hk2, -, rfl⟩; exact ⟨k, ⟨hk, hk2⟩, rfl⟩
  · simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
    intro k _ _ h'; exact absurd h' h

theorem mem_tailTok {N r : Nat} {i : Index} {a : Atom} :
    a ∈ tailTok q N r i ↔ ∃ k, k < q ∧ k + r < q ∧ i.row + 1 = N ∧ 0 < r ∧ a = Atom.tail k := by
  unfold tailTok; split_ifs with h
  · simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨k, ⟨hk, hk2⟩, rfl⟩; exact ⟨k, hk, hk2, h.1, h.2, rfl⟩
    · rintro ⟨k, hk, hk2, -, -, rfl⟩; exact ⟨k, ⟨hk, hk2⟩, rfl⟩
  · simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
    intro k _ _ h1 h2; exact absurd ⟨h1, h2⟩ h

theorem mem_atoms {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : a ∈ atoms q N eps r i ↔ Contains q N eps r i a := by
  have hr := hi.1
  have hfirst := hi.2.2.1
  rw [atoms, tokenAtoms, mem_union, mem_union, mem_union, mem_oldAtoms, mem_inTok, mem_outTok,
    mem_tailTok]
  cases a with
  | old j =>
    change _ ↔ i.row = j ∧ i.useOld = true
    constructor
    · rintro (⟨h1, h2⟩ | (⟨k, -, -, -, h⟩ | ⟨k, -, -, -, h⟩) | ⟨k, -, -, -, -, h⟩)
      · exact ⟨(Atom.old.inj h1).symm, h2⟩
      · cases h
      · cases h
      · cases h
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨by rw [h1], h2⟩
  | wire j k =>
    change _ ↔ k < q ∧ ((i.row = j ∧ i.row + 1 < N ∧ k + after q eps i < q) ∨
      (i.row = j + 1 ∧ q ≤ k + i.before))
    constructor
    · rintro (⟨h1, -⟩ | (⟨k', hk, hk2, h0, h⟩ | ⟨k', hk, hk2, hrow, h⟩) | ⟨k', -, -, -, -, h⟩)
      · cases h1
      · obtain ⟨hj, hkk⟩ := Atom.wire.inj h
        subst hkk
        exact ⟨hk, Or.inr ⟨by omega, hk2⟩⟩
      · obtain ⟨hj, hkk⟩ := Atom.wire.inj h
        subst hkk
        exact ⟨hk, Or.inl ⟨hj.symm, hrow, hk2⟩⟩
      · cases h
    · rintro ⟨hk, ⟨hj, hrow, hk2⟩ | ⟨hj, hk2⟩⟩
      · exact Or.inr (Or.inl (Or.inr ⟨k, hk, hk2, hrow, by rw [hj]⟩))
      · exact Or.inr (Or.inl (Or.inl ⟨k, hk, hk2, by omega, by rw [hj, Nat.add_sub_cancel]⟩))
  | tail k =>
    change _ ↔ i.row + 1 = N ∧ 0 < r ∧ k + r < q
    constructor
    · rintro (⟨h1, -⟩ | (⟨k', -, -, -, h⟩ | ⟨k', -, -, -, h⟩) | ⟨k', hk, hk2, h1, h2, h⟩)
      · cases h1
      · cases h
      · cases h
      · cases Atom.tail.inj h
        exact ⟨h1, h2, hk2⟩
    · rintro ⟨h1, h2, hk2⟩
      exact Or.inr (Or.inr ⟨k, by omega, hk2, h1, h2, rfl⟩)

theorem card_filter_lt_sub (a : Nat) : ((range q).filter (fun k => k + a < q)).card = q - a := by
  have : (range q).filter (fun k => k + a < q) = range (q - a) := by
    ext k; simp; omega
  rw [this, card_range]

theorem card_filter_ge (b : Nat) (hb : b ≤ q) :
    ((range q).filter (fun k => q ≤ k + b)).card = b := by
  have : (range q).filter (fun k => q ≤ k + b) = Ico (q - b) q := by
    ext k; simp; omega
  rw [this, Nat.card_Ico]; omega

theorem card_tokenAtoms {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : (tokenAtoms q N eps r i).card = tokenCount q N eps r i := by
  have hb := hi.2.1
  have hfirst := hi.2.2.1
  have hd1 : Disjoint (inTok q i) (outTok q N eps i) := by
    rw [disjoint_left]; intro a ha hb'
    rw [mem_inTok] at ha; rw [mem_outTok] at hb'
    obtain ⟨k, -, -, h0, rfl⟩ := ha
    obtain ⟨k', -, -, -, h⟩ := hb'
    have := (Atom.wire.inj h).1
    omega
  have hd2 : Disjoint (inTok q i ∪ outTok q N eps i) (tailTok q N r i) := by
    rw [disjoint_left]; intro a ha hb'
    rw [mem_tailTok] at hb'
    obtain ⟨k, -, -, -, -, rfl⟩ := hb'
    rw [mem_union, mem_inTok, mem_outTok] at ha
    rcases ha with ⟨k', -, -, -, h⟩ | ⟨k', -, -, -, h⟩ <;> cases h
  have hinj : ∀ j, Function.Injective (Atom.wire j) := fun j a b h => by cases h; rfl
  have htinj : Function.Injective Atom.tail := fun a b h => by cases h; rfl
  have hin : (inTok q i).card = i.before := by
    unfold inTok
    split
    · rw [card_image_of_injective _ (hinj _), card_filter_ge _ hb.le]
    · simp; omega
  have hout : (outTok q N eps i).card = if i.row + 1 < N then q - after q eps i else 0 := by
    unfold outTok
    split
    · rw [card_image_of_injective _ (hinj _), card_filter_lt_sub]
    · simp
  have htail : (tailTok q N r i).card = if i.row + 1 = N ∧ 0 < r then q - r else 0 := by
    unfold tailTok
    split
    · rw [card_image_of_injective _ htinj, card_filter_lt_sub]
    · simp
  unfold tokenAtoms tokenCount
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, hin, hout, htail]

theorem card_tokenAtoms_le (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : (tokenAtoms q N eps r i).card ≤ 3 * q := by
  rw [card_tokenAtoms hi]
  exact tokenCount_le hq hi

noncomputable def selectedLibrary (q N : Nat) (eps : Nat → Nat) (choose : Nat → Bool) :
    Finset Index :=
  (range N).image (selected q eps choose)

noncomputable def targetAtoms (q N r : Nat) (choose : Nat → Bool) : Finset Atom :=
  ((range N).filter fun j => choose j = true).image Atom.old ∪ tokens q N r

theorem mem_targetAtoms {N r : Nat} {choose : Nat → Bool} {a : Atom} :
    a ∈ targetAtoms q N r choose ↔ Target q N r choose a := by
  cases a with
  | old j => simp [targetAtoms, mem_tokens, Target]
  | wire j k =>
    rw [targetAtoms, mem_union, mem_tokens]
    simp [Target]
  | tail k =>
    rw [targetAtoms, mem_union, mem_tokens]
    simp [Target]

theorem selectedLibrary_subset (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool}
    {r : Nat} (hfinal : carry q eps choose N = r) :
    selectedLibrary q N eps choose ⊆ library q N eps r := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
  exact mem_library.mpr (selected_valid hq hfinal (mem_range.mp hj))

theorem biUnion_atoms_selected (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool}
    {r : Nat} (hfinal : carry q eps choose N = r) :
    (selectedLibrary q N eps choose).biUnion (atoms q N eps r) = targetAtoms q N r choose := by
  ext a
  rw [mem_biUnion, mem_targetAtoms]
  constructor
  · rintro ⟨i, hi, hai⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    have hj' := mem_range.mp hj
    exact selected_no_extra hj' ((mem_atoms (selected_valid hq hfinal hj')).mp hai)
  · intro ha
    obtain ⟨j, hj, ha⟩ := selected_covers (eps := eps) ha
    exact ⟨selected q eps choose j, mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩,
      (mem_atoms (selected_valid hq hfinal hj)).mpr ha⟩

theorem pairwiseDisjoint_atoms_selected (hq : 0 < q) {N : Nat} {eps : Nat → Nat}
    {choose : Nat → Bool} {r : Nat} (hfinal : carry q eps choose N = r) :
    (selectedLibrary q N eps choose : Set Index).PairwiseDisjoint (atoms q N eps r) := by
  intro i hi j hj hne
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hj
  change Disjoint _ _
  rw [disjoint_left]
  intro a hak hal
  have hk' := mem_range.mp hk
  have hl' := mem_range.mp hl
  have hkl := selected_disjoint
    ((mem_atoms (selected_valid hq hfinal hk')).mp hak)
    ((mem_atoms (selected_valid hq hfinal hl')).mp hal)
  exact hne (congrArg (selected q eps choose) hkl)

theorem carry_eq_sum_mod (N : Nat) (eps : Nat → Nat) (choose : Nat → Bool) :
    carry q eps choose N = (∑ j ∈ range N, if choose j then eps j % q else 0) % q := by
  induction N with
  | zero => simp [carry]
  | succ N ih =>
    rw [carry, ih, sum_range_succ]
    conv_rhs => rw [Nat.add_mod]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod]

theorem occurrence_card_le (hq : 0 < q) (N : Nat) (eps : Nat → Nat) (r : Nat) (a : Atom) :
    ((library q N eps r).filter (fun i => a ∈ atoms q N eps r i)).card ≤ slotBound q a := by
  have h := card_le_card_of_injOn (localSlot q a)
    (s := (library q N eps r).filter (fun i => a ∈ atoms q N eps r i)) (t := range (slotBound q a))
    (fun i hi => mem_range.mpr (localSlot_bound (mem_library.mp (mem_filter.mp hi).1)))
    (by
      intro i hi j hj heq
      have hiv := mem_library.mp (mem_filter.mp hi).1
      have hjv := mem_library.mp (mem_filter.mp hj).1
      exact localSlot_injective hq hiv hjv
        ((mem_atoms hiv).mp (mem_filter.mp hi).2)
        ((mem_atoms hjv).mp (mem_filter.mp hj).2) heq)
  simpa using h

noncomputable def allAtoms (q N r : Nat) : Finset Atom :=
  (range N).image Atom.old ∪ tokens q N r

theorem atoms_subset_all {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : atoms q N eps r i ⊆ allAtoms q N r := by
  intro a ha
  have h := (mem_atoms hi).mp ha
  have hr := hi.1
  cases a with
  | old j =>
    change i.row = j ∧ _ at h
    exact mem_union_left _ (mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩)
  | wire j k =>
    apply mem_union_right
    apply mem_tokens.mpr
    change k < q ∧ ((i.row = j ∧ i.row + 1 < N ∧ _) ∨ (i.row = j + 1 ∧ _)) at h
    change j + 1 < N ∧ k < q
    omega
  | tail k =>
    apply mem_union_right
    apply mem_tokens.mpr
    change i.row + 1 = N ∧ 0 < r ∧ k + r < q at h
    change 0 < N ∧ 0 < r ∧ k + r < q
    omega

theorem old_disjoint_tokens (N r : Nat) :
    Disjoint ((range N).image Atom.old) (tokens q N r) := by
  rw [disjoint_left]
  intro a ha ht
  obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
  exact (mem_tokens.mp ht)

/-- Double counting with the explicit local-slot bounds. -/
theorem weighted_incidence_le (hq : 0 < q) (N : Nat) (eps : Nat → Nat) (r : Nat)
    (w : Atom → Nat) :
    ∑ i ∈ library q N eps r, ∑ a ∈ atoms q N eps r i, w a ≤
      q * ∑ j ∈ range N, w (.old j) + 4 * q * ∑ a ∈ tokens q N r, w a := by
  classical
  have hdouble :
      (∑ i ∈ library q N eps r, ∑ a ∈ atoms q N eps r i, w a) =
      ∑ a ∈ allAtoms q N r,
        ((library q N eps r).filter (fun i => a ∈ atoms q N eps r i)).card * w a := by
    calc
      (∑ i ∈ library q N eps r, ∑ a ∈ atoms q N eps r i, w a) =
          ∑ i ∈ library q N eps r, ∑ a ∈ allAtoms q N r,
            if a ∈ atoms q N eps r i then w a else 0 := by
        apply sum_congr rfl
        intro i hi
        rw [← sum_filter]
        congr 1
        ext a
        simp only [mem_filter]
        exact ⟨fun ha => ⟨atoms_subset_all (mem_library.mp hi) ha, ha⟩, fun ha => ha.2⟩
      _ = ∑ a ∈ allAtoms q N r, ∑ i ∈ library q N eps r,
            if a ∈ atoms q N eps r i then w a else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        rw [← sum_filter]
        simp [sum_const, mul_comm]
  rw [hdouble, allAtoms, sum_union (old_disjoint_tokens N r), sum_image (fun i _ j _ h => Atom.old.inj h)]
  have h1 : (∑ j ∈ range N, ((library q N eps r).filter
      (fun i => Atom.old j ∈ atoms q N eps r i)).card * w (.old j)) ≤ q * ∑ j ∈ range N, w (.old j) := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => by
      have := occurrence_card_le hq N eps r (.old j)
      simp only [slotBound] at this
      exact Nat.mul_le_mul_right _ this
  have h2 : (∑ a ∈ tokens q N r, ((library q N eps r).filter
      (fun i => a ∈ atoms q N eps r i)).card * w a) ≤ 4 * q * ∑ a ∈ tokens q N r, w a := by
    rw [mul_sum]
    exact sum_le_sum fun a ha => by
      have := occurrence_card_le hq N eps r a
      have hb : slotBound q a ≤ 4 * q := by
        cases a <;> simp only [slotBound] <;> omega
      exact Nat.mul_le_mul_right _ (this.trans hb)
  omega

theorem old_not_mem_tokenAtoms {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index} (j : Nat) :
    Atom.old j ∉ tokenAtoms q N eps r i := by
  rw [tokenAtoms, mem_union, mem_union, mem_inTok, mem_outTok, mem_tailTok]
  rintro ((⟨k, -, -, -, h⟩ | ⟨k, -, -, -, h⟩) | ⟨k, -, -, -, -, h⟩) <;> cases h

theorem oldAtoms_disjoint_tokenAtoms (N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) :
    Disjoint (oldAtoms i) (tokenAtoms q N eps r i) := by
  rw [disjoint_left]
  intro a ha ht
  obtain ⟨rfl, -⟩ := mem_oldAtoms.mp ha
  exact old_not_mem_tokenAtoms _ ht

theorem tokenAtoms_subset_tokens {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : tokenAtoms q N eps r i ⊆ tokens q N r := by
  intro a ha
  have hmem := atoms_subset_all hi (mem_union_right _ ha)
  rcases mem_union.mp hmem with hmem | hmem
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hmem
    exact absurd ha (old_not_mem_tokenAtoms j)
  · exact hmem

def atomValue (v : Nat → Nat) : Atom → Nat
  | .old j => v j
  | _ => 1

theorem sum_atoms_value {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) (v : Nat → Nat) :
    (∑ a ∈ atoms q N eps r i, atomValue v a) =
      (if i.useOld then v i.row else 0) + tokenCount q N eps r i := by
  rw [atoms, sum_union (oldAtoms_disjoint_tokenAtoms N eps r i)]
  have hold : (∑ a ∈ oldAtoms i, atomValue v a) = if i.useOld then v i.row else 0 := by
    cases hs : i.useOld <;> simp [oldAtoms, hs, atomValue]
  have htok : (∑ a ∈ tokenAtoms q N eps r i, atomValue v a) = (tokenAtoms q N eps r i).card := by
    calc
      (∑ a ∈ tokenAtoms q N eps r i, atomValue v a) =
          ∑ a ∈ tokenAtoms q N eps r i, (1 : Nat) := by
        apply sum_congr rfl
        intro a ha
        cases a with
        | old j => exact absurd ha (old_not_mem_tokenAtoms j)
        | wire j k => rfl
        | tail k => rfl
      _ = _ := by simp
  rw [hold, htok, card_tokenAtoms hi]

end TorsionQ

#print axioms TorsionQ.card_tokenAtoms
#print axioms TorsionQ.weighted_incidence_le
#print axioms TorsionQ.biUnion_atoms_selected
#print axioms TorsionQ.sum_atoms_value
