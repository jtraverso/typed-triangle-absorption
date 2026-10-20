/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Std

@[expose] public section

/-!
# A fixed universal chain for one cyclic torsion value modulo `q`

Generalization of `PaddedF12.TorsionChain` (the case `q = 2`). There is one old piece at every row
`i < N`, with torsion `eps i` (taken mod `q`). A library index chooses whether to use the old piece
and an incoming carry `before < q`. Every wire `j` (between rows `j` and `j + 1`) carries `q` private
torsion-one tokens `wire j k`, `k < q`; a piece at row `j` with outgoing carry `a` takes the tokens
`k < q - a` of its wire, the next row takes the other `a` tokens. The last row takes `(q - r) mod q`
tail tokens. Every library piece has torsion `0 (mod q)`, and for every selection `choose` with total
carry `r` the selected pieces partition the target exactly.
-/

namespace TorsionQ

variable (q : Nat)

structure Index where
  row : Nat
  useOld : Bool
  before : Nat
deriving DecidableEq, Repr

inductive Atom where
  | old : Nat → Atom
  | wire : Nat → Nat → Atom
  | tail : Nat → Atom
deriving DecidableEq, Repr

def oldVal (eps : Nat → Nat) (i : Index) : Nat :=
  if i.useOld then eps i.row % q else 0

def after (eps : Nat → Nat) (i : Index) : Nat :=
  (i.before + oldVal q eps i) % q

variable {q}

theorem oldVal_lt (hq : 0 < q) (eps : Nat → Nat) (i : Index) : oldVal q eps i < q := by
  unfold oldVal
  split
  · exact Nat.mod_lt _ hq
  · exact hq

theorem after_lt (hq : 0 < q) (eps : Nat → Nat) (i : Index) : after q eps i < q :=
  Nat.mod_lt _ hq

variable (q)

def Valid (N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) : Prop :=
  i.row < N ∧ i.before < q ∧ (i.row = 0 → i.before = 0) ∧
    (i.row + 1 = N → after q eps i = r)

def Contains (N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) : Atom → Prop
  | .old j => i.row = j ∧ i.useOld = true
  | .wire j k => k < q ∧ ((i.row = j ∧ i.row + 1 < N ∧ k + after q eps i < q) ∨
      (i.row = j + 1 ∧ q ≤ k + i.before))
  | .tail k => i.row + 1 = N ∧ 0 < r ∧ k + r < q

/-- Number of private token occurrences in a library piece. -/
def tokenCount (N : Nat) (eps : Nat → Nat) (r : Nat) (i : Index) : Nat :=
  i.before + (if i.row + 1 < N then q - after q eps i else 0) +
  (if i.row + 1 = N ∧ 0 < r then q - r else 0)

variable {q}

theorem tokenCount_le (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) : tokenCount q N eps r i ≤ 3 * q := by
  have hb := hi.2.1
  have ha := after_lt hq eps i
  unfold tokenCount
  split <;> split <;> omega

/-- Every member of the fixed library has torsion zero mod `q`. -/
theorem piece_zero (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index}
    (hi : Valid q N eps r i) :
    (oldVal q eps i + tokenCount q N eps r i) % q = 0 := by
  obtain ⟨hrow, hb, hfirst, hlast⟩ := hi
  have he := oldVal_lt hq eps i
  have ha : after q eps i = (i.before + oldVal q eps i) % q := rfl
  have hlt := after_lt hq eps i
  unfold tokenCount
  by_cases hout : i.row + 1 < N
  · have hnl : ¬ (i.row + 1 = N ∧ 0 < r) := by omega
    rw [if_pos hout, if_neg hnl]
    have hdm := Nat.div_add_mod (i.before + oldVal q eps i) q
    rw [← ha] at hdm
    have hle : i.before + oldVal q eps i < 2 * q := by omega
    have hdiv : (i.before + oldVal q eps i) / q ≤ 1 := by
      have := Nat.div_lt_iff_lt_mul hq |>.mpr (by omega : i.before + oldVal q eps i < 2 * q)
      omega
    have e : oldVal q eps i + (i.before + (q - after q eps i) + 0) =
        q * ((i.before + oldVal q eps i) / q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e, Nat.mul_mod_right]
  · have hlast' : i.row + 1 = N := by omega
    have hr := hlast hlast'
    rw [if_neg hout]
    have hdm := Nat.div_add_mod (i.before + oldVal q eps i) q
    rw [← ha, hr] at hdm
    by_cases hr0 : 0 < r
    · rw [if_pos ⟨hlast', hr0⟩]
      have e : oldVal q eps i + (i.before + 0 + (q - r)) =
          q * ((i.before + oldVal q eps i) / q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [e, Nat.mul_mod_right]
    · rw [if_neg (by omega)]
      have e : oldVal q eps i + (i.before + 0 + 0) = q * ((i.before + oldVal q eps i) / q) := by
        omega
      rw [e, Nat.mul_mod_right]

variable (q)

def carry (eps : Nat → Nat) (choose : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => (carry eps choose j + if choose j then eps j % q else 0) % q

def selected (eps : Nat → Nat) (choose : Nat → Bool) (j : Nat) : Index :=
  ⟨j, choose j, carry q eps choose j⟩

def Target (N : Nat) (r : Nat) (choose : Nat → Bool) : Atom → Prop
  | .old j => j < N ∧ choose j = true
  | .wire j k => j + 1 < N ∧ k < q
  | .tail k => 0 < N ∧ 0 < r ∧ k + r < q

variable {q}

theorem carry_lt (hq : 0 < q) (eps : Nat → Nat) (choose : Nat → Bool) (j : Nat) :
    carry q eps choose j < q := by
  cases j with
  | zero => exact hq
  | succ j => exact Nat.mod_lt _ hq

theorem after_selected (eps : Nat → Nat) (choose : Nat → Bool) (j : Nat) :
    after q eps (selected q eps choose j) = carry q eps choose (j + 1) := rfl

theorem selected_valid (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool} {r : Nat}
    (hfinal : carry q eps choose N = r) {j : Nat} (hj : j < N) :
    Valid q N eps r (selected q eps choose j) := by
  refine ⟨hj, carry_lt hq eps choose j, ?_, ?_⟩
  · intro h
    change j = 0 at h
    subst j
    rfl
  · intro h
    rw [after_selected]
    change j + 1 = N at h
    rw [h, hfinal]

theorem selected_no_extra {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool} {r : Nat}
    {j : Nat} (hj : j < N) {a : Atom}
    (ha : Contains q N eps r (selected q eps choose j) a) : Target q N r choose a := by
  cases a with
  | old k =>
    change j = k ∧ choose j = true at ha
    obtain ⟨rfl, hs⟩ := ha
    exact ⟨hj, hs⟩
  | wire l k =>
    change k < q ∧ ((j = l ∧ j + 1 < N ∧ _) ∨ (j = l + 1 ∧ _)) at ha
    change l + 1 < N ∧ k < q
    omega
  | tail k =>
    change j + 1 = N ∧ 0 < r ∧ k + r < q at ha
    change 0 < N ∧ 0 < r ∧ k + r < q
    omega

theorem selected_covers {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool} {r : Nat} {a : Atom}
    (ha : Target q N r choose a) :
    ∃ j, j < N ∧ Contains q N eps r (selected q eps choose j) a := by
  cases a with
  | old k =>
    exact ⟨k, ha.1, rfl, ha.2⟩
  | wire l k =>
    obtain ⟨hl, hk⟩ := ha
    by_cases hp : k + carry q eps choose (l + 1) < q
    · exact ⟨l, by omega, hk, Or.inl ⟨rfl, hl, (after_selected eps choose l).symm ▸ hp⟩⟩
    · exact ⟨l + 1, hl, hk, Or.inr ⟨rfl, by change q ≤ k + carry q eps choose (l + 1); omega⟩⟩
  | tail k =>
    obtain ⟨hN, hr, hk⟩ := ha
    refine ⟨N - 1, by omega, ?_⟩
    change N - 1 + 1 = N ∧ 0 < r ∧ k + r < q
    omega

theorem selected_disjoint {N : Nat} {eps : Nat → Nat} {choose : Nat → Bool} {r : Nat}
    {j k : Nat} {a : Atom}
    (hj : Contains q N eps r (selected q eps choose j) a)
    (hk : Contains q N eps r (selected q eps choose k) a) : j = k := by
  cases a with
  | old l =>
    change j = l ∧ _ at hj
    change k = l ∧ _ at hk
    omega
  | wire l m =>
    change m < q ∧ ((j = l ∧ j + 1 < N ∧ m + after q eps (selected q eps choose j) < q) ∨
      (j = l + 1 ∧ q ≤ m + carry q eps choose j)) at hj
    change m < q ∧ ((k = l ∧ k + 1 < N ∧ m + after q eps (selected q eps choose k) < q) ∨
      (k = l + 1 ∧ q ≤ m + carry q eps choose k)) at hk
    rw [after_selected] at hj hk
    rcases hj with ⟨-, ⟨hjl, -, hjp⟩ | ⟨hjl, hjp⟩⟩ <;>
      rcases hk with ⟨-, ⟨hkl, -, hkp⟩ | ⟨hkl, hkp⟩⟩
    · omega
    · subst j; subst k; omega
    · subst j; subst k; omega
    · omega
  | tail m =>
    change j + 1 = N ∧ _ at hj
    change k + 1 = N ∧ _ at hk
    omega

/-- **Full universal partition statement** modulo `q`. -/
theorem fixed_chain_refines (hq : 0 < q) (N : Nat) (eps : Nat → Nat) (r : Nat) :
    (∀ i, Valid q N eps r i →
      tokenCount q N eps r i ≤ 3 * q ∧ (oldVal q eps i + tokenCount q N eps r i) % q = 0) ∧
    ∀ choose : Nat → Bool, carry q eps choose N = r →
      (∀ j < N, Valid q N eps r (selected q eps choose j)) ∧
      (∀ a, Target q N r choose a ↔
        ∃ j, j < N ∧ Contains q N eps r (selected q eps choose j) a) ∧
      (∀ j k a, Contains q N eps r (selected q eps choose j) a →
        Contains q N eps r (selected q eps choose k) a → j = k) := by
  refine ⟨fun _ hi => ⟨tokenCount_le hq hi, piece_zero hq hi⟩, ?_⟩
  intro choose hfinal
  refine ⟨fun _ hj => selected_valid hq hfinal hj, ?_, fun _ _ _ => selected_disjoint⟩
  intro a
  exact ⟨selected_covers, fun ⟨_, hj, ha⟩ => selected_no_extra hj ha⟩

/-! ## Local incidence bounds, as explicit finite-slot injections -/

def useBit (b : Bool) : Nat := if b then 1 else 0

theorem useBit_lt (b : Bool) : useBit b < 2 := by cases b <;> decide

theorem useBit_injective {b c : Bool} (h : useBit b = useBit c) : b = c := by
  cases b <;> cases c <;> simp_all [useBit]

variable (q)

def localSlot (a : Atom) (i : Index) : Nat :=
  match a with
  | .old _ => i.before
  | .wire j _ => if i.row = j then q * useBit i.useOld + i.before
      else 2 * q + q * useBit i.useOld + i.before
  | .tail _ => q * useBit i.useOld + i.before

def slotBound (a : Atom) : Nat :=
  match a with
  | .old _ => q
  | .wire _ _ => 4 * q
  | .tail _ => 2 * q

variable {q}

theorem localSlot_bound {N : Nat} {eps : Nat → Nat} {r : Nat} {i : Index} {a : Atom}
    (hi : Valid q N eps r i) : localSlot q a i < slotBound q a := by
  have hb := hi.2.1
  have hs := useBit_lt i.useOld
  have hm : q * useBit i.useOld ≤ q := by
    have := Nat.mul_le_mul_left q (show useBit i.useOld ≤ 1 by omega); simpa using this
  cases a <;> simp only [localSlot, slotBound]
  · omega
  · split <;> omega
  · omega

theorem localSlot_injective (hq : 0 < q) {N : Nat} {eps : Nat → Nat} {r : Nat}
    {i j : Index} {a : Atom} (hi : Valid q N eps r i) (hj : Valid q N eps r j)
    (hai : Contains q N eps r i a) (haj : Contains q N eps r j a)
    (heq : localSlot q a i = localSlot q a j) : i = j := by
  obtain ⟨ir, is, ib⟩ := i
  obtain ⟨jr, js, jb⟩ := j
  have hib : ib < q := hi.2.1
  have hjb : jb < q := hj.2.1
  have hu1 := useBit_lt is
  have hu2 := useBit_lt js
  have key : ∀ (b c : Bool) (x y : Nat), x < q → y < q →
      q * useBit b + x = q * useBit c + y → b = c ∧ x = y := by
    intro b c x y hx hy h
    have hb := useBit_lt b
    have hc := useBit_lt c
    have hbc : useBit b = useBit c := by
      rcases Nat.lt_or_ge (useBit b) (useBit c) with hlt | hge
      · exfalso
        have : useBit b + 1 ≤ useBit c := hlt
        have := Nat.mul_le_mul_left q this
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      · rcases Nat.lt_or_ge (useBit c) (useBit b) with hlt' | hge'
        · exfalso
          have : useBit c + 1 ≤ useBit b := hlt'
          have := Nat.mul_le_mul_left q this
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        · omega
    refine ⟨useBit_injective hbc, ?_⟩
    rw [hbc] at h
    omega
  cases a with
  | old k =>
    change ir = k ∧ is = true at hai
    change jr = k ∧ js = true at haj
    change ib = jb at heq
    obtain ⟨rfl, rfl⟩ := hai
    obtain ⟨rfl, rfl⟩ := haj
    cases heq
    rfl
  | wire l m =>
    change m < q ∧ ((ir = l ∧ ir + 1 < N ∧ _) ∨ (ir = l + 1 ∧ _)) at hai
    change m < q ∧ ((jr = l ∧ jr + 1 < N ∧ _) ∨ (jr = l + 1 ∧ _)) at haj
    change (if ir = l then q * useBit is + ib else 2 * q + q * useBit is + ib) =
      (if jr = l then q * useBit js + jb else 2 * q + q * useBit js + jb) at heq
    have hm1 : q * useBit is ≤ q := by
      have := Nat.mul_le_mul_left q (show useBit is ≤ 1 by omega); simpa using this
    have hm2 : q * useBit js ≤ q := by
      have := Nat.mul_le_mul_left q (show useBit js ≤ 1 by omega); simpa using this
    rcases hai with ⟨-, ⟨hir, -⟩ | ⟨hir, -⟩⟩ <;> rcases haj with ⟨-, ⟨hjr, -⟩ | ⟨hjr, -⟩⟩
    · subst ir; subst jr
      simp only [if_true] at heq
      obtain ⟨h1, h2⟩ := key is js ib jb hib hjb heq
      subst h1; subst h2; rfl
    · subst ir; subst jr
      rw [if_pos rfl, if_neg (by omega)] at heq
      omega
    · subst ir; subst jr
      rw [if_neg (by omega), if_pos rfl] at heq
      omega
    · subst ir; subst jr
      rw [if_neg (by omega), if_neg (by omega)] at heq
      obtain ⟨h1, h2⟩ := key is js ib jb hib hjb (by omega)
      subst h1; subst h2; rfl
  | tail m =>
    change ir + 1 = N ∧ _ at hai
    change jr + 1 = N ∧ _ at haj
    change q * useBit is + ib = q * useBit js + jb at heq
    have hir : ir = jr := by omega
    obtain ⟨h1, h2⟩ := key is js ib jb hib hjb heq
    subst hir; subst h1; subst h2; rfl

end TorsionQ

#print axioms TorsionQ.piece_zero
#print axioms TorsionQ.fixed_chain_refines
#print axioms TorsionQ.localSlot_injective
