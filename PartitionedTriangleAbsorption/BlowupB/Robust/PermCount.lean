/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Counting permutations that map a set into a set

For a finite type `α` with `n` elements and finite sets `A, W ⊆ α` with `|A| = a`, `|W| = w`,
the number of permutations `σ` with `σ(A) ⊆ W` is `(w)_a (n - a)!`. We prove it in the form
`#{σ | σ(A) ⊆ W} * (n)_a = (w)_a * n!` (`card_perm_mapsTo_mul`) and deduce the probability bound
`#{σ | σ(A) ⊆ W} * n^a ≤ w^a * n!` (`card_perm_mapsTo_le`), together with its `d`-fold product form
(`card_pi_perm_mapsTo`). These are the counting inputs of the robust matching lemma (`Robust.RMBG`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The restriction of a permutation to the elements of `A`. -/
def restr (A : Finset α) (σ : Equiv.Perm α) : A ↪ α :=
  (Function.Embedding.subtype _).trans σ.toEmbedding

@[simp] theorem restr_apply (A : Finset α) (σ : Equiv.Perm α) (x : A) : restr A σ x = σ x := rfl

theorem exists_restr_eq (A : Finset α) (e : A ↪ α) : ∃ τ : Equiv.Perm α, restr A τ = e := by
  classical
  let f : {x // x ∈ A} ≃ {y // y ∈ Set.range e} := Equiv.ofInjective e e.injective
  refine ⟨f.extendSubtype, ?_⟩
  ext x
  rw [restr_apply, Equiv.extendSubtype_apply_of_mem f x.1 x.2]
  simp [f]

theorem card_fiber_restr (A : Finset α) (e : A ↪ α) :
    #(univ.filter fun σ : Equiv.Perm α => restr A σ = e) =
      #(univ.filter fun σ : Equiv.Perm α => restr A σ = restr A 1) := by
  obtain ⟨τ, hτ⟩ := exists_restr_eq A e
  refine card_bij (fun σ _ => τ⁻¹ * σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    ext x
    have h1 := congrArg (fun g : A ↪ α => g x) hσ
    have h2 := congrArg (fun g : A ↪ α => g x) hτ
    simp only [restr_apply] at h1 h2
    simp only [restr_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [h1, ← h2]; simp
  · intro σ₁ _ σ₂ _ h
    simpa using h
  · intro σ hσ
    refine ⟨τ * σ, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    ext x
    have h1 := congrArg (fun g : A ↪ α => g x) hσ
    have h2 := congrArg (fun g : A ↪ α => g x) hτ
    simp only [restr_apply, Equiv.Perm.one_apply] at h1 h2
    simp only [restr_apply, Equiv.Perm.mul_apply]
    rw [h1, h2]

/-- Permutations whose restriction lies in a set `E` of embeddings: `|E|` fibres of equal size. -/
theorem card_perm_restr_mem (A : Finset α) (E : Finset (A ↪ α)) :
    #(univ.filter fun σ : Equiv.Perm α => restr A σ ∈ E) =
      #E * #(univ.filter fun σ : Equiv.Perm α => restr A σ = restr A 1) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := restr A) (s := univ.filter fun σ : Equiv.Perm α => restr A σ ∈ E)
    (t := E) (fun σ hσ => (mem_filter.mp hσ).2)]
  rw [← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  rw [← card_fiber_restr A e]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ he, h⟩

/-- Embeddings of `A` with values in `W`: `(|W|)_{|A|}` of them. -/
theorem card_emb_into (A W : Finset α) :
    #(univ.filter fun e : A ↪ α => ∀ x, e x ∈ W) = (#W).descFactorial #A := by
  classical
  rw [← Fintype.card_coe A, ← Fintype.card_coe W, ← Fintype.card_embedding_eq,
    ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun e => ⟨fun x => ⟨e.1 x, e.2 x⟩, fun x y h => e.1.injective (congrArg Subtype.val h)⟩
      invFun := fun g => ⟨g.trans (Function.Embedding.subtype _), fun x => (g x).2⟩
      left_inv := fun e => Subtype.ext (Function.Embedding.ext fun x => rfl)
      right_inv := fun g => Function.Embedding.ext fun x => rfl }

/-- **Exact count.** `#{σ | σ(A) ⊆ W} * (n)_a = (w)_a * n!`. -/
theorem card_perm_mapsTo_mul (A W : Finset α) :
    #(univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ W) * (Fintype.card α).descFactorial #A =
      (#W).descFactorial #A * (Fintype.card α).factorial := by
  classical
  set F := #(univ.filter fun σ : Equiv.Perm α => restr A σ = restr A 1)
  have hset : ∀ W' : Finset α, (univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ W') =
      univ.filter fun σ : Equiv.Perm α => restr A σ ∈ univ.filter fun e : A ↪ α => ∀ x, e x ∈ W' := by
    intro W'
    ext σ
    simp only [mem_filter, mem_univ, true_and, restr_apply]
    exact ⟨fun h x => h x.1 x.2, fun h x hx => h ⟨x, hx⟩⟩
  have hW : #(univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ W) = (#W).descFactorial #A * F := by
    rw [hset W, card_perm_restr_mem, card_emb_into]
  have huniv : (Fintype.card α).factorial = (Fintype.card α).descFactorial #A * F := by
    have h := congrArg Finset.card (hset univ)
    have hall : (univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ (univ : Finset α)) = univ := by
      ext σ; simp
    rw [hall, card_perm_restr_mem, card_emb_into, card_univ, card_univ, Fintype.card_perm] at h
    exact h
  rw [hW, huniv]
  ring

/-- `(w)_k * n^k ≤ w^k * (n)_k` for `w ≤ n`. -/
theorem descFactorial_mul_pow_le {w n : ℕ} (hwn : w ≤ n) :
    ∀ k : ℕ, w.descFactorial k * n ^ k ≤ w ^ k * n.descFactorial k
  | 0 => by simp
  | k + 1 => by
    have ih := descFactorial_mul_pow_le hwn k
    have hstep : (w - k) * n ≤ w * (n - k) := by
      rcases le_or_gt k w with hk | hk
      · have h1 : (w - k) * n = w * n - k * n := Nat.sub_mul w k n
        have h2 : w * (n - k) = w * n - w * k := Nat.mul_sub w n k
        rw [h1, h2]
        have : w * k ≤ k * n := by rw [mul_comm w k]; exact Nat.mul_le_mul_left k hwn
        omega
      · rw [Nat.sub_eq_zero_of_le hk.le, zero_mul]; exact Nat.zero_le _
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (w - k) * w.descFactorial k * (n ^ k * n)
        = (w.descFactorial k * n ^ k) * ((w - k) * n) := by ring
      _ ≤ (w ^ k * n.descFactorial k) * (w * (n - k)) := Nat.mul_le_mul ih hstep
      _ = w ^ k * w * ((n - k) * n.descFactorial k) := by ring

/-- **Probability bound.** `#{σ | σ(A) ⊆ W} * n^a ≤ w^a * n!`. -/
theorem card_perm_mapsTo_le (A W : Finset α) :
    #(univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ W) * (Fintype.card α) ^ #A ≤
      (#W) ^ #A * (Fintype.card α).factorial := by
  set n := Fintype.card α
  set N := #(univ.filter fun σ : Equiv.Perm α => ∀ x ∈ A, σ x ∈ W)
  have hA : #A ≤ n := card_le_univ A
  have hWn : #W ≤ n := card_le_univ W
  have hpos : 0 < n.descFactorial #A := Nat.descFactorial_pos.mpr hA
  have hex := card_perm_mapsTo_mul A W
  have hr := descFactorial_mul_pow_le hWn #A
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc N * n ^ #A * n.descFactorial #A = (N * n.descFactorial #A) * n ^ #A := by ring
    _ = (#W).descFactorial #A * n.factorial * n ^ #A := by rw [hex]
    _ = ((#W).descFactorial #A * n ^ #A) * n.factorial := by ring
    _ ≤ ((#W) ^ #A * n.descFactorial #A) * n.factorial := Nat.mul_le_mul_right _ hr
    _ = (#W) ^ #A * n.factorial * n.descFactorial #A := by ring

/-- `d` independent permutations. -/
theorem card_pi_perm_mapsTo (d : ℕ) (P : Equiv.Perm α → Prop) [DecidablePred P] :
    #(univ.filter fun φ : Fin d → Equiv.Perm α => ∀ i, P (φ i)) =
      #(univ.filter P) ^ d := by
  rw [← Fintype.card_piFinset_const]
  congr 1
  ext φ
  simp [Fintype.mem_piFinset]

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.card_perm_mapsTo_mul
#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.card_perm_mapsTo_le
#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.card_pi_perm_mapsTo
