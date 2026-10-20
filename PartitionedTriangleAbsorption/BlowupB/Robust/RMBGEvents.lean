/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Robust.PermCount
public import PartitionedTriangleAbsorption.BlowupB.Robust.RMBGHall

@[expose] public section

/-!
# Robustly matchable bipartite graphs: bad events and their sizes

A configuration that is not `Good` lies in one of three explicit families of "bad events"
(`mem_bad1_of_not_P1`, `mem_bad3_of_not_P3`, `mem_bad4_of_not_P4`), whose sizes are bounded by
the permutation count of `Robust.PermCount` (`card_E1_le`, `card_E3_le`, `card_E4_le`), all in `ℕ`:

* `E1 A W`: every `φᵢ` maps `A` into `W`;
* `E3 C W`: every `ψᵢ⁻¹` maps `C` into `W`;
* `E4 A1 A2 C`: no `φᵢ`-edge from `A1` and no `ψᵢ`-edge from `A2` hits `C`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

open Finset

variable {d m : ℕ}

def E1 (d m : ℕ) (A W : Finset (Fin (m + m))) : Finset (Conf d m) :=
  univ.filter fun c => ∀ i, ∀ x ∈ A, c.1 i x ∈ W

def E3 (d m : ℕ) (C W : Finset (Fin (m + m))) : Finset (Conf d m) :=
  univ.filter fun c => ∀ i, ∀ z ∈ C, (c.2 i).symm z ∈ W

/-- The two copies of a set of `Y`. -/
def dup (U : Finset (Fin m)) : Finset (Fin (m + m)) := U.image yl ∪ U.image yr

theorem card_dup (U : Finset (Fin m)) : #(dup U) = 2 * #U := by
  unfold dup
  rw [card_union_of_disjoint, card_image_of_injective _ yl_inj, card_image_of_injective _ yr_inj]
  · ring
  · rw [disjoint_left]
    intro z h1 h2
    obtain ⟨y, -, rfl⟩ := mem_image.mp h1
    obtain ⟨y', -, h⟩ := mem_image.mp h2
    exact yl_ne_yr y y' h.symm

def E4 (d m : ℕ) (A1 : Finset (Fin (m + m))) (A2 : Finset (Fin m)) (C : Finset (Fin (m + m))) :
    Finset (Conf d m) :=
  univ.filter fun c => (∀ i, ∀ x ∈ A1, c.1 i x ∈ univ \ C) ∧ (∀ i, ∀ w ∈ dup A2, c.2 i w ∈ univ \ C)

/-! ### Non-good configurations lie in bad events -/

theorem every_yl_or_yr (w : Fin (m + m)) : ∃ y, w = yl y ∨ w = yr y := by
  rcases h : finSumFinEquiv.symm w with y | y
  · exact ⟨y, Or.inl (by unfold yl; rw [← h]; simp)⟩
  · exact ⟨y, Or.inr (by unfold yr; rw [← h]; simp)⟩

theorem mem_bad1_of_not_P1 (c : Conf d m) (h : ¬ P1 c) :
    ∃ A W : Finset (Fin (m + m)), 1 ≤ #A ∧ 10 * #A ≤ m ∧ #W = 2 * #A - 1 ∧ c ∈ E1 d m A W := by
  classical
  unfold P1 at h
  push Not at h
  obtain ⟨A, hA1, hA10, hlt⟩ := h
  have hle : 2 * #A - 1 ≤ #(univ : Finset (Fin (m + m))) := by
    rw [card_univ, Fintype.card_fin]; omega
  obtain ⟨W, hNW, -, hW⟩ := exists_subsuperset_card_eq (subset_univ (A.biUnion (NX c)))
    (by omega) hle
  refine ⟨A, W, hA1, hA10, hW, ?_⟩
  simp only [E1, mem_filter, mem_univ, true_and]
  intro i x hx
  exact hNW (mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)

theorem mem_bad3_of_not_P3 (c : Conf d m) (h : ¬ P3 c) :
    ∃ (C : Finset (Fin (m + m))) (U : Finset (Fin m)), 1 ≤ #C ∧ 10 * #C ≤ m ∧ #U = #C - 1 ∧
      c ∈ E3 d m C (dup U) := by
  classical
  unfold P3 at h
  push Not at h
  obtain ⟨C, hC1, hC10, hlt⟩ := h
  have hle : #C - 1 ≤ #(univ : Finset (Fin m)) := by rw [card_univ, Fintype.card_fin]; omega
  obtain ⟨U, hNU, -, hU⟩ := exists_subsuperset_card_eq (subset_univ (NYinv c C)) (by omega) hle
  refine ⟨C, U, hC1, hC10, hU, ?_⟩
  simp only [E3, mem_filter, mem_univ, true_and]
  intro i z hz
  obtain ⟨y, hy | hy⟩ := every_yl_or_yr ((c.2 i).symm z)
  · have hyN : y ∈ NYinv c C := mem_filter.mpr ⟨mem_univ _, z, hz,
      mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, by rw [← hy]; simp⟩)⟩
    rw [hy]; exact mem_union_left _ (mem_image.mpr ⟨y, hNU hyN, rfl⟩)
  · have hyN : y ∈ NYinv c C := mem_filter.mpr ⟨mem_univ _, z, hz,
      mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, by rw [← hy]; simp⟩)⟩
    rw [hy]; exact mem_union_right _ (mem_image.mpr ⟨y, hNU hyN, rfl⟩)

theorem mem_bad4_of_not_P4 (c : Conf d m) (h : ¬ P4 c) :
    ∃ (A1 : Finset (Fin (m + m))) (A2 : Finset (Fin m)) (C : Finset (Fin (m + m))),
      m ≤ 10 * (#A1 + #A2) ∧ m ≤ 10 * #C ∧ c ∈ E4 d m A1 A2 C := by
  classical
  unfold P4 at h
  push Not at h
  obtain ⟨A1, A2, C, h1, h2, hno1, hno2⟩ := h
  refine ⟨A1, A2, C, h1, h2, ?_⟩
  simp only [E4, mem_filter, mem_univ, true_and]
  refine ⟨fun i x hx => mem_sdiff.mpr ⟨mem_univ _, fun hz =>
    hno1 x hx _ hz (mem_image.mpr ⟨i, mem_univ _, rfl⟩)⟩, fun i w hw => ?_⟩
  refine mem_sdiff.mpr ⟨mem_univ _, fun hz => ?_⟩
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
    exact hno2 y hy _ hz (mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
    exact hno2 y hy _ hz (mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩))

/-! ### Sizes -/

theorem card_conf : Fintype.card (Conf d m) = ((m + m).factorial ^ d) ^ 2 := by
  simp [Conf, Fintype.card_prod, Fintype.card_pi, Fintype.card_perm, sq]

/-- `d`-fold product of the permutation bound. -/
theorem card_pi_mapsTo_le (A W : Finset (Fin (m + m))) :
    #(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ x ∈ A, φ i x ∈ W) *
      (m + m) ^ (#A * d) ≤ (#W) ^ (#A * d) * (m + m).factorial ^ d := by
  rw [card_pi_perm_mapsTo d (fun σ => ∀ x ∈ A, σ x ∈ W)]
  have h := card_perm_mapsTo_le A W
  simp only [Fintype.card_fin] at h
  calc #(univ.filter fun σ : Equiv.Perm (Fin (m + m)) => ∀ x ∈ A, σ x ∈ W) ^ d * (m + m) ^ (#A * d)
      = (#(univ.filter fun σ : Equiv.Perm (Fin (m + m)) => ∀ x ∈ A, σ x ∈ W) * (m + m) ^ #A) ^ d := by
        rw [mul_pow, ← pow_mul, mul_comm #A d]
    _ ≤ ((#W) ^ #A * (m + m).factorial) ^ d := by convert Nat.pow_le_pow_left h d using 4; ext σ; simp
    _ = (#W) ^ (#A * d) * (m + m).factorial ^ d := by rw [mul_pow, ← pow_mul]

theorem card_E1_le (A W : Finset (Fin (m + m))) :
    #(E1 d m A W) * (m + m) ^ (#A * d) ≤ (#W) ^ (#A * d) * ((m + m).factorial ^ d) ^ 2 := by
  have hE : E1 d m A W = (univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) =>
      ∀ i, ∀ x ∈ A, φ i x ∈ W) ×ˢ (univ : Finset (Fin d → Equiv.Perm (Fin (m + m)))) := by
    ext c; simp [E1]
  rw [hE, card_product, card_univ]
  have h := card_pi_mapsTo_le (d := d) A W
  have hψ : Fintype.card (Fin d → Equiv.Perm (Fin (m + m))) = (m + m).factorial ^ d := by
    simp [Fintype.card_pi, Fintype.card_perm]
  rw [hψ]
  calc _ = (#(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ x ∈ A, φ i x ∈ W) *
        (m + m) ^ (#A * d)) * (m + m).factorial ^ d := by ring
    _ ≤ ((#W) ^ (#A * d) * (m + m).factorial ^ d) * (m + m).factorial ^ d := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem card_inv_mapsTo (C W : Finset (Fin (m + m))) :
    #(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ z ∈ C, (φ i).symm z ∈ W) =
      #(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ z ∈ C, φ i z ∈ W) := by
  refine card_bij (fun φ _ => fun i => (φ i).symm) ?_ ?_ ?_
  · intro φ hφ; simpa using hφ
  · intro φ₁ _ φ₂ _ h
    funext i
    have := congrFun h i
    exact Equiv.symm_bijective.injective this
  · intro ψ hψ
    refine ⟨fun i => (ψ i).symm, by simpa using hψ, ?_⟩
    funext i; simp

theorem card_E3_le (C W : Finset (Fin (m + m))) :
    #(E3 d m C W) * (m + m) ^ (#C * d) ≤ (#W) ^ (#C * d) * ((m + m).factorial ^ d) ^ 2 := by
  have hE : E3 d m C W = (univ : Finset (Fin d → Equiv.Perm (Fin (m + m)))) ×ˢ
      (univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ z ∈ C, (φ i).symm z ∈ W) := by
    ext c; simp [E3]
  rw [hE, card_product, card_univ, card_inv_mapsTo]
  have h := card_pi_mapsTo_le (d := d) C W
  have hψ : Fintype.card (Fin d → Equiv.Perm (Fin (m + m))) = (m + m).factorial ^ d := by
    simp [Fintype.card_pi, Fintype.card_perm]
  rw [hψ]
  calc _ = (#(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ x ∈ C, φ i x ∈ W) *
        (m + m) ^ (#C * d)) * (m + m).factorial ^ d := by ring
    _ ≤ ((#W) ^ (#C * d) * (m + m).factorial ^ d) * (m + m).factorial ^ d := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem card_E4_le (A1 : Finset (Fin (m + m))) (A2 : Finset (Fin m)) (C : Finset (Fin (m + m))) :
    #(E4 d m A1 A2 C) * ((m + m) ^ (#A1 * d) * (m + m) ^ (#(dup A2) * d)) ≤
      ((m + m - #C) ^ (#A1 * d) * (m + m - #C) ^ (#(dup A2) * d)) * ((m + m).factorial ^ d) ^ 2 := by
  have hE : E4 d m A1 A2 C =
      (univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ x ∈ A1, φ i x ∈ univ \ C) ×ˢ
      (univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ w ∈ dup A2, φ i w ∈ univ \ C) := by
    ext c; simp [E4]
  have hc : #(univ \ C) = m + m - #C := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  rw [hE, card_product]
  have h1 := card_pi_mapsTo_le (d := d) A1 (univ \ C)
  have h2 := card_pi_mapsTo_le (d := d) (dup A2) (univ \ C)
  rw [hc] at h1 h2
  calc _ = (#(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) => ∀ i, ∀ x ∈ A1, φ i x ∈ univ \ C) *
        (m + m) ^ (#A1 * d)) * (#(univ.filter fun φ : Fin d → Equiv.Perm (Fin (m + m)) =>
          ∀ i, ∀ w ∈ dup A2, φ i w ∈ univ \ C) * (m + m) ^ (#(dup A2) * d)) := by ring
    _ ≤ ((m + m - #C) ^ (#A1 * d) * (m + m).factorial ^ d) *
        ((m + m - #C) ^ (#(dup A2) * d) * (m + m).factorial ^ d) := Nat.mul_le_mul h1 h2
    _ = _ := by ring

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.mem_bad3_of_not_P3
#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.card_E4_le
