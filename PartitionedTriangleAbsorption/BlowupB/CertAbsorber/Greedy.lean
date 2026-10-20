/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairMoveSelectionStage85

/-! # Ranked greedy embedding from the compatible four-root supply

A finite set `X` of new vertices is embedded injectively into a host `G`, avoiding a forbidden
vertex set `Z` and a blocked edge set `B` of bounded degree.  Each new vertex `x` has a label,
a set of fixed host roots `roots x` and a set of earlier new vertices `back x` (of strictly
smaller rank) to which it must be adjacent, with at most four demands in total.  Each choice
is made by the existing selector `PairMoveSelectionStage85.exists_fresh`, which consumes the
verifiable premise `CompatibleSupply p F G a` (four-root typed common neighbourhoods).
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.PairMoveSelectionStage85
  PartitionedTriangleAbsorption.TypedTransformer

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The required properties of the image of one new vertex. -/
def GoodAt {X : Type*} (p : V → Fin t) (G : SimpleGraph V) (B : Finset (Sym2 V)) (Z : Finset V)
    (lab : X → Fin t) (roots : X → Finset V) (back : X → Finset X) (φ : X → V) (x : X) : Prop :=
  p (φ x) = lab x ∧ φ x ∉ Z ∧ (∀ v ∈ roots x, G.Adj v (φ x) ∧ s(v, φ x) ∉ B) ∧
    ∀ y ∈ back x, G.Adj (φ y) (φ x) ∧ s(φ y, φ x) ∉ B

/-- **Ranked greedy embedding.** -/
theorem greedy_embedding {X : Type*} [Fintype X] [DecidableEq X]
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hs : CompatibleSupply p F G a) (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (hd : 0 ≤ d) (Z : Finset V)
    (lab : X → Fin t) (roots : X → Finset V) (back : X → Finset X) (rk : X → ℕ)
    (hrk : ∀ x, ∀ y ∈ back x, rk y < rk x)
    (hcard : ∀ x, (roots x).card + (back x).card ≤ 4)
    (hroots : ∀ x, ∀ v ∈ roots x, ∃ k, Link F (lab x) (p v) k)
    (hback : ∀ x, ∀ y ∈ back x, ∃ k, Link F (lab x) (lab y) k)
    (hbud : (Z.card : ℝ) + Fintype.card X + 4 * d < a) :
    ∃ φ : X → V, Function.Injective φ ∧ ∀ x, GoodAt p G B Z lab roots back φ x := by
  classical
  -- a default host vertex (only needed when `X` is nonempty)
  by_cases hX : IsEmpty X
  · exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  rw [not_isEmpty_iff] at hX
  obtain ⟨x0⟩ := hX
  have hcomp0 : Compatible p F (∅ : Finset V) (lab x0) := fun v hv => absurd hv (by simp)
  have hX0 : (0 : ℝ) ≤ Fintype.card X := by positivity
  obtain ⟨v0, -⟩ := exists_fresh p F G a d hs ∅ Z (lab x0) (by simp) hcomp0 B hB hd
    (by linarith)
  -- induction on downward-closed sets
  have key : ∀ n : ℕ, ∀ T : Finset X, T.card = n → (∀ x ∈ T, back x ⊆ T) →
      ∃ φ : X → V, Set.InjOn φ T ∧ ∀ x ∈ T, GoodAt p G B Z lab roots back φ x := by
    intro n
    induction n with
    | zero =>
      intro T hT _
      rw [card_eq_zero] at hT
      subst hT
      exact ⟨fun _ => v0, by simp, by simp⟩
    | succ n ih =>
      intro T hT hclosed
      have hne : T.Nonempty := card_pos.mp (by omega)
      obtain ⟨x, hxT, hxmax⟩ := exists_max_image T rk hne
      set T' := T.erase x with hT'
      have hback' : ∀ y ∈ back x, y ∈ T' := fun y hy =>
        mem_erase.mpr ⟨fun h => by have := hrk x y hy; rw [h] at this; omega, hclosed x hxT hy⟩
      have hclosed' : ∀ y ∈ T', back y ⊆ T' := by
        intro y hy z hz
        have hyT := mem_of_mem_erase hy
        refine mem_erase.mpr ⟨fun h => ?_, hclosed y hyT hz⟩
        have h1 := hrk y z hz
        have h2 := hxmax y hyT
        rw [h] at h1; omega
      obtain ⟨φ, hinj, hgood⟩ := ih T' (by rw [card_erase_of_mem hxT]; omega) hclosed'
      -- choose the image of `x`
      set S : Finset V := roots x ∪ (back x).image φ with hS
      have hScard : S.card ≤ 4 :=
        (card_union_le _ _).trans ((Nat.add_le_add_left card_image_le _).trans (hcard x))
      have hScomp : Compatible p F S (lab x) := by
        intro v hv
        rcases mem_union.mp hv with hv | hv
        · exact hroots x v hv
        · obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
          rw [(hgood y (hback' y hy)).1]
          exact hback x y hy
      set Z' := Z ∪ T'.image φ with hZ'
      have hZ'card : (Z'.card : ℝ) + 4 * d < a := by
        have h1 : Z'.card ≤ Z.card + T'.card :=
          (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
        have h2 : T'.card ≤ Fintype.card X := card_le_univ _
        have h3 : (Z'.card : ℝ) ≤ Z.card + Fintype.card X := by exact_mod_cast h1.trans (by omega)
        linarith
      obtain ⟨w, hwlab, hwadj, hwZ, hwB⟩ :=
        exists_fresh p F G a d hs S Z' (lab x) hScard hScomp B hB hd hZ'card
      have hwZ0 : w ∉ Z := fun h => hwZ (mem_union.mpr (Or.inl h))
      have hwT' : ∀ y ∈ T', φ y ≠ w := fun y hy h =>
        hwZ (mem_union.mpr (Or.inr (mem_image.mpr ⟨y, hy, h⟩)))
      refine ⟨Function.update φ x w, ?_, ?_⟩
      · intro y hy z hz hyz
        have hyz' : (Function.update φ x w) y = (Function.update φ x w) z := hyz
        by_cases hyx : y = x
        · by_cases hzx : z = x
          · rw [hyx, hzx]
          · subst hyx
            have hzT' : z ∈ T' := mem_erase.mpr ⟨hzx, hz⟩
            rw [Function.update_self, Function.update_of_ne hzx] at hyz'
            exact absurd hyz'.symm (hwT' z hzT')
        · by_cases hzx : z = x
          · subst hzx
            have hyT' : y ∈ T' := mem_erase.mpr ⟨hyx, hy⟩
            rw [Function.update_self, Function.update_of_ne hyx] at hyz'
            exact absurd hyz' (hwT' y hyT')
          · rw [Function.update_of_ne hyx, Function.update_of_ne hzx] at hyz'
            exact hinj (mem_erase.mpr ⟨hyx, hy⟩) (mem_erase.mpr ⟨hzx, hz⟩) hyz'
      · intro y hy
        by_cases hyx : y = x
        · subst hyx
          refine ⟨by simpa using hwlab, by simpa using hwZ0, ?_, ?_⟩
          · intro v hv
            simp only [Function.update_self]
            exact ⟨hwadj v (mem_union.mpr (Or.inl hv)), hwB v (mem_union.mpr (Or.inl hv))⟩
          · intro z hz
            have hzx : z ≠ y := fun h => by have := hrk y z hz; rw [h] at this; omega
            simp only [Function.update_self, Function.update_of_ne hzx]
            have hmem : φ z ∈ S := mem_union.mpr (Or.inr (mem_image.mpr ⟨z, hz, rfl⟩))
            exact ⟨hwadj _ hmem, hwB _ hmem⟩
        · have hyT' : y ∈ T' := mem_erase.mpr ⟨hyx, hy⟩
          obtain ⟨h1, h2, h3, h4⟩ := hgood y hyT'
          refine ⟨by rwa [Function.update_of_ne hyx], by rwa [Function.update_of_ne hyx], ?_, ?_⟩
          · intro v hv
            rw [Function.update_of_ne hyx]
            exact h3 v hv
          · intro z hz
            have hzx : z ≠ x := fun h => (mem_erase.mp (hclosed' y hyT' hz)).1 h
            rw [Function.update_of_ne hyx, Function.update_of_ne hzx]
            exact h4 z hz
  obtain ⟨φ, hinj, hgood⟩ := key _ univ rfl (fun _ _ => subset_univ _)
  exact ⟨φ, fun y z h => hinj (mem_univ y) (mem_univ z) h, fun x => hgood x (mem_univ x)⟩

end PaperII.CertAbsorber
