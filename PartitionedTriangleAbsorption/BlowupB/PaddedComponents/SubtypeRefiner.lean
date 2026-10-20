/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.Split
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LocalPaths
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Universal
public import PartitionedTriangleAbsorption.ColouredHub.Lattice

@[expose] public section

/-!
# The ordinary refiner inside one component (virtual edges inside the component)

For a component label `k`, let `W = {v // c (p v) = k}` be the vertices of the classes of
component `k`. The ordinary refiner `exists_universal_refiner_alpha` is run in the COMPLETE graph on
`W` (any two vertices of `W` have `|W| - 2` common neighbours there), with the reserve `X` pulled
back to `W`, and the result is pushed forward to `V` along the inclusion. The scales are rescaled
by `n / |W|`, so that the degree and incidence bounds are the same as for a refiner on `V`:

* virtual edges `R` inside component `k`, disjoint from `X`, of maximum degree `≤ 4 λ n`;
* `Even3` pieces of at most `42` edges, at most `1224 ρ n²` of them, with incidence `≤ 4096 λ n`;
* every `Even3` leftover `L ⊆ X` is partitioned, together with `R`, by disjoint pieces.

The only extra hypothesis is `64 λ n ≤ |W|`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

variable {V : Type} [Fintype V] [DecidableEq V]

theorem incidentLoad_image_le (f : W → V) (hf : Function.Injective f) [DecidableEq W]
    (E : Finset (Sym2 W)) (d : ℝ) (hd : 0 ≤ d) (hE : ∀ w, (incidentLoad E w : ℝ) ≤ d) (v : V) :
    (incidentLoad (E.image (Sym2.map f)) v : ℝ) ≤ d := by
  by_cases hv : ∃ w, f w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [ColouredHub.incidentLoad_image_apply f hf E w]
    exact hE w
  · push Not at hv
    rw [ColouredHub.incidentLoad_image_of_notMem f E v hv]
    simpa using hd

/-- **The ordinary refiner inside one component.** -/
theorem exists_component_refiner (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4)
    (lam rho : ℝ) (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ))
    (X : Finset (Sym2 V)) (hXin : ∀ e ∈ X, InsideE p c k e) (hXloop : ∀ e ∈ X, ¬ e.IsDiag)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3))
      (P : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      (∀ e ∈ R, InsideE p c k e ∧ ¬ e.IsDiag) ∧ Disjoint R X ∧
      (∀ L ⊆ X, OnePart.Even3 L → ∃ s ⊆ indices,
        (s : Set (ℕ × Bool × Fin 3 × Fin 3)).PairwiseDisjoint P ∧ s.biUnion P = R ∪ L) ∧
      (∀ j ∈ indices, P j ⊆ X ∪ R ∧ OnePart.Even3 (P j) ∧ (P j).card ≤ 42) ∧
      DegBounded R (4 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  classical
  set W := {v // c (p v) = k}
  let f : W → V := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set m : ℝ := (Fintype.card W : ℝ) with hm
  have hn0 : 0 < n := by
    by_contra h
    have : n ≤ 0 := le_of_not_gt h
    nlinarith
  have hmn : m ≤ n := by
    rw [hm, hn]; exact_mod_cast Fintype.card_subtype_le _
  have hm0 : 0 < m := by nlinarith
  set lamW : ℝ := lam * n / m with hlamW
  set rhoW : ℝ := rho * n / m with hrhoW
  have hlamWm : lamW * m = lam * n := by rw [hlamW]; field_simp
  have hrhoWm : rhoW * m = rho * n := by rw [hrhoW]; field_simp
  have hlamW0 : 0 < lamW := by positivity
  have hrhoW0 : 0 < rhoW := by positivity
  have hlamW64 : lamW ≤ 1 / 64 := by
    rw [hlamW, div_le_iff₀ hm0]; linarith
  have hscaleW : 2 ^ 24 * rhoW ≤ lamW ^ 2 := by
    rw [hlamW, hrhoW, div_pow, le_div_iff₀ (by positivity)]
    have h1 : 2 ^ 24 * (rho * n / m) * m ^ 2 = (2 ^ 24 * rho) * (n * m) := by
      field_simp
    rw [h1]
    have h2 : (2 ^ 24 * rho) * (n * m) ≤ lam ^ 2 * (n * m) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    have h3 : lam ^ 2 * (n * m) ≤ lam ^ 2 * (n * n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmn hn0.le) (sq_nonneg _)
    nlinarith
  have hn1W : 1 ≤ rhoW * Fintype.card W := by rw [← hm, hrhoWm]; exact hn1
  have hn2W : 256 ≤ lamW * Fintype.card W := by rw [← hm, hlamWm]; exact hn2
  have hW4 : 4 ≤ Fintype.card W := by
    have : (4 : ℝ) ≤ (Fintype.card W : ℝ) := by rw [← hm]; nlinarith
    exact_mod_cast this
  -- the pulled-back reserve
  let XW : Finset (Sym2 W) := univ.filter fun e => Sym2.map f e ∈ X
  have hpull : ∀ E ⊆ X, (univ.filter fun e : Sym2 W => Sym2.map f e ∈ E).image (Sym2.map f) = E := by
    intro E hE
    ext e
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e', he', rfl⟩; exact he'
    · intro he
      have hin := hXin e (hE he)
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb⟩ := (insideE_mk p c k a b).mp hin
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa [f] using he, by simp [f]⟩
  have hXW : XW.image (Sym2.map f) = X := hpull X subset_rfl
  have hloopW : ∀ E : Finset (Sym2 W), (∀ e ∈ E.image (Sym2.map f), ¬ e.IsDiag) →
      ∀ e ∈ E, ¬ e.IsDiag := by
    intro E hE e he hd
    exact hE _ (mem_image_of_mem _ he) (Sym2.IsDiag.map hd)
  have hXWloop : ∀ e ∈ XW, ¬ e.IsDiag := hloopW XW (by rw [hXW]; exact hXloop)
  have hXWtop : XW ⊆ (⊤ : SimpleGraph W).edgeFinset := by
    intro e he
    have hnd := hXWloop e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      intro hab; exact hnd (by simp [hab])
  have hXWdeg : DegBounded XW (2 * rhoW * Fintype.card W) := by
    intro w
    change (incidentLoad XW w : ℝ) ≤ _
    rw [← ColouredHub.incidentLoad_image_apply f hf XW w, hXW, ← hm,
      show 2 * rhoW * m = 2 * (rhoW * m) by ring, hrhoWm]
    have := hX (f w)
    change (incidentLoad X (f w) : ℝ) ≤ _ at this
    linarith
  obtain ⟨indices, P, R, hRtop, hRX, href, hpieces, hRdeg, hcardI, hinc⟩ :=
    exists_universal_refiner_alpha (⊤ : SimpleGraph W) XW hXWtop lamW rhoW hlamW0 hlamW64
      hrhoW0 hscaleW hn1W hn2W hXWdeg (1 / 2) (by linarith) (antiEdgeful_top hW4)
  have hRloop : ∀ e ∈ R, ¬ e.IsDiag := fun e he =>
    (⊤ : SimpleGraph W).not_isDiag_of_mem_edgeFinset (hRtop he)
  have himg_inside : ∀ E : Finset (Sym2 W), ∀ e ∈ E.image (Sym2.map f), InsideE p c k e := by
    intro E e he
    obtain ⟨e', -, rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ a b => exact (insideE_mk p c k _ _).mpr ⟨a.2, b.2⟩
  have hinj := Sym2.map.injective hf
  refine ⟨indices, fun j => (P j).image (Sym2.map f), R.image (Sym2.map f), fun e he =>
    ⟨himg_inside R e he, loopless_image f hf R hRloop e he⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hXW]; exact (disjoint_image hinj).mpr hRX
  · intro L hL h3
    set LW : Finset (Sym2 W) := univ.filter fun e => Sym2.map f e ∈ L with hLW
    have hLWimg : LW.image (Sym2.map f) = L := hpull L hL
    have hLWX : LW ⊆ XW := by
      intro e he
      simp only [LW, XW, mem_filter, mem_univ, true_and] at he ⊢
      exact hL he
    have hLWloop : ∀ e ∈ LW, ¬ e.IsDiag := fun e he => hXWloop e (hLWX he)
    have hLW3 : OnePart.Even3 LW := by
      refine ⟨?_, fun w => ?_⟩
      · have : LW.card = L.card := by rw [← hLWimg, card_image_of_injective _ hinj]
        rw [this]; exact h3.1
      · rw [← ColouredHub.incidentLoad_image_apply f hf LW w, hLWimg]
        exact h3.2 (f w)
    obtain ⟨s, hs, hsdis, hsU⟩ := href LW hLWX ((OnePart.isIntDiv_part1_iff LW hLWloop).mpr hLW3)
    refine ⟨s, hs, ?_, ?_⟩
    · intro i hi j hj hij
      exact (disjoint_image hinj).mpr (hsdis hi hj hij)
    · have hbu : s.biUnion (fun j => (P j).image (Sym2.map f)) =
          (s.biUnion P).image (Sym2.map f) := by
        ext e
        simp only [mem_biUnion, mem_image]
        constructor
        · rintro ⟨j, hj, e', he', rfl⟩; exact ⟨e', ⟨j, hj, he'⟩, rfl⟩
        · rintro ⟨e', ⟨j, hj, he'⟩, rfl⟩; exact ⟨j, hj, e', he', rfl⟩
      rw [hbu, hsU, image_union, hLWimg]
  · intro j hj
    obtain ⟨hPsub, hPloop, hPeven, hP3, hP42⟩ := hpieces j hj
    refine ⟨?_, ⟨?_, even_image f hf (P j) hPeven⟩, ?_⟩
    · intro e he
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      rcases mem_union.mp (hPsub he') with h | h
      · exact mem_union_left _ (hXW ▸ mem_image_of_mem _ h)
      · exact mem_union_right _ (mem_image_of_mem _ h)
    · rw [card_image_of_injective _ hinj]; exact hP3
    · rw [card_image_of_injective _ hinj]; exact hP42
  · intro v
    change (incidentLoad (R.image (Sym2.map f)) v : ℝ) ≤ _
    refine incidentLoad_image_le f hf R _ (by positivity) (fun w => ?_) v
    have := hRdeg w
    change (incidentLoad R w : ℝ) ≤ 4 * lamW * Fintype.card W at this
    rw [← hm, show 4 * lamW * m = 4 * (lamW * m) by ring, hlamWm] at this
    linarith
  · have : 1224 * rhoW * (Fintype.card W : ℝ) ^ 2 = 1224 * (rho * n) * m := by
      rw [← hm, show 1224 * rhoW * m ^ 2 = 1224 * (rhoW * m) * m by ring, hrhoWm]
    rw [this] at hcardI
    have h2 : 1224 * (rho * n) * m ≤ 1224 * (rho * n) * n :=
      mul_le_mul_of_nonneg_left hmn (by positivity)
    nlinarith
  · intro v
    by_cases hv : ∃ w, f w = v
    · obtain ⟨w, rfl⟩ := hv
      simp only [ColouredHub.incidentLoad_image_apply f hf]
      have := hinc w
      rw [← hm, show 4096 * lamW * m = 4096 * (lamW * m) by ring, hlamWm] at this
      linarith
    · push Not at hv
      simp only [ColouredHub.incidentLoad_image_of_notMem f _ v hv, sum_const_zero,
        Nat.cast_zero]
      positivity

end PaddedComponents

#print axioms PaddedComponents.exists_component_refiner
