/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.CutHub
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Filling
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoscopicSpec
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The mesoscopic producer on the cut-partition class, with an explicit fixed library

This file proves the conclusion of `MesoscopicRefinerWith C 12` (`MesoscopicSpec.lean`),
**with the actual interface**: a fixed reserve `R`, a fixed library `lib` of nonempty balanced
pieces of size `≤ 12` lying in `R ∪ Y`, `lib.card ≤ C |Y|`, catalogue edge-incidence load
`(∑_{P ∈ lib} deg_P v)^2 ≤ C^2 |Y|` at every vertex, and an exact positive multiplicity-free
partition of `R ∪ L` by a subfamily of `lib` for every balanced `L ⊆ Y` (including `L = ∅`).

It does so for every cyclically tripartite `Y` of maximum degree `≤ 17` in the class
`MesoCutClass B`: `Y` has a vertex partition `p` satisfying the cut hypothesis
`CutHub.CutPartition` such that

* every part has arc load at most `B √|Y|` (stated as `load_a ^ 2 ≤ B ^ 2 |Y|`), and
* between two different parts there are at most `B` arcs in each direction.

The constant is `C = mesoConst B` and `K = 12`.  The reserve is the distributed-hub reserve of
`CutHub.lean`; the library is

* the triangles `Tcyc e` and the basal pieces `Ccyc e` (`e ∈ Y`),
* the transition cycles `Dcyc e f` for every pair of arcs `e, f ∈ Y` with `e.2 = f.1`,
* the connector pairs `Pcyc x y` for every crossing arc `x` and every arc `y` going back between
  the same two parts.

This class is strictly larger than `CutShortenable` (bounded parts): parts may have up to
`B √|Y|` arcs, e.g. `Y` may be a disjoint union of arbitrary (expander) blocks of `√|Y|` arcs
each (`mesoCutClass_of_blocks`).  It does **not** contain all `Y`: a general `Y` (e.g. a single
bounded-degree expander) has no such partition.  `MesoscopicRefiner` itself remains open.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace MesoCutHub

open CutHub
open Hub (ne_of_cyc deg_biUnion)

section Library

variable {V P : Type*} [DecidableEq V] [DecidableEq P]
variable (c : V → ZMod 3) (p : V → P)

/-- Pairs of arcs `(e, f)` of `Y` meeting head-to-tail (`e.2 = f.1`). -/
def dPairs (Y : Finset (V × V)) : Finset ((V × V) × (V × V)) :=
  (Y ×ˢ Y).filter (fun ef => ef.1.2 = ef.2.1)

/-- Pairs `(x, y)` of arcs of `Y` with `x` crossing from part `a` to part `b ≠ a` and `y` going
back from part `b` to part `a`. -/
def pPairs (Y : Finset (V × V)) : Finset ((V × V) × (V × V)) :=
  (Y ×ˢ Y).filter (fun xy => p xy.1.1 ≠ p xy.1.2 ∧ p xy.2.1 = p xy.1.2 ∧ p xy.2.2 = p xy.1.1)

/-- **The fixed library** (chosen before the demand). -/
def lib (Y : Finset (V × V)) : Finset (Finset (CV V P × CV V P)) :=
  Y.image Tcyc ∪ Y.image (Ccyc c p) ∪ (dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2) ∪
    (pPairs p Y).image (fun xy => Pcyc p xy.1 xy.2)

end Library

/-! ### Elementary degree facts -/

section DegFacts

variable {W : Type*} [DecidableEq W]

lemma deg_mono {E F : Finset (W × W)} (h : E ⊆ F) (v : W) : deg E v ≤ deg F v := by
  unfold deg inDeg outDeg
  exact Nat.add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ h))
    (Finset.card_le_card (Finset.filter_subset_filter _ h))

lemma deg_union_le (E F : Finset (W × W)) (v : W) : deg (E ∪ F) v ≤ deg E v + deg F v := by
  unfold deg inDeg outDeg
  rw [Finset.filter_union, Finset.filter_union]
  have h1 := Finset.card_union_le (E.filter (fun e => e.2 = v)) (F.filter (fun e => e.2 = v))
  have h2 := Finset.card_union_le (E.filter (fun e => e.1 = v)) (F.filter (fun e => e.1 = v))
  omega

lemma sum_union_le' {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  omega

lemma sum_image_le' {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (g : ι → κ) (f : κ → ℕ) :
    ∑ x ∈ s.image g, f x ≤ ∑ x ∈ s, f (g x) :=
  Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)

/-- Summing over pairs filtered by a relation, bounded by the maximal fibre size. -/
lemma sum_filter_prod_fst_le {α : Type*} (Y : Finset α) (q : α → α → Prop)
    [∀ a b, Decidable (q a b)] (g : α → ℕ) (d : ℕ)
    (hd : ∀ a ∈ Y, (Y.filter (fun b => q a b)).card ≤ d) :
    ∑ x ∈ (Y ×ˢ Y).filter (fun x => q x.1 x.2), g x.1 ≤ d * ∑ a ∈ Y, g a := by
  rw [Finset.sum_filter, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (hd a ha)

lemma sum_filter_prod_snd_le {α : Type*} (Y : Finset α) (q : α → α → Prop)
    [∀ a b, Decidable (q a b)] (g : α → ℕ) (d : ℕ)
    (hd : ∀ b ∈ Y, (Y.filter (fun a => q a b)).card ≤ d) :
    ∑ x ∈ (Y ×ˢ Y).filter (fun x => q x.1 x.2), g x.2 ≤ d * ∑ a ∈ Y, g a := by
  rw [Finset.sum_filter, Finset.sum_product_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (hd b hb)

lemma card_filter_prod_le {α : Type*} (Y : Finset α) (q : α → α → Prop)
    [∀ a b, Decidable (q a b)] (d : ℕ) (hd : ∀ a ∈ Y, (Y.filter (fun b => q a b)).card ≤ d) :
    ((Y ×ˢ Y).filter (fun x => q x.1 x.2)).card ≤ d * Y.card := by
  have h := sum_filter_prod_fst_le Y q (fun _ => 1) d hd
  simpa using h

end DegFacts

/-! ### Load and count of the library -/

section Bounds

variable {V P : Type*} [DecidableEq V] [DecidableEq P]
variable (c : V → ZMod 3) (p : V → P)

lemma outDeg_le_of_maxDeg {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) (v : V) :
    (Y.filter (fun f => f.1 = v)).card ≤ 17 := by
  have := hdeg v; unfold deg outDeg at this; omega

lemma inDeg_le_of_maxDeg {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) (v : V) :
    (Y.filter (fun f => f.2 = v)).card ≤ 17 := by
  have := hdeg v; unfold deg inDeg at this; omega

lemma card_dPairs_le {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) :
    (dPairs Y).card ≤ 17 * Y.card :=
  card_filter_prod_le Y (fun e f => e.2 = f.1) 17 fun e _ => by
    simpa [eq_comm] using outDeg_le_of_maxDeg hdeg e.2

/-- The multiplicity hypothesis: at most `B` arcs from part `a` to part `b ≠ a`. -/
def MultLE (Y : Finset (V × V)) (B : ℕ) : Prop :=
  ∀ a b, a ≠ b → (Y.filter (fun e => p e.1 = a ∧ p e.2 = b)).card ≤ B

lemma pPairs_fst_fiber {Y : Finset (V × V)} {B : ℕ} (hB : MultLE p Y B) (x : V × V) :
    (Y.filter (fun y => p x.1 ≠ p x.2 ∧ p y.1 = p x.2 ∧ p y.2 = p x.1)).card ≤ B := by
  by_cases hx : p x.1 = p x.2
  · simp [hx]
  · refine le_trans (Finset.card_le_card ?_) (hB (p x.2) (p x.1) (Ne.symm hx))
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.2⟩

lemma pPairs_snd_fiber {Y : Finset (V × V)} {B : ℕ} (hB : MultLE p Y B) (y : V × V) :
    (Y.filter (fun x => p x.1 ≠ p x.2 ∧ p y.1 = p x.2 ∧ p y.2 = p x.1)).card ≤ B := by
  by_cases hy : p y.1 = p y.2
  · refine le_trans (le_of_eq ?_) (Nat.zero_le B)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hx, h1, h2⟩
    exact hx (by rw [← h1, ← h2, hy])
  · refine le_trans (Finset.card_le_card ?_) (hB (p y.2) (p y.1) (Ne.symm hy))
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.2.2.symm, hx.2.2.1.symm⟩

lemma card_pPairs_le {Y : Finset (V × V)} {B : ℕ} (hB : MultLE p Y B) :
    (pPairs p Y).card ≤ B * Y.card :=
  card_filter_prod_le Y (fun x y => p x.1 ≠ p x.2 ∧ p y.1 = p x.2 ∧ p y.2 = p x.1) B
    fun x _ => pPairs_fst_fiber p hB x

/-- **Library count:** `|lib| ≤ (19 + B) |Y|`. -/
theorem card_lib_le {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) {B : ℕ} (hB : MultLE p Y B) :
    (lib c p Y).card ≤ (19 + B) * Y.card := by
  unfold lib
  have h1 := Finset.card_union_le (Y.image Tcyc ∪ Y.image (Ccyc c p) ∪
    (dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2))
    ((pPairs p Y).image (fun xy => Pcyc p xy.1 xy.2))
  have h2 := Finset.card_union_le (Y.image Tcyc ∪ Y.image (Ccyc c p))
    ((dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2))
  have h3 := Finset.card_union_le (Y.image (Tcyc (P := P))) (Y.image (Ccyc c p))
  have i1 := Finset.card_image_le (s := Y) (f := Tcyc (P := P))
  have i2 := Finset.card_image_le (s := Y) (f := Ccyc c p)
  have i3 := Finset.card_image_le (s := dPairs Y) (f := fun ef => Dcyc c p ef.1 ef.2)
  have i4 := Finset.card_image_le (s := pPairs p Y) (f := fun xy => Pcyc p xy.1 xy.2)
  have d1 := card_dPairs_le hdeg
  have d2 := card_pPairs_le p hB
  nlinarith

lemma deg_Tcyc_le (e : V × V) (w : CV V P) :
    deg (Tcyc (P := P) e) w ≤ deg (Ccyc c p e) w + deg {((Sum.inl e.1, Sum.inl e.2) : CV V P × CV V P)} w := by
  have hsub : Tcyc (P := P) e ⊆ Ccyc c p e ∪ {((Sum.inl e.1, Sum.inl e.2) : CV V P × CV V P)} := by
    intro a ha
    simp only [Tcyc, Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ ((mem_Ccyc c p).2 (Or.inl ha))
  exact (deg_mono hsub w).trans (deg_union_le _ _ w)

lemma deg_Dcyc_le (e f : V × V) (w : CV V P) :
    deg (Dcyc c p e f) w ≤ deg (Ccyc c p e) w + deg (Ccyc c p f) w := by
  have hsub : Dcyc c p e f ⊆ Ccyc c p e ∪ Ccyc c p f := by
    intro a ha
    simp only [Dcyc, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact Finset.mem_union_left _ ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inr ha))))
    · exact Finset.mem_union_right _ ((mem_Ccyc c p).2 (Or.inr (Or.inl ha)))
  exact (deg_mono hsub w).trans (deg_union_le _ _ w)

lemma deg_Pcyc_le (x y : V × V) (w : CV V P) :
    deg (Pcyc p x y) w ≤ deg (Ccyc c p x) w + deg (Ccyc c p y) w := by
  have hsub : Pcyc p x y ⊆ Ccyc c p x ∪ Ccyc c p y := by
    intro a ha
    simp only [Pcyc, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact Finset.mem_union_left _ ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha))))
    · exact Finset.mem_union_right _ ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha))))
  exact (deg_mono hsub w).trans (deg_union_le _ _ w)

lemma sum_deg_single_lift (Y : Finset (V × V)) (w : CV V P) :
    ∑ e ∈ Y, deg {((Sum.inl e.1, Sum.inl e.2) : CV V P × CV V P)} w =
      deg (Y.map (liftArc V (P ⊕ ((V × V) × Fin 9)))) w := by
  have hY : Y.map (liftArc V (P ⊕ ((V × V) × Fin 9))) =
      Y.biUnion (fun e => {((Sum.inl e.1, Sum.inl e.2) : CV V P × CV V P)}) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_biUnion, Finset.mem_singleton, liftArc,
      Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩
  rw [hY, deg_biUnion]
  intro i _ j _ hij
  rw [Finset.disjoint_singleton]
  intro h
  simp only [Prod.mk.injEq, Sum.inl.injEq] at h
  exact hij (Prod.ext h.1 h.2)

/-- **Catalogue load of the library, vertex by vertex:**
`∑_{P ∈ lib} deg_P w ≤ (36 + 2B) deg_R w + deg_Y w`. -/
theorem catalogLoad_lib_le {Y : Finset (V × V)} (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17)
    {B : ℕ} (hB : MultLE p Y B) (w : CV V P) :
    catalogLoad (lib c p Y) w ≤
      (36 + 2 * B) * deg (reserve c p Y) w + deg (Y.map (liftArc V (P ⊕ ((V × V) × Fin 9)))) w := by
  have hdisjY : ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → Disjoint (Ccyc c p i) (Ccyc c p j) :=
    fun i _ j _ hij => Ccyc_disjoint c p hij
  have hR : deg (reserve c p Y) w = ∑ e ∈ Y, deg (Ccyc c p e) w := deg_biUnion Y _ hdisjY w
  -- the four classes
  have hT : ∑ q ∈ Y.image (Tcyc (P := P)), deg q w ≤ (∑ e ∈ Y, deg (Ccyc c p e) w) +
      deg (Y.map (liftArc V (P ⊕ ((V × V) × Fin 9)))) w := by
    refine (sum_image_le' _ _ _).trans ?_
    rw [← sum_deg_single_lift, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e _ => deg_Tcyc_le c p e w
  have hC : ∑ q ∈ Y.image (Ccyc c p), deg q w ≤ ∑ e ∈ Y, deg (Ccyc c p e) w := sum_image_le' _ _ _
  have hD : ∑ q ∈ (dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2), deg q w ≤
      34 * ∑ e ∈ Y, deg (Ccyc c p e) w := by
    refine (sum_image_le' _ _ _).trans ?_
    refine (Finset.sum_le_sum fun ef _ => deg_Dcyc_le c p ef.1 ef.2 w).trans ?_
    rw [Finset.sum_add_distrib]
    have h1 : ∑ x ∈ dPairs Y, deg (Ccyc c p x.1) w ≤ 17 * ∑ a ∈ Y, deg (Ccyc c p a) w :=
      sum_filter_prod_fst_le Y (fun e f => e.2 = f.1) (fun e => deg (Ccyc c p e) w) 17 fun e _ => by
        simpa [eq_comm] using outDeg_le_of_maxDeg hdeg e.2
    have h2 : ∑ x ∈ dPairs Y, deg (Ccyc c p x.2) w ≤ 17 * ∑ a ∈ Y, deg (Ccyc c p a) w :=
      sum_filter_prod_snd_le Y (fun e f => e.2 = f.1) (fun e => deg (Ccyc c p e) w) 17 fun f _ =>
        inDeg_le_of_maxDeg hdeg f.1
    omega
  have hP : ∑ q ∈ (pPairs p Y).image (fun xy => Pcyc p xy.1 xy.2), deg q w ≤
      (2 * B) * ∑ e ∈ Y, deg (Ccyc c p e) w := by
    refine (sum_image_le' _ _ _).trans ?_
    refine (Finset.sum_le_sum fun xy _ => deg_Pcyc_le c p xy.1 xy.2 w).trans ?_
    rw [Finset.sum_add_distrib]
    have h1 : ∑ x ∈ pPairs p Y, deg (Ccyc c p x.1) w ≤ B * ∑ a ∈ Y, deg (Ccyc c p a) w := sum_filter_prod_fst_le Y
      (fun x y => p x.1 ≠ p x.2 ∧ p y.1 = p x.2 ∧ p y.2 = p x.1) (fun e => deg (Ccyc c p e) w) B
      fun x _ => pPairs_fst_fiber p hB x
    have h2 : ∑ x ∈ pPairs p Y, deg (Ccyc c p x.2) w ≤ B * ∑ a ∈ Y, deg (Ccyc c p a) w := sum_filter_prod_snd_le Y
      (fun x y => p x.1 ≠ p x.2 ∧ p y.1 = p x.2 ∧ p y.2 = p x.1) (fun e => deg (Ccyc c p e) w) B
      fun y _ => pPairs_snd_fiber p hB y
    nlinarith
  unfold catalogLoad lib
  have u1 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc c p) ∪
    (dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2))
    ((pPairs p Y).image (fun xy => Pcyc p xy.1 xy.2)) (fun q => deg q w)
  have u2 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc c p))
    ((dPairs Y).image (fun ef => Dcyc c p ef.1 ef.2)) (fun q => deg q w)
  have u3 := sum_union_le' (Y.image (Tcyc (P := P))) (Y.image (Ccyc c p)) (fun q => deg q w)
  rw [hR]
  nlinarith

end Bounds

/-! ### Validity of the library pieces and the partitions -/

section Partition

variable {V P : Type*} [DecidableEq V] [DecidableEq P]
variable (c : V → ZMod 3) (p : V → P)

omit [DecidableEq V] in
lemma balanced_of_isDirCycle {W : Type*} [DecidableEq W] {E : Finset (W × W)}
    (h : IsDirCycle E) : Balanced E := h.2.1

/-- Every library piece is a nonempty directed simple cycle (hence balanced) of length `≤ 12`
contained in `R ∪ Y`. -/
theorem lib_valid {Y : Finset (V × V)} (hY : IsCyc c Y) :
    ∀ q ∈ lib c p Y, IsDirCycle q ∧ q.card ≤ 12 ∧
      q ⊆ reserve c p Y ∪ Y.map (liftArc V (P ⊕ ((V × V) × Fin 9))) := by
  intro q hq
  have hRmem : ∀ e ∈ Y, ∀ {a}, a ∈ Ccyc c p e → a ∈ reserve c p Y ∪
      Y.map (liftArc V (P ⊕ ((V × V) × Fin 9))) :=
    fun e he a ha => Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨e, he, ha⟩)
  simp only [lib, dPairs, pPairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product] at hq
  rcases hq with ((⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨⟨e, f⟩, ⟨⟨he, hf⟩, hef⟩, rfl⟩) |
      ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩
  · obtain ⟨h1, h2⟩ := isDirCycle_T (P := P) (ne_of_cyc c (hY e he))
    refine ⟨h1, h2, ?_⟩
    intro a ha
    simp only [Tcyc, Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · refine Finset.mem_union_right _ (Finset.mem_map.2 ⟨e, he, rfl⟩)
    · exact hRmem e he ((mem_Ccyc c p).2 (Or.inl ha))
  · obtain ⟨k, g, hk, hg, hC, -⟩ := Ccyc_eq c p (hY e he)
    refine ⟨?_, ?_, fun a ha => hRmem e he ha⟩
    · rw [hC]; exact isDirCycle_cycF hg
    · rw [hC, card_cycF hg]; exact hk
  · obtain ⟨h1, h2⟩ := isDirCycle_D c p (e := e) (f := f) hef
    refine ⟨h1, h2, ?_⟩
    intro a ha
    simp only [Dcyc, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact hRmem e he ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inr ha))))
    · exact hRmem f hf ((mem_Ccyc c p).2 (Or.inr (Or.inl ha)))
  · obtain ⟨h1, h2⟩ := isDirCycle_P p (e := x) (f := y) hxy.1 hxy.2.1 hxy.2.2
    refine ⟨h1, h2, ?_⟩
    intro a ha
    simp only [Pcyc, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact hRmem x hx ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha))))
    · exact hRmem y hy ((mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha))))

/-- **Exact positive partitions from the fixed library.** For every balanced `L ⊆ Y` a
subfamily of `lib` partitions `R ∪ L` exactly, without repeated arcs. (The pieces are those of
`CutHub.cutHub_shortener`; here we record that they all belong to the fixed library.) -/
theorem partition_from_lib (rk : P → ℕ) (hrk : Function.Injective rk) {Y : Finset (V × V)}
    (hY : IsCyc c Y) (hcut : CutPartition Y p) (L : Finset (V × V)) (hLY : L ⊆ Y)
    (hLb : Balanced L) :
    ∃ Q ⊆ lib c p Y, (Q : Set (Finset (CV V P × CV V P))).PairwiseDisjoint id ∧
      Q.biUnion id = reserve c p Y ∪ L.map (liftArc V (P ⊕ ((V × V) × Fin 9))) := by
  classical
  have hliftmem : ∀ {a : CV V P × CV V P} {L : Finset (V × V)},
      a ∈ L.map (liftArc V (P ⊕ ((V × V) × Fin 9))) ↔ ∃ e ∈ L, a = (old e.1, old e.2) := by
    intro a L
    simp only [Finset.mem_map, liftArc, Function.Embedding.coeFn_mk, old]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩
  obtain ⟨β, hβ, hβinj, hβsurj⟩ := Hub.exists_pairing L hLb
  obtain ⟨τ, hτ, hτinj, hτsurj⟩ := exists_cross_pairing p hcut hLY hLb rk
  set F := L.filter (fun x => rk (p x.1) < rk (p x.2)) with hF
  have hcross : ∀ f : V × V, p f.1 ≠ p f.2 →
      rk (p f.1) < rk (p f.2) ∨ rk (p f.2) < rk (p f.1) := by
    intro f hf
    rcases lt_trichotomy (rk (p f.1)) (rk (p f.2)) with h | h | h
    · exact Or.inl h
    · exact absurd (hrk h) hf
    · exact Or.inr h
  refine ⟨L.image Tcyc ∪ (Y \ L).image (Ccyc c p) ∪ L.image (fun e => Dcyc c p e (β e)) ∪
    F.image (fun x => Pcyc p x (τ x)), ?_, ?_, ?_⟩
  · -- the chosen pieces belong to the fixed library
    intro q hq
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
    simp only [lib, dPairs, pPairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product]
    rcases hq with ((⟨e, he, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨e, hLY he, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))
    · exact Or.inl (Or.inr ⟨(e, β e), ⟨⟨hLY he, hLY (hβ e he).1⟩, (hβ e he).2.symm⟩, rfl⟩)
    · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
      obtain ⟨hτL, h1, h2⟩ := hτ x hxL hlt
      refine Or.inr ⟨(x, τ x), ⟨⟨hLY hxL, hLY hτL⟩, ?_, h1, h2⟩, rfl⟩
      intro h; rw [h] at hlt; exact lt_irrefl _ hlt
  · have hclass : ∀ q ∈ L.image Tcyc ∪ (Y \ L).image (Ccyc c p) ∪
        L.image (fun e => Dcyc c p e (β e)) ∪ F.image (fun x => Pcyc p x (τ x)),
        ∀ a ∈ q, PieceClass c p Y L rk β τ q a := by
      intro q hq a ha
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
      rcases hq with ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, hfL⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩
      · refine Or.inl ⟨e, he, rfl, ?_⟩
        simp only [Tcyc, Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inl ⟨tag_old _ _, rfl⟩
        · exact Or.inr (tag_piA ha)
      · refine Or.inr (Or.inl ⟨f, hf, hfL, rfl, ?_⟩)
        rcases tag_Ccyc c p ha with t | t | t | t <;> exact ⟨_, t⟩
      · refine Or.inr (Or.inr (Or.inl ⟨e, he, rfl, ?_⟩))
        simp only [Dcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (tag_IA c p ha)
        · exact Or.inr (tag_OA c p ha)
      · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
        refine Or.inr (Or.inr (Or.inr ⟨x, hxL, hlt, rfl, ?_⟩))
        simp only [Pcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (tag_QA p ha)
        · exact Or.inr (tag_QA p ha)
    intro q₁ hq₁ q₂ hq₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a h₁ h₂
    exact hne (pieceClass_eq c p hβinj (fun e he => (hβ e he).1) hτ hτinj
      (hclass q₁ hq₁ a h₁) (hclass q₂ hq₂ a h₂))
  · ext a
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
      id_eq]
    constructor
    · rintro ⟨q, ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩, ha⟩
      · simp only [Tcyc, Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inr (hliftmem.2 ⟨e, he, rfl⟩)
        · exact Or.inl (Finset.mem_biUnion.2 ⟨e, hLY he, (mem_Ccyc c p).2 (Or.inl ha)⟩)
      · exact Or.inl (Finset.mem_biUnion.2 ⟨f, hf, ha⟩)
      · simp only [Dcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (Finset.mem_biUnion.2
            ⟨e, hLY he, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inr ha)))⟩)
        · exact Or.inl (Finset.mem_biUnion.2
            ⟨β e, hLY (hβ e he).1, (mem_Ccyc c p).2 (Or.inr (Or.inl ha))⟩)
      · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
        simp only [Pcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (Finset.mem_biUnion.2
            ⟨x, hLY hxL, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha)))⟩)
        · exact Or.inl (Finset.mem_biUnion.2
            ⟨τ x, hLY (hτ x hxL hlt).1, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha)))⟩)
    · rintro (ha | ha)
      · obtain ⟨f, hf, haf⟩ := Finset.mem_biUnion.1 ha
        by_cases hfL : f ∈ L
        · rcases (mem_Ccyc c p).1 haf with h | h | h | h
          · exact ⟨Tcyc f, Or.inl (Or.inl (Or.inl ⟨f, hfL, rfl⟩)), Finset.mem_insert_of_mem h⟩
          · obtain ⟨e, he, rfl⟩ := hβsurj f hfL
            exact ⟨Dcyc c p e (β e), Or.inl (Or.inr ⟨e, he, rfl⟩),
              Finset.mem_union_right _ h⟩
          · have hpf : p f.1 ≠ p f.2 := by
              intro hpf; simp [QA, hpf] at h
            rcases hcross f hpf with hlt | hlt
            · exact ⟨Pcyc p f (τ f), Or.inr ⟨f, Finset.mem_filter.2 ⟨hfL, hlt⟩, rfl⟩,
                Finset.mem_union_left _ h⟩
            · obtain ⟨x, hxL, hxlt, rfl⟩ := hτsurj f hfL hlt
              exact ⟨Pcyc p x (τ x), Or.inr ⟨x, Finset.mem_filter.2 ⟨hxL, hxlt⟩, rfl⟩,
                Finset.mem_union_right _ h⟩
          · exact ⟨Dcyc c p f (β f), Or.inl (Or.inr ⟨f, hfL, rfl⟩),
              Finset.mem_union_left _ h⟩
        · exact ⟨Ccyc c p f, Or.inl (Or.inl (Or.inr ⟨f, ⟨hf, hfL⟩, rfl⟩)), haf⟩
      · obtain ⟨e, he, rfl⟩ := hliftmem.1 ha
        exact ⟨Tcyc e, Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩)), Finset.mem_insert_self _ _⟩

end Partition

/-! ### The mesoscopic conclusion on the class -/

/-- The conclusion of `MesoscopicRefinerWith C K` for one input `Y` (verbatim body of the
specification in `MesoscopicSpec.lean`). -/
def MesoscopicFor (C K : ℕ) {V : Type} [Fintype V] [DecidableEq V] (c : V → ZMod 3)
    (Y : Finset (V × V)) : Prop :=
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
    (R : Finset ((V ⊕ U) × (V ⊕ U)))
    (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U)))),
    IsCyc (Sum.elim c cU) R ∧ Disjoint R (Y.map (liftArc V U)) ∧
    (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ Y.map (liftArc V U) ∧
      P.card ≤ K ∧ Balanced P) ∧
    lib.card ≤ C * Y.card ∧
    (∀ v, catalogLoad lib v ^ 2 ≤ C ^ 2 * Y.card) ∧
    ∀ L ⊆ Y, Balanced L →
      ∃ Q ⊆ lib, (Q : Set (Finset ((V ⊕ U) × (V ⊕ U)))).PairwiseDisjoint id ∧
        Q.biUnion id = R ∪ L.map (liftArc V U)

/-- `MesoscopicRefinerWith C K` is exactly `MesoscopicFor C K` for every admissible `Y`. -/
theorem mesoscopicRefinerWith_iff (C K : ℕ) :
    MesoscopicRefinerWith C K ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V)),
        IsCyc c Y → MaxDegLE Y 17 → MesoscopicFor C K c Y := Iff.rfl

/-- **The mesoscopic cut class.** `Y` has a cut partition (`CutHub.CutPartition`) whose parts
have arc load at most `B √|Y|` and with at most `B` arcs from any part to any other part. -/
def MesoCutClass {V : Type} [DecidableEq V] (B : ℕ) (Y : Finset (V × V)) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (p : V → P), CutPartition Y p ∧
    (∀ a, (Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card ^ 2 ≤ B ^ 2 * Y.card) ∧
    (∀ a b, a ≠ b → (Y.filter (fun e => p e.1 = a ∧ p e.2 = b)).card ≤ B)

/-- The constant of the mesoscopic cut-class theorem. -/
def mesoConst (B : ℕ) : ℕ := (36 + 2 * B) * 34 + 17 + 2 * (36 + 2 * B) * B + 19 + B

/-- Arithmetic core of the load bound (no square roots). -/
lemma load_sq_le (A D B m ℓ x : ℕ) (hm : 1 ≤ m) (hℓ : ℓ ^ 2 ≤ B ^ 2 * m)
    (hx : x ≤ A + D * ℓ) : x ^ 2 ≤ (A + D * B) ^ 2 * m := by
  have hℓm : ℓ ≤ B * m := by
    have h1 : ℓ ^ 2 ≤ (B * m) ^ 2 := by
      calc ℓ ^ 2 ≤ B ^ 2 * m := hℓ
        _ ≤ B ^ 2 * m * m := Nat.le_mul_of_pos_right _ hm
        _ = (B * m) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h1
  have hx2 : x ^ 2 ≤ (A + D * ℓ) ^ 2 := Nat.pow_le_pow_left hx 2
  refine hx2.trans ?_
  have e1 : (A + D * ℓ) ^ 2 = A ^ 2 + 2 * A * D * ℓ + D ^ 2 * ℓ ^ 2 := by ring
  have e2 : (A + D * B) ^ 2 * m = A ^ 2 * m + 2 * A * D * (B * m) + D ^ 2 * (B ^ 2 * m) := by
    ring
  rw [e1, e2]
  have t1 : A ^ 2 ≤ A ^ 2 * m := Nat.le_mul_of_pos_right _ hm
  have t2 : 2 * A * D * ℓ ≤ 2 * A * D * (B * m) := Nat.mul_le_mul_left _ hℓm
  have t3 : D ^ 2 * ℓ ^ 2 ≤ D ^ 2 * (B ^ 2 * m) := Nat.mul_le_mul_left _ hℓ
  omega

/-- **Main theorem: the mesoscopic producer on the cut class.** For every cyclically tripartite
`Y` of maximum degree `≤ 17` in `MesoCutClass B`, the full conclusion of
`MesoscopicRefinerWith (mesoConst B) 12` holds: fixed reserve, fixed library of nonempty balanced
pieces of size `≤ 12` in `R ∪ Y`, `|lib| ≤ C |Y|`, catalogue load `≤ C √|Y|` at every vertex,
and exact positive partitions of `R ∪ L` for every balanced `L ⊆ Y`. -/
theorem mesoscopicFor_of_mesoCutClass (V : Type) [Fintype V] [DecidableEq V]
    (c : V → ZMod 3) (Y : Finset (V × V)) (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17) (B : ℕ)
    (hB : MesoCutClass B Y) : MesoscopicFor (mesoConst B) 12 c Y := by
  classical
  obtain ⟨P, hPf, hPd, p, hcut, hload, hmult⟩ := hB
  have hmult' : MultLE p Y B := hmult
  set U := P ⊕ ((V × V) × Fin 9)
  refine ⟨U, inferInstance, inferInstance, hcol c, reserve c p Y, lib c p Y, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro a ha
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    exact isCyc_Ccyc c p (hY e he) a hae
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    obtain ⟨f, -, rfl⟩ := Finset.mem_map.1 hb
    exact old_not_mem_Ccyc c p _ _ hae
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := lib_valid c p hY q hq
    exact ⟨h1.1, h3, h2, h1.2.1⟩
  · refine (card_lib_le c p hdeg hmult').trans (Nat.mul_le_mul_right _ ?_)
    unfold mesoConst; omega
  · intro w
    rcases Nat.eq_zero_or_pos Y.card with hm | hm
    · have hY0 : Y = ∅ := Finset.card_eq_zero.1 hm
      have hlib : lib c p Y = ∅ := by
        simp [lib, dPairs, pPairs, hY0]
      simp [hlib, catalogLoad, hm]
    · have hL := catalogLoad_lib_le c p hY hdeg hmult' w
      have hYd : deg (Y.map (liftArc V U)) w ≤ 17 := maxDegLE_map_liftArc hdeg w
      -- reserve degree: `≤ 34 + 2 ℓ` with `ℓ ^ 2 ≤ B ^ 2 |Y|`
      have hdisjY : ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → Disjoint (Ccyc c p i) (Ccyc c p j) :=
        fun i _ j _ hij => Ccyc_disjoint c p hij
      obtain ⟨ℓ, hℓ, hRw⟩ : ∃ ℓ : ℕ, ℓ ^ 2 ≤ B ^ 2 * Y.card ∧
          deg (reserve c p Y) w ≤ 34 + 2 * ℓ := by
        rcases w with v | a | x
        · refine ⟨0, by simp, ?_⟩
          have h := deg_biUnion Y (Ccyc c p) hdisjY (old v)
          have hv : deg (reserve c p Y) (Sum.inl v) = 2 * deg Y v := by
            unfold reserve
            rw [show (Sum.inl v : CV V P) = old v from rfl, h]
            rw [Finset.sum_congr rfl fun e he => deg_Ccyc_old c p (hY e he) v]
            unfold deg inDeg outDeg
            rw [Finset.card_filter, Finset.card_filter, mul_add, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun e he => ?_
            have hne := ne_of_cyc c (hY e he)
            by_cases h2 : e.2 = v
            · have h1 : e.1 ≠ v := fun h1 => hne (h1.trans h2.symm)
              simp [h1, h2]
            · simp [h2]
          rw [hv]; have := hdeg v; omega
        · refine ⟨(Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card, hload a, ?_⟩
          unfold reserve
          rw [deg_biUnion Y (Ccyc c p) hdisjY]
          rw [show (Sum.inr (Sum.inl a) : CV V P) = hub a from rfl]
          rw [Finset.sum_congr rfl fun e he => deg_Ccyc_hub c p (hY e he) a]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
          omega
        · refine ⟨0, by simp, ?_⟩
          unfold reserve
          rw [deg_biUnion Y (Ccyc c p) hdisjY]
          calc ∑ e ∈ Y, deg (Ccyc c p e) (Sum.inr (Sum.inr x))
              ≤ ∑ e ∈ Y, (if x.1 = e then 2 else 0) :=
                Finset.sum_le_sum fun e he => deg_Ccyc_pv c p (hY e he) x
            _ ≤ 34 + 2 * 0 := by
                rw [Finset.sum_ite_eq]
                split_ifs <;> omega
      have hx : catalogLoad (lib c p Y) w ≤
          ((36 + 2 * B) * 34 + 17) + (2 * (36 + 2 * B)) * ℓ := by
        have := Nat.mul_le_mul_left (36 + 2 * B) hRw
        nlinarith
      have hsq := load_sq_le ((36 + 2 * B) * 34 + 17) (2 * (36 + 2 * B)) B Y.card ℓ _ hm hℓ hx
      refine hsq.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ?_ 2))
      unfold mesoConst; nlinarith
  · intro L hLY hLb
    exact partition_from_lib c p (fun a => (Fintype.equivFin P a).val)
      (fun a b h => (Fintype.equivFin P).injective (Fin.ext h)) hY hcut L hLY hLb

/-- **Example of the class: blocks of size `≤ B √|Y|`.** If a vertex partition has no crossing
arcs (`Y` is a union of blocks, e.g. of weak components) and each block carries at most
`B √|Y|` arcs, then `Y ∈ MesoCutClass B`.  The blocks themselves are arbitrary (for instance
bounded-degree expanders), which is beyond the bounded-part class of `CutHub`. -/
theorem mesoCutClass_of_blocks {V : Type} [DecidableEq V] (B : ℕ) (Y : Finset (V × V))
    (P : Type) [Fintype P] [DecidableEq P] (p : V → P) (hblock : ∀ e ∈ Y, p e.1 = p e.2)
    (hload : ∀ a, (Y.filter (fun e => p e.1 = a)).card ^ 2 ≤ B ^ 2 * Y.card) :
    MesoCutClass B Y := by
  refine ⟨P, inferInstance, inferInstance, p, ?_, ?_, ?_⟩
  · intro e he hne; exact absurd (hblock e he) hne
  · intro a
    have : Y.filter (fun e => p e.1 = a ∨ p e.2 = a) = Y.filter (fun e => p e.1 = a) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, h | h⟩
        · exact ⟨he, h⟩
        · exact ⟨he, (hblock e he).trans h⟩
      · rintro ⟨he, h⟩; exact ⟨he, Or.inl h⟩
    rw [this]; exact hload a
  · intro a b hab
    refine le_trans (le_of_eq ?_) (Nat.zero_le B)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro e he ⟨h1, h2⟩
    exact hab (h1.symm.trans ((hblock e he).trans h2))

/-- Corollary in the form of the specification: `MesoscopicRefinerWith (mesoConst B) 12`
holds **restricted to** `MesoCutClass B`. -/
theorem mesoscopicRefiner_on_mesoCutClass (B : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V)),
      IsCyc c Y → MaxDegLE Y 17 → MesoCutClass B Y → MesoscopicFor (mesoConst B) 12 c Y :=
  fun V _ _ c Y hY hdeg hB => mesoscopicFor_of_mesoCutClass V c Y hY hdeg B hB

end MesoCutHub

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
