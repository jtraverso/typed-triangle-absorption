/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.Orientation

@[expose] public section

/-!
# Palette-independent cyclic orientation

For an arbitrary number of classes `t`, a colouring `col : Fin t → ZMod 3` of the classes and an
orientation matrix `o` given by `o r i = [col i = col r + 1] - [col r = col i + 1]`, the
weighted degree `genFlow o p E v = ∑ i, o (p v) i * degVec p E v i` is the out-degree minus the
in-degree of the cyclic orientation `orientBy (col ∘ p) E` (`genFlow_eq_out_sub_in`).  The
forgetful map `symImage` is injective on cyclically oriented arc sets and turns arc degrees into
edge loads.  Nothing here depends on the palette size; the four-label (`Orientation.lean`) and
three-label (`Tri.lean`) bridges are instances.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The cyclic orientation of an edge set for a vertex colouring `c : V → ZMod 3`. -/
def orientBy (c : V → ZMod 3) (E : Finset (Sym2 V)) : Finset (V × V) :=
  (univ ×ˢ univ).filter fun x => s(x.1, x.2) ∈ E ∧ c x.2 = c x.1 + 1

theorem mem_orientBy {c : V → ZMod 3} {E : Finset (Sym2 V)} {x : V × V} :
    x ∈ orientBy c E ↔ s(x.1, x.2) ∈ E ∧ c x.2 = c x.1 + 1 := by
  simp [orientBy]

theorem orientSet_eq_orientBy (p : V → Fin 4) (E : Finset (Sym2 V)) :
    orientSet p E = orientBy (fun v => latinColour (p v)) E := rfl

theorem isCyc_orientBy (c : V → ZMod 3) (E : Finset (Sym2 V)) : IsCyc c (orientBy c E) :=
  fun _ he => (mem_orientBy.mp he).2

theorem orientBy_mono {c : V → ZMod 3} {E F : Finset (Sym2 V)} (h : E ⊆ F) :
    orientBy c E ⊆ orientBy c F := by
  intro x hx
  rw [mem_orientBy] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-- Weighted class degree for an orientation matrix `o`. -/
def genFlow (o : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) : ℤ :=
  ∑ i, o (p v) i * degVec p E v i

omit [Fintype V] in
theorem flowCharge_eq_genFlow (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) :
    flowCharge p E v = genFlow latinOrient p E v := rfl

/-- `o` is the signed adjacency of the cyclic colour order `col`. -/
def IsCycOrient (o : Fin t → Fin t → ℤ) (col : Fin t → ZMod 3) : Prop :=
  ∀ r i, o r i = (if col i = col r + 1 then 1 else 0) - (if col r = col i + 1 then 1 else 0)

theorem IsCycOrient.diag {o : Fin t → Fin t → ℤ} {col : Fin t → ZMod 3}
    (ho : IsCycOrient o col) (r : Fin t) : o r r = 0 := by
  rw [ho r r, if_neg (colour_ne_succ _)]
  simp

theorem genEdge_flow {o : Fin t → Fin t → ℤ} (hd : ∀ r, o r r = 0)
    (p : V → Fin t) (v : V) (e : Sym2 V) :
    ∑ i, o (p v) i * degContrib p v e i = ∑ w, if e = s(v, w) then o (p v) (p w) else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hL : ∑ i, o (p v) i * degContrib p v s(a, b) i =
        (if a = v then o (p v) (p b) else 0) + (if b = v then o (p v) (p a) else 0) := by
      simp only [degContrib, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
        mul_zero]
      congr 1
      · by_cases hv : a = v <;> simp [hv]
      · by_cases hv : b = v <;> simp [hv]
    rw [hL]
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb
      simp [hd]
    · subst ha
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro w _ hw
        rw [if_neg]
        intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hw h2.symm
        · exact hb h2
      · simp
    · subst hb
      rw [Finset.sum_eq_single a]
      · simp [ha, Sym2.eq_swap]
      · intro w _ hw
        rw [if_neg]
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact ha h1
        · exact hw h1.symm
      · simp
    · rw [if_neg ha, if_neg hb, Finset.sum_eq_zero]
      · simp
      intro w _
      rw [if_neg]
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ha h1
      · exact hb h2

theorem genFlow_eq_sum {o : Fin t → Fin t → ℤ} (hd : ∀ r, o r r = 0)
    (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) :
    genFlow o p E v = ∑ w, if s(v, w) ∈ E then o (p v) (p w) else 0 := by
  have h1 : genFlow o p E v = ∑ e ∈ E, ∑ i, o (p v) i * degContrib p v e i := by
    simp only [genFlow, degVec, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h1]
  simp only [genEdge_flow hd]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq']

theorem outDeg_orientBy (c : V → ZMod 3) (E : Finset (Sym2 V)) (v : V) :
    (outDeg (orientBy c E) v : ℤ) = ∑ w, if s(v, w) ∈ E ∧ c w = c v + 1 then 1 else 0 := by
  unfold outDeg orientBy
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product, Finset.sum_eq_single v]
  · refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : s(v, w) ∈ E ∧ c w = c v + 1
    · simp [h]
    · simp [h]
  · intro x _ hx
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [hx]
  · simp

theorem inDeg_orientBy (c : V → ZMod 3) (E : Finset (Sym2 V)) (v : V) :
    (inDeg (orientBy c E) v : ℤ) = ∑ w, if s(v, w) ∈ E ∧ c v = c w + 1 then 1 else 0 := by
  unfold inDeg orientBy
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single v]
  · rw [Sym2.eq_swap]
    by_cases h : s(v, w) ∈ E ∧ c v = c w + 1
    · simp [h]
    · simp [h]
  · intro x _ hx
    simp [hx]
  · simp

/-- **Weighted degree = out-degree − in-degree** of the cyclic orientation, for every palette. -/
theorem genFlow_eq_out_sub_in {o : Fin t → Fin t → ℤ} {col : Fin t → ZMod 3}
    (ho : IsCycOrient o col) (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) :
    genFlow o p E v = (outDeg (orientBy (fun v => col (p v)) E) v : ℤ) -
      inDeg (orientBy (fun v => col (p v)) E) v := by
  rw [genFlow_eq_sum ho.diag, outDeg_orientBy, inDeg_orientBy, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ho]
  by_cases hE : s(v, w) ∈ E <;> simp [hE]

theorem balanced_iff_genFlow {o : Fin t → Fin t → ℤ} {col : Fin t → ZMod 3}
    (ho : IsCycOrient o col) (p : V → Fin t) (E : Finset (Sym2 V)) :
    Cycles.Balanced (orientBy (fun v => col (p v)) E) ↔ ∀ v, genFlow o p E v = 0 := by
  constructor
  · intro h v
    rw [genFlow_eq_out_sub_in ho, h v]
    ring
  · intro h v
    have := h v
    rw [genFlow_eq_out_sub_in ho] at this
    omega

section SymImageBy

variable {c : V → ZMod 3}

omit [Fintype V] [DecidableEq V] in
theorem sym_eq_of_cycBy {x y : V × V} (hx : c x.2 = c x.1 + 1) (hy : c y.2 = c y.1 + 1)
    (h : s(x.1, x.2) = s(y.1, y.2)) : x = y := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    rw [h1, h2] at hx
    exact colour_not_both _ _ hy hx

omit [Fintype V] [DecidableEq V] in
theorem symInjOnBy {A : Finset (V × V)} (hA : IsCyc c A) :
    Set.InjOn (fun x : V × V => s(x.1, x.2)) (A : Set (V × V)) :=
  fun _ hx _ hy h => sym_eq_of_cycBy (hA _ hx) (hA _ hy) h

theorem orientBy_symImage {A : Finset (V × V)} (hA : IsCyc c A) :
    orientBy c (symImage A) = A := by
  ext x
  rw [mem_orientBy, mem_symImage]
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have := sym_eq_of_cycBy (c := c) (hA y hy) hx hxy
    exact this ▸ hy
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hA x hx⟩

/-- If every edge joins two consecutive colours, orienting and forgetting is the identity. -/
theorem symImage_orientBy {E : Finset (Sym2 V)}
    (hcons : ∀ a b, s(a, b) ∈ E → c b = c a + 1 ∨ c a = c b + 1) :
    symImage (orientBy c E) = E := by
  ext e
  rw [mem_symImage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_orientBy.mp hx).1
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rcases hcons a b he with h | h
      · exact ⟨(a, b), mem_orientBy.mpr ⟨he, h⟩, rfl⟩
      · exact ⟨(b, a), mem_orientBy.mpr ⟨by rwa [Sym2.eq_swap], h⟩, Sym2.eq_swap⟩

omit [Fintype V] in
theorem disjoint_symImageBy {A B : Finset (V × V)} (hAB : IsCyc c (A ∪ B))
    (hd : Disjoint A B) : Disjoint (symImage A) (symImage B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  obtain ⟨x, hx, rfl⟩ := mem_symImage.mp heA
  obtain ⟨y, hy, hxy⟩ := mem_symImage.mp heB
  have := sym_eq_of_cycBy (c := c) (hAB y (mem_union_right _ hy)) (hAB x (mem_union_left _ hx)) hxy
  exact Finset.disjoint_left.mp hd hx (this ▸ hy)

omit [Fintype V] in
theorem incidentLoad_symImageBy {A : Finset (V × V)} (hA : IsCyc c A) (v : V) :
    incidentLoad (symImage A) v = deg A v := by
  unfold incidentLoad symImage deg inDeg outDeg
  rw [Finset.filter_image]
  rw [card_image_of_injOn ((symInjOnBy hA).mono (by intro x hx; exact (mem_filter.mp hx).1))]
  have hsplit : A.filter (fun x => v ∈ s(x.1, x.2)) =
      A.filter (fun x => x.2 = v) ∪ A.filter (fun x => x.1 = v) := by
    ext x
    simp only [mem_filter, mem_union, Sym2.mem_iff]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact Or.inr ⟨hx, h.symm⟩
      · exact Or.inl ⟨hx, h.symm⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, Or.inr h.symm⟩
      · exact ⟨hx, Or.inl h.symm⟩
  rw [hsplit, card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 := (mem_filter.mp hx1).2
  have h2 := (mem_filter.mp hx2).2
  have hc := hA x (mem_filter.mp hx1).1
  rw [h1, ← h2] at hc
  exact colour_ne_succ _ hc

end SymImageBy

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge
