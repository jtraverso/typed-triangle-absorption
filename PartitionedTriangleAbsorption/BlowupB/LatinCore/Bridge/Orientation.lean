/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Reduction
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Flow
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoscopicSpec

@[expose] public section

/-!
# Orientation bridge between the Latin family and cyclically oriented digraphs

The allowed class pairs of `F_latin = {012, 013}` are `01, 02, 03, 12, 13`.  Merging the classes
`2` and `3` gives the colouring `latinColour = (0, 1, 2, 2) : Fin 4 → ZMod 3`, and every allowed
edge joins two consecutive colours.  Orienting every edge from colour `i` to colour `i + 1`
(`orientSet`) turns

* integral `F_latin`-divisibility into the Eulerian condition `Cycles.Balanced`
  (`isIntDiv_iff_balanced`, via the ported `isIntDiv_latin_iff` of `Flow.lean`),
* edge loads into arc degrees (`incidentLoad_symImage`), and
* edge-disjoint unions into arc-disjoint unions (`disjoint_symImage`).

`latinRefiner_of_physicalCycRefiner` reduces `LatinRefiner` to `PhysicalCycRefiner`, the same
statement in the oriented vocabulary of `Cycles.MesoscopicRefinerWith`.  `PhysicalCycRefiner` is
NOT asserted anywhere: it is the remaining physical statement.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

/-- Merging the two last classes: colours `0, 1, 2, 2`. -/
def latinColour : Fin 4 → ZMod 3 := ![0, 1, 2, 2]

theorem latinOrient_eq_colour : ∀ r i : Fin 4, latinOrient r i =
    (if latinColour i = latinColour r + 1 then 1 else 0) -
      (if latinColour r = latinColour i + 1 then 1 else 0) := by
  unfold latinOrient latinColour; decide

theorem link_consecutive : ∀ i j k : Fin 4, Link F_latin i j k →
    latinColour j = latinColour i + 1 ∨ latinColour i = latinColour j + 1 := by
  unfold Link F_latin latinColour; decide

theorem colour_not_both (x y : ZMod 3) (h1 : y = x + 1) (h2 : x = y + 1) : False := by
  subst h1
  have : (0 : ZMod 3) = 2 := by
    calc (0 : ZMod 3) = x - x := by ring
      _ = (x + 1 + 1) - x := by rw [← h2]
      _ = 2 := by ring
  exact absurd this (by decide)

theorem colour_ne_succ (x : ZMod 3) : x ≠ x + 1 := by
  intro h
  have : (0 : ZMod 3) = 1 := by
    calc (0 : ZMod 3) = x - x := by ring
      _ = (x + 1) - x := by rw [← h]
      _ = 1 := by ring
  exact absurd this (by decide)

theorem latinOrient_diag : ∀ r : Fin 4, latinOrient r r = 0 := by
  unfold latinOrient; decide

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cyclic orientation of an (unordered) edge set. -/
def orientSet (p : V → Fin 4) (E : Finset (Sym2 V)) : Finset (V × V) :=
  (univ ×ˢ univ).filter fun x => s(x.1, x.2) ∈ E ∧ latinColour (p x.2) = latinColour (p x.1) + 1

/-- Forgetting the orientation. -/
def symImage (A : Finset (V × V)) : Finset (Sym2 V) := A.image fun x => s(x.1, x.2)

theorem mem_orientSet {p : V → Fin 4} {E : Finset (Sym2 V)} {x : V × V} :
    x ∈ orientSet p E ↔ s(x.1, x.2) ∈ E ∧ latinColour (p x.2) = latinColour (p x.1) + 1 := by
  simp [orientSet]

theorem isCyc_orientSet (p : V → Fin 4) (E : Finset (Sym2 V)) :
    IsCyc (fun v => latinColour (p v)) (orientSet p E) := fun _ he => (mem_orientSet.mp he).2

theorem edge_flow (p : V → Fin 4) (v : V) (e : Sym2 V) :
    ∑ i, latinOrient (p v) i * degContrib p v e i =
      ∑ w, if e = s(v, w) then latinOrient (p v) (p w) else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hL : ∑ i, latinOrient (p v) i * degContrib p v s(a, b) i =
        (if a = v then latinOrient (p v) (p b) else 0) +
          (if b = v then latinOrient (p v) (p a) else 0) := by
      simp only [degContrib, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
        mul_zero]
      congr 1
      · by_cases hv : a = v <;> simp [hv]
      · by_cases hv : b = v <;> simp [hv]
    rw [hL]
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb
      simp [latinOrient_diag]
    · subst ha
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro w _ hw
        rw [if_neg]
        intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, h2⟩
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

theorem flowCharge_eq_sum (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) :
    flowCharge p E v = ∑ w, if s(v, w) ∈ E then latinOrient (p v) (p w) else 0 := by
  have h1 : flowCharge p E v = ∑ e ∈ E, ∑ i, latinOrient (p v) i * degContrib p v e i := by
    simp only [flowCharge, degVec, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h1]
  simp only [edge_flow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq']

theorem outDeg_orientSet (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) :
    (outDeg (orientSet p E) v : ℤ) = ∑ w,
      if s(v, w) ∈ E ∧ latinColour (p w) = latinColour (p v) + 1 then 1 else 0 := by
  unfold outDeg orientSet
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product, Finset.sum_eq_single v]
  · refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : s(v, w) ∈ E ∧ latinColour (p w) = latinColour (p v) + 1
    · simp [h]
    · simp [h]
  · intro x _ hx
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [hx]
  · simp

theorem inDeg_orientSet (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) :
    (inDeg (orientSet p E) v : ℤ) = ∑ w,
      if s(v, w) ∈ E ∧ latinColour (p v) = latinColour (p w) + 1 then 1 else 0 := by
  unfold inDeg orientSet
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single v]
  · rw [Sym2.eq_swap]
    by_cases h : s(v, w) ∈ E ∧ latinColour (p v) = latinColour (p w) + 1
    · simp [h]
    · simp [h]
  · intro x _ hx
    simp [hx]
  · simp

theorem flowCharge_eq_out_sub_in (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) :
    flowCharge p E v = (outDeg (orientSet p E) v : ℤ) - inDeg (orientSet p E) v := by
  rw [flowCharge_eq_sum, outDeg_orientSet, inDeg_orientSet, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [latinOrient_eq_colour]
  by_cases hE : s(v, w) ∈ E <;> simp [hE]

theorem balanced_iff_flowCharge (p : V → Fin 4) (E : Finset (Sym2 V)) :
    Cycles.Balanced (orientSet p E) ↔ ∀ v, flowCharge p E v = 0 := by
  constructor
  · intro h v
    rw [flowCharge_eq_out_sub_in, h v]
    ring
  · intro h v
    have := h v
    rw [flowCharge_eq_out_sub_in] at this
    omega

/-- **Integral Latin divisibility is the Eulerian condition of the cyclic orientation.** -/
theorem isIntDiv_iff_balanced (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F_latin p E) :
    IsIntDiv p F_latin E ↔ Cycles.Balanced (orientSet p E) := by
  rw [balanced_iff_flowCharge, isIntDiv_latin_iff p E hact]

section SymImage

variable {p : V → Fin 4}

/-- Arc sets oriented from colour `i` to colour `i + 1`. -/
abbrev CycArcs (p : V → Fin 4) (A : Finset (V × V)) : Prop :=
  IsCyc (fun v => latinColour (p v)) A

omit [Fintype V] [DecidableEq V] in
theorem sym_eq_of_cyc {x y : V × V}
    (hx : latinColour (p x.2) = latinColour (p x.1) + 1)
    (hy : latinColour (p y.2) = latinColour (p y.1) + 1)
    (h : s(x.1, x.2) = s(y.1, y.2)) : x = y := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    rw [h1, h2] at hx
    exact colour_not_both _ _ hy hx

omit [Fintype V] [DecidableEq V] in
theorem symInjOn {A : Finset (V × V)} (hA : CycArcs p A) :
    Set.InjOn (fun x : V × V => s(x.1, x.2)) (A : Set (V × V)) :=
  fun _ hx _ hy h => sym_eq_of_cyc (hA _ hx) (hA _ hy) h

omit [Fintype V] in
theorem mem_symImage {A : Finset (V × V)} {e : Sym2 V} :
    e ∈ symImage A ↔ ∃ x ∈ A, s(x.1, x.2) = e := by
  simp [symImage]

omit [Fintype V] in
theorem card_symImage {A : Finset (V × V)} (hA : CycArcs p A) :
    (symImage A).card = A.card :=
  card_image_of_injOn (symInjOn hA)

theorem orientSet_symImage {A : Finset (V × V)} (hA : CycArcs p A) :
    orientSet p (symImage A) = A := by
  ext x
  rw [mem_orientSet, mem_symImage]
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have := sym_eq_of_cyc (p := p) (hA y hy) hx hxy
    exact this ▸ hy
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hA x hx⟩

theorem symImage_orientSet {E : Finset (Sym2 V)} (hact : ActiveEdges F_latin p E) :
    symImage (orientSet p E) = E := by
  ext e
  rw [mem_symImage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_orientSet.mp hx).1
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := hact a b he
      rcases link_consecutive _ _ _ hk with h | h
      · exact ⟨(a, b), mem_orientSet.mpr ⟨he, h⟩, rfl⟩
      · refine ⟨(b, a), mem_orientSet.mpr ⟨by rwa [Sym2.eq_swap], h⟩, Sym2.eq_swap⟩

omit [Fintype V] in
theorem symImage_union (A B : Finset (V × V)) : symImage (A ∪ B) = symImage A ∪ symImage B :=
  image_union _ _

omit [Fintype V] in
theorem symImage_mono {A B : Finset (V × V)} (h : A ⊆ B) : symImage A ⊆ symImage B :=
  image_subset_image h

omit [Fintype V] in
theorem disjoint_symImage {A B : Finset (V × V)} (hAB : CycArcs p (A ∪ B))
    (hd : Disjoint A B) : Disjoint (symImage A) (symImage B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  obtain ⟨x, hx, rfl⟩ := mem_symImage.mp heA
  obtain ⟨y, hy, hxy⟩ := mem_symImage.mp heB
  have := sym_eq_of_cyc (p := p) (hAB y (mem_union_right _ hy)) (hAB x (mem_union_left _ hx)) hxy
  exact Finset.disjoint_left.mp hd hx (this ▸ hy)

omit [Fintype V] in
theorem incidentLoad_symImage {A : Finset (V × V)} (hA : CycArcs p A) (v : V) :
    incidentLoad (symImage A) v = deg A v := by
  unfold incidentLoad symImage deg inDeg outDeg
  rw [Finset.filter_image]
  rw [card_image_of_injOn ((symInjOn hA).mono (by intro x hx; exact (mem_filter.mp hx).1))]
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

omit [Fintype V] in
theorem activeEdges_symImage (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link F_latin (p u) (p v) k) {A : Finset (V × V)}
    (hA : ∀ x ∈ A, G.Adj x.1 x.2) : ActiveEdges F_latin p (symImage A) := by
  intro a b hab
  obtain ⟨x, hx, hxe⟩ := mem_symImage.mp hab
  rcases Sym2.eq_iff.mp hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hG a b (h1 ▸ h2 ▸ hA x hx)
  · exact hG a b (h1 ▸ h2 ▸ (hA x hx).symm)

theorem symImage_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (V × V)} (hA : ∀ x ∈ A, G.Adj x.1 x.2) : symImage A ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_symImage.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (hA x hx)

theorem orientSet_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) : orientSet p E ⊆ orientSet p F := by
  intro x hx
  rw [mem_orientSet] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

end SymImage

/-- **The physical cyclic refiner** (the Latin refiner in oriented vocabulary; NOT asserted).

The same quantifiers, hypotheses and constants as `LatinRefiner`, but the reserve `R` is a set of
host arcs oriented from colour `i` to colour `i + 1`, the library pieces are arc sets inside
`R ∪ orientSet p X`, divisibility is replaced by `Cycles.Balanced`, edge loads by arc degrees
(`deg`, `catalogLoad`), and the leftovers are the balanced subsets of the oriented reserve
`orientSet p X`.  Compared with `Cycles.MesoscopicRefinerWith`, all vertices are physical host
vertices (no auxiliary vertex type), every reserve arc is a host edge outside `X`, the input `X`
may have degree up to `2 rho n`, and all budgets are in terms of `lam n / ω`. -/
def PhysicalCycRefiner : Prop :=
  ∃ K M L0 : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 → 0 < lam → 2 ^ L0 * lam ≤ ω ^ 3 → 0 < rho → 2 ^ 24 * rho ≤ lam ^ 2 →
    1 ≤ rho * Fintype.card V →
    (∀ u v, G.Adj u v → ∃ k, Link F_latin (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F_latin i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
      ∃ (R : Finset (V × V)) (lib : Finset (Finset (V × V))),
        (∀ e ∈ R, G.Adj e.1 e.2) ∧ IsCyc (fun v => latinColour (p v)) R ∧
        Disjoint R (orientSet p X) ∧
        (∀ v, (deg R v : ℝ) ≤ M * lam * Fintype.card V / ω) ∧
        (∀ P ∈ lib, P ⊆ R ∪ orientSet p X ∧ P.card ≤ K ∧ Cycles.Balanced P) ∧
        ((lib.card : ℝ) ≤ M * lam * (Fintype.card V : ℝ) ^ 2 / ω) ∧
        (∀ v, (catalogLoad lib v : ℝ) ≤ M * lam * Fintype.card V / ω) ∧
        ∀ L ⊆ orientSet p X, Cycles.Balanced L →
          ∃ Q ⊆ lib, (Q : Set (Finset (V × V))).PairwiseDisjoint id ∧ Q.biUnion id = R ∪ L

/-- **Orientation bridge.** The physical cyclic refiner implies the Latin refiner. -/
theorem latinRefiner_of_physicalCycRefiner (h : PhysicalCycRefiner) : LatinRefiner := by
  obtain ⟨K, M, L0, h⟩ := h
  refine ⟨K, M, L0, ?_⟩
  intro V _ _ p G _ ω lam rho hω hω1 hlam hL0 hrho hscale hn hG hs X hXG hXdeg
  obtain ⟨R, lib, hRG, hRcyc, hRX, hRdeg, hpieces, hlib, hload, href⟩ :=
    h V p G ω lam rho hω hω1 hlam hL0 hrho hscale hn hG hs X hXG hXdeg
  have hXact : ActiveEdges F_latin p X := fun a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hXG hab))
  have hOX : CycArcs p (orientSet p X) := isCyc_orientSet p X
  have hall : CycArcs p (R ∪ orientSet p X) := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hRcyc e he
    · exact hOX e he
  have hXsym : symImage (orientSet p X) = X := symImage_orientSet hXact
  have hadj : ∀ x ∈ R ∪ orientSet p X, G.Adj x.1 x.2 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hRG x hx
    · exact SimpleGraph.mem_edgeFinset.mp (hXG (mem_orientSet.mp hx).1)
  have hpieceCyc : ∀ P ∈ lib, CycArcs p P := fun P hP e he => hall e ((hpieces P hP).1 he)
  refine ⟨Finset (V × V), lib, symImage, symImage R, symImage_subset_edgeFinset G hRG, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := disjoint_symImage hall hRX
    rwa [hXsym] at this
  · intro v
    change ((incidentLoad (symImage R) v : ℕ) : ℝ) ≤ _
    rw [incidentLoad_symImage hRcyc]
    exact hRdeg v
  · intro L hLX hL
    have hLact : ActiveEdges F_latin p L := fun a b hab => hXact a b (hLX hab)
    have hbal : Cycles.Balanced (orientSet p L) := (isIntDiv_iff_balanced p L hLact).mp hL
    obtain ⟨Q, hQ, hdisj, hU⟩ := href (orientSet p L) (orientSet_mono hLX) hbal
    refine ⟨Q, hQ, ?_, ?_⟩
    · intro P1 hP1 P2 hP2 hne
      have hc : CycArcs p (P1 ∪ P2) := by
        intro e he
        rcases mem_union.mp he with he | he
        · exact hpieceCyc P1 (hQ hP1) e he
        · exact hpieceCyc P2 (hQ hP2) e he
      exact disjoint_symImage hc (hdisj hP1 hP2 hne)
    · have himg : Q.biUnion symImage = symImage (Q.biUnion id) := by
        ext e
        simp only [symImage, mem_biUnion, mem_image, id]
        constructor
        · rintro ⟨P, hP, x, hx, rfl⟩
          exact ⟨x, ⟨P, hP, hx⟩, rfl⟩
        · rintro ⟨x, ⟨P, hP, hx⟩, rfl⟩
          exact ⟨P, hP, x, hx, rfl⟩
      rw [himg, hU, symImage_union, symImage_orientSet hLact]
  · intro P hP
    obtain ⟨hPsub, hPcard, hPbal⟩ := hpieces P hP
    refine ⟨?_, card_image_le.trans hPcard, ?_⟩
    · have := symImage_mono hPsub
      rw [symImage_union, hXsym] at this
      rwa [union_comm] at this
    · have hact := activeEdges_symImage G hG (fun x hx => hadj x (hPsub hx))
      rw [isIntDiv_iff_balanced p _ hact, orientSet_symImage (hpieceCyc P hP)]
      exact hPbal
  · exact hlib
  · intro v
    have : (∑ i ∈ lib, incidentLoad (symImage i) v) = catalogLoad lib v := by
      unfold catalogLoad
      exact sum_congr rfl fun P hP => incidentLoad_symImage (hpieceCyc P hP) v
    rw [this]
    exact hload v

/-- If the physical cyclic refiner is ever constructed, the Latin target follows. -/
theorem latinTarget_of_physicalCycRefiner (h : PhysicalCycRefiner) : LatinTarget :=
  latinTarget_of_latinRefiner (latinRefiner_of_physicalCycRefiner h)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge
