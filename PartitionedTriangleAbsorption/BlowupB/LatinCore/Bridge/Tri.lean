/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.CycOrient

@[expose] public section

/-!
# The native three-colour (tripartite) bridge

Here the palette is `Fin 3` and the family is the single rainbow triangle `F_tri = {{0, 1, 2}}`.
Allowed pairs are the three pairs of distinct classes, oriented `0 → 1 → 2 → 0`.

* `isIntDiv_tri_iff`: on allowed edge sets, `IsIntDiv p F_tri E` is the Eulerian condition
  `genFlow triOrient p E v = 0` at every vertex.
* `isIntDiv_iff_balanced_tri`: equivalently, the cyclic orientation is `Cycles.Balanced`.
* `TriRefiner`: the three-colour analogue of `LatinRefiner` (same quantifiers, constants,
  guarded supply and budgets, palette `Fin 3`, family `F_tri`). NOT asserted.
* `PhysicalCycRefiner3`: the same statement in oriented vocabulary over physical host vertices.
  NOT asserted.
* `triRefiner_of_physicalCycRefiner3 : PhysicalCycRefiner3 → TriRefiner` (proved).
* Four-label specialisation: `physicalCycRefiner_of_physicalCycRefiner3 :
  PhysicalCycRefiner3 → PhysicalCycRefiner`, obtained by fusing the classes `2, 3` of a Latin host
  (`fuse`), which preserves the guarded supply with the same absolute bound (`guardedSupply_fuse`);
  hence `latinRefiner_of_physicalCycRefiner3` and `latinTarget_of_physicalCycRefiner3`.

The three-colour statement does not require a fourth (possibly empty) class, so it applies to
hosts with exactly three nonempty supplied classes.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

/-- The rainbow triangle family on three classes. -/
def F_tri : Finset (Multiset (Fin 3)) := {{0, 1, 2}}

/-- Class colours `0, 1, 2`. -/
def triColour : Fin 3 → ZMod 3 := ![0, 1, 2]

/-- The cyclic orientation `0 → 1 → 2 → 0` as a signed matrix. -/
def triOrient : Fin 3 → Fin 3 → ℤ := ![![0, 1, -1], ![-1, 0, 1], ![1, -1, 0]]

theorem triOrient_isCyc : IsCycOrient triOrient triColour := by
  unfold IsCycOrient triOrient triColour; decide

theorem triOrient_apply :
    triOrient 0 0 = 0 ∧ triOrient 0 1 = 1 ∧ triOrient 0 2 = -1 ∧
    triOrient 1 0 = -1 ∧ triOrient 1 1 = 0 ∧ triOrient 1 2 = 1 ∧
    triOrient 2 0 = 1 ∧ triOrient 2 1 = -1 ∧ triOrient 2 2 = 0 := by decide

theorem tri_link_consecutive : ∀ i j k : Fin 3, Link F_tri i j k →
    triColour j = triColour i + 1 ∨ triColour i = triColour j + 1 := by
  unfold Link F_tri triColour; decide

theorem tri_no_loop : ∀ r : Fin 3, ¬ ∃ l, Link F_tri r r l := by
  unfold Link F_tri; decide

theorem typeDegVec_tri_apply :
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 0 0 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 0 1 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 0 2 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 1 0 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 1 1 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 1 2 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 2 0 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 2 1 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 3)) 2 2 = 0 := by decide

theorem typeEdgeVec_tri_apply :
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 0 0 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 0 1 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 0 2 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 1 0 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 1 1 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 1 2 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 2 0 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 2 1 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 3)) 2 2 = 0 := by decide

theorem tri_kill : ∀ r : Fin 3, ∀ τ ∈ F_tri, r ∈ τ →
    ∑ i, triOrient r i * typeDegVec τ r i = 0 := by
  unfold F_tri; decide

theorem tri_filter : ∀ r : Fin 3, F_tri.filter (fun τ => r ∈ τ) = {{0, 1, 2}} := by
  unfold F_tri; decide

/-- The local lattice of `F_tri`, solved. -/
theorem tri_local (r : Fin 3) (d : Fin 3 → ℤ) (hsupp : ∀ j, d j ≠ 0 → ∃ l, Link F_tri r j l)
    (hflow : ∑ j, triOrient r j * d j = 0) :
    ∃ c : Multiset (Fin 3) → ℤ, d = ∑ τ ∈ F_tri with r ∈ τ, c τ • typeDegVec τ r := by
  have hrr : d r = 0 := by
    by_contra h
    exact tri_no_loop r (hsupp r h)
  rw [tri_filter r]
  simp only [sum_singleton]
  simp only [Fin.sum_univ_three] at hflow
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
  · refine ⟨fun _ => d 1, ?_⟩
    simp only [triOrient_apply] at hflow
    funext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_tri_apply] <;> linarith
  · refine ⟨fun _ => d 2, ?_⟩
    simp only [triOrient_apply] at hflow
    funext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_tri_apply] <;> linarith
  · refine ⟨fun _ => d 0, ?_⟩
    simp only [triOrient_apply] at hflow
    funext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_tri_apply] <;> linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem genFlow_tri_eq_zero_of_isIntDiv (p : V → Fin 3) (E : Finset (Sym2 V))
    (h : IsIntDiv p F_tri E) (v : V) : genFlow triOrient p E v = 0 := by
  obtain ⟨c, hc⟩ := h.2 v
  unfold genFlow
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  obtain ⟨hτF, hvτ⟩ := Finset.mem_filter.mp hτ
  have hk := tri_kill (p v) τ hτF hvτ
  calc ∑ i, triOrient (p v) i * (c τ * typeDegVec τ (p v) i)
      = c τ * ∑ i, triOrient (p v) i * typeDegVec τ (p v) i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hk, mul_zero]

theorem sum_orient_edgeVec_tri (p : V → Fin 3) (E : Finset (Sym2 V)) (r : Fin 3) :
    ∑ j, triOrient r j * edgeVec p E r j =
      ∑ v ∈ univ.filter (fun v => p v = r), genFlow triOrient p E v := by
  simp only [StructuralF3General.LatticeBasics.edgeVec_eq_sum_degVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [genFlow, (Finset.mem_filter.mp hv).2]

/-- **Integral `F_tri`-divisibility is the Eulerian condition** of the orientation `0→1→2→0`. -/
theorem isIntDiv_tri_iff (p : V → Fin 3) (E : Finset (Sym2 V))
    (hact : ActiveEdges F_tri p E) :
    IsIntDiv p F_tri E ↔ ∀ v, genFlow triOrient p E v = 0 := by
  constructor
  · exact fun h v => genFlow_tri_eq_zero_of_isIntDiv p E h v
  intro hflow
  have hsupp : ∀ v j, degVec p E v j ≠ 0 → ∃ l, Link F_tri (p v) j l := by
    intro v j hj
    obtain ⟨b, hb, hpb⟩ := exists_of_degVec_ne_zero hj
    exact hpb ▸ hact v b hb
  refine ⟨?_, fun v => tri_local (p v) (degVec p E v) (hsupp v) (hflow v)⟩
  have hzero : ∀ i j, ¬ (∃ l, Link F_tri i j l) → edgeVec p E i j = 0 := by
    intro i j hij
    rw [StructuralF3General.LatticeBasics.edgeVec_eq_sum_degVec]
    refine Finset.sum_eq_zero fun v hv => ?_
    by_contra hne
    exact hij ((Finset.mem_filter.mp hv).2 ▸ hsupp v j hne)
  have hbal : ∀ r, ∑ j, triOrient r j * edgeVec p E r j = 0 := fun r => by
    rw [sum_orient_edgeVec_tri]; exact Finset.sum_eq_zero fun v _ => hflow v
  have hsym := StructuralF3General.LatticeBasics.edgeVec_symm p E
  have b0 := hbal 0
  have b1 := hbal 1
  simp only [Fin.sum_univ_three, triOrient_apply] at b0 b1
  have z00 := hzero 0 0 (tri_no_loop 0)
  have z11 := hzero 1 1 (tri_no_loop 1)
  have z22 := hzero 2 2 (tri_no_loop 2)
  have s01 := hsym 0 1
  have s02 := hsym 0 2
  have s12 := hsym 1 2
  refine ⟨fun _ => edgeVec p E 0 1, ?_⟩
  unfold F_tri
  rw [sum_singleton]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, typeEdgeVec_tri_apply] <;> linarith

/-- The cyclic orientation of a three-colour host. -/
abbrev orientTri (p : V → Fin 3) (E : Finset (Sym2 V)) : Finset (V × V) :=
  orientBy (fun v => triColour (p v)) E

/-- **Three-colour divisibility = balance** of the cyclic orientation. -/
theorem isIntDiv_iff_balanced_tri (p : V → Fin 3) (E : Finset (Sym2 V))
    (hact : ActiveEdges F_tri p E) :
    IsIntDiv p F_tri E ↔ Cycles.Balanced (orientTri p E) := by
  rw [balanced_iff_genFlow triOrient_isCyc, isIntDiv_tri_iff p E hact]

omit [Fintype V] in
theorem activeEdges_symImageF {t : ℕ} (F : Finset (Multiset (Fin t))) (p : V → Fin t)
    (G : SimpleGraph V) (hG : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k)
    {A : Finset (V × V)} (hA : ∀ x ∈ A, G.Adj x.1 x.2) : ActiveEdges F p (symImage A) := by
  intro a b hab
  obtain ⟨x, hx, hxe⟩ := mem_symImage.mp hab
  rcases Sym2.eq_iff.mp hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hG a b (h1 ▸ h2 ▸ hA x hx)
  · exact hG a b (h1 ▸ h2 ▸ (hA x hx).symm)

/-- **The native three-colour balanced refiner** (NOT asserted).

Word for word `LatinRefiner` with palette `Fin 3` and family `F_tri = {{0,1,2}}`: every host edge
joins two distinct classes, the guarded supply (including the empty query, i.e. every class has
at least `ω n` vertices) is required for the three actual classes only. -/
def TriRefiner : Prop :=
  ∃ K M L0 : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 → 0 < lam → 2 ^ L0 * lam ≤ ω ^ 3 → 0 < rho → 2 ^ 24 * rho ≤ lam ^ 2 →
    1 ≤ rho * Fintype.card V →
    (∀ u v, G.Adj u v → ∃ k, Link F_tri (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F_tri i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
      ∃ (ι : Type) (lib : Finset ι) (B : ι → Finset (Sym2 V)) (R : Finset (Sym2 V)),
        R ⊆ G.edgeFinset ∧ Disjoint R X ∧
        DegBounded R (M * lam * Fintype.card V / ω) ∧
        RefinerAssembly.RefinesReserve (p := p) (F := F_tri) lib B X R ∧
        (∀ i ∈ lib, B i ⊆ X ∪ R ∧ (B i).card ≤ K ∧ IsIntDiv p F_tri (B i)) ∧
        ((lib.card : ℝ) ≤ M * lam * (Fintype.card V : ℝ) ^ 2 / ω) ∧
        ∀ v, ((∑ i ∈ lib, incidentLoad (B i) v : ℕ) : ℝ) ≤ M * lam * Fintype.card V / ω

/-- **The physical three-colour cyclic refiner** (NOT asserted): `TriRefiner` in the oriented
vocabulary of `Cycles.MesoscopicRefinerWith`, over physical host vertices only. -/
def PhysicalCycRefiner3 : Prop :=
  ∃ K M L0 : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 → 0 < lam → 2 ^ L0 * lam ≤ ω ^ 3 → 0 < rho → 2 ^ 24 * rho ≤ lam ^ 2 →
    1 ≤ rho * Fintype.card V →
    (∀ u v, G.Adj u v → ∃ k, Link F_tri (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F_tri i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
      ∃ (R : Finset (V × V)) (lib : Finset (Finset (V × V))),
        (∀ e ∈ R, G.Adj e.1 e.2) ∧ IsCyc (fun v => triColour (p v)) R ∧
        Disjoint R (orientTri p X) ∧
        (∀ v, (deg R v : ℝ) ≤ M * lam * Fintype.card V / ω) ∧
        (∀ P ∈ lib, P ⊆ R ∪ orientTri p X ∧ P.card ≤ K ∧ Cycles.Balanced P) ∧
        ((lib.card : ℝ) ≤ M * lam * (Fintype.card V : ℝ) ^ 2 / ω) ∧
        (∀ v, (catalogLoad lib v : ℝ) ≤ M * lam * Fintype.card V / ω) ∧
        ∀ L ⊆ orientTri p X, Cycles.Balanced L →
          ∃ Q ⊆ lib, (Q : Set (Finset (V × V))).PairwiseDisjoint id ∧ Q.biUnion id = R ∪ L

/-- **Three-colour orientation bridge.** -/
theorem triRefiner_of_physicalCycRefiner3 (h : PhysicalCycRefiner3) : TriRefiner := by
  obtain ⟨K, M, L0, h⟩ := h
  refine ⟨K, M, L0, ?_⟩
  intro V _ _ p G _ ω lam rho hω hω1 hlam hL0 hrho hscale hn hG hs X hXG hXdeg
  obtain ⟨R, lib, hRG, hRcyc, hRX, hRdeg, hpieces, hlib, hload, href⟩ :=
    h V p G ω lam rho hω hω1 hlam hL0 hrho hscale hn hG hs X hXG hXdeg
  have hXact : ActiveEdges F_tri p X := fun a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hXG hab))
  have hcons : ∀ (E : Finset (Sym2 V)), ActiveEdges F_tri p E → ∀ a b, s(a, b) ∈ E →
      triColour (p b) = triColour (p a) + 1 ∨ triColour (p a) = triColour (p b) + 1 := by
    intro E hE a b hab
    obtain ⟨k, hk⟩ := hE a b hab
    exact tri_link_consecutive _ _ _ hk
  have hOX : IsCyc (fun v => triColour (p v)) (orientTri p X) := isCyc_orientBy _ X
  have hall : IsCyc (fun v => triColour (p v)) (R ∪ orientTri p X) := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hRcyc e he
    · exact hOX e he
  have hXsym : symImage (orientTri p X) = X := symImage_orientBy (hcons X hXact)
  have hadj : ∀ x ∈ R ∪ orientTri p X, G.Adj x.1 x.2 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hRG x hx
    · exact SimpleGraph.mem_edgeFinset.mp (hXG (mem_orientBy.mp hx).1)
  have hpieceCyc : ∀ P ∈ lib, IsCyc (fun v => triColour (p v)) P :=
    fun P hP e he => hall e ((hpieces P hP).1 he)
  refine ⟨Finset (V × V), lib, symImage, symImage R, symImage_subset_edgeFinset G hRG, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := disjoint_symImageBy hall hRX
    rwa [hXsym] at this
  · intro v
    change ((incidentLoad (symImage R) v : ℕ) : ℝ) ≤ _
    rw [incidentLoad_symImageBy hRcyc]
    exact hRdeg v
  · intro L hLX hL
    have hLact : ActiveEdges F_tri p L := fun a b hab => hXact a b (hLX hab)
    have hbal : Cycles.Balanced (orientTri p L) := (isIntDiv_iff_balanced_tri p L hLact).mp hL
    obtain ⟨Q, hQ, hdisj, hU⟩ := href (orientTri p L) (orientBy_mono hLX) hbal
    refine ⟨Q, hQ, ?_, ?_⟩
    · intro P1 hP1 P2 hP2 hne
      have hc : IsCyc (fun v => triColour (p v)) (P1 ∪ P2) := by
        intro e he
        rcases mem_union.mp he with he | he
        · exact hpieceCyc P1 (hQ hP1) e he
        · exact hpieceCyc P2 (hQ hP2) e he
      exact disjoint_symImageBy hc (hdisj hP1 hP2 hne)
    · have himg : Q.biUnion symImage = symImage (Q.biUnion id) := by
        ext e
        simp only [symImage, mem_biUnion, mem_image, id]
        constructor
        · rintro ⟨P, hP, x, hx, rfl⟩
          exact ⟨x, ⟨P, hP, hx⟩, rfl⟩
        · rintro ⟨x, ⟨P, hP, hx⟩, rfl⟩
          exact ⟨P, hP, x, hx, rfl⟩
      rw [himg, hU, symImage_union, symImage_orientBy (hcons L hLact)]
  · intro P hP
    obtain ⟨hPsub, hPcard, hPbal⟩ := hpieces P hP
    refine ⟨?_, card_image_le.trans hPcard, ?_⟩
    · have := symImage_mono hPsub
      rw [symImage_union, hXsym] at this
      rwa [union_comm] at this
    · have hact := activeEdges_symImageF F_tri p G hG (fun x hx => hadj x (hPsub hx))
      rw [isIntDiv_iff_balanced_tri p _ hact]
      show Cycles.Balanced (orientBy _ _)
      rw [orientBy_symImage (hpieceCyc P hP)]
      exact hPbal
  · exact hlib
  · intro v
    have : (∑ i ∈ lib, incidentLoad (symImage i) v) = catalogLoad lib v := by
      unfold catalogLoad
      exact sum_congr rfl fun P hP => incidentLoad_symImageBy (hpieceCyc P hP) v
    rw [this]
    exact hload v

/-! ### Four-label specialisation: fusing the classes `2` and `3` of a Latin host -/

/-- Fusion of the Latin classes: `0, 1, 2, 3 ↦ 0, 1, 2, 2`. -/
def fuse : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- A Latin class representing each fused class. -/
def unfuse : Fin 3 → Fin 4 := ![0, 1, 2]

theorem triColour_fuse : ∀ i : Fin 4, triColour (fuse i) = latinColour i := by
  unfold triColour fuse latinColour; decide

theorem fuse_link : ∀ i j k : Fin 4, Link F_latin i j k → ∃ k', Link F_tri (fuse i) (fuse j) k' := by
  unfold Link F_latin F_tri fuse; decide

theorem fuse_unfuse : ∀ i : Fin 3, fuse (unfuse i) = i := by
  unfold fuse unfuse; decide

theorem unfuse_allowed : ∀ (j : Fin 4) (i : Fin 3),
    (∃ k, Link F_tri (fuse j) i k) → ∃ k, Link F_latin j (unfuse i) k := by
  unfold Link F_latin F_tri fuse unfuse; decide

/-- Fusing preserves the guarded supply with the same absolute bound. -/
theorem guardedSupply_fuse (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (a : ℝ) (hs : GuardedSupply p G (fun i j => ∃ k, Link F_latin i j k) D a) :
    GuardedSupply (fun v => fuse (p v)) G (fun i j => ∃ k, Link F_tri i j k) D a := by
  intro S hS i hguard
  refine (hs S hS (unfuse i) fun u hu => unfuse_allowed _ _ (hguard u hu)).trans ?_
  have hsub : guardedNeighbours p G S (unfuse i) ⊆
      guardedNeighbours (fun v => fuse (p v)) G S i := by
    intro w hw
    simp only [guardedNeighbours, mem_filter, mem_univ, true_and] at hw ⊢
    exact ⟨by rw [hw.1, fuse_unfuse], hw.2⟩
  exact_mod_cast card_le_card hsub

/-- **Four-label specialisation.** The three-colour physical refiner yields the four-label one. -/
theorem physicalCycRefiner_of_physicalCycRefiner3 (h : PhysicalCycRefiner3) :
    PhysicalCycRefiner := by
  obtain ⟨K, M, L0, h⟩ := h
  refine ⟨K, M, L0, ?_⟩
  intro V _ _ p G _ ω lam rho hω hω1 hlam hL0 hrho hscale hn hG hs X hXG hXdeg
  have hcol : (fun v => triColour (fuse (p v))) = fun v => latinColour (p v) :=
    funext fun v => triColour_fuse (p v)
  obtain ⟨R, lib, hRG, hRcyc, hRX, hRdeg, hpieces, hlib, hload, href⟩ :=
    h V (fun v => fuse (p v)) G ω lam rho hω hω1 hlam hL0 hrho hscale hn
      (fun u v huv => by
        obtain ⟨k, hk⟩ := hG u v huv
        exact fuse_link _ _ _ hk)
      (guardedSupply_fuse p G _ _ hs) X hXG hXdeg
  simp only [orientTri] at hRX hpieces href
  rw [hcol] at hRcyc hRX hpieces href
  exact ⟨R, lib, hRG, hRcyc, hRX, hRdeg, hpieces, hlib, hload, href⟩

theorem latinRefiner_of_physicalCycRefiner3 (h : PhysicalCycRefiner3) : LatinRefiner :=
  latinRefiner_of_physicalCycRefiner (physicalCycRefiner_of_physicalCycRefiner3 h)

theorem latinTarget_of_physicalCycRefiner3 (h : PhysicalCycRefiner3) : LatinTarget :=
  latinTarget_of_latinRefiner (latinRefiner_of_physicalCycRefiner3 h)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge
