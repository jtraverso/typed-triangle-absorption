/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueBudget
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueColours
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget

@[expose] public section

/-! The root catalogue supplies the hypotheses of the weighted physical
constructor. This theorem chooses the catalogue, anchors and paths from X
and the host supplies, all before any balanced residual input is chosen. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalEmbedding

open Finset Cycles AntiEdgeSelection StructuralF3General PaddedNoCommon WeightedEdgeLedger

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

abbrev factor : ℕ := WeightedEmbeddingBudget.factor RootCatalogueBudget.constant 20

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

theorem exists_embedding (p : V → Fin 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset (V × V)) (B : Finset (Sym2 V)) (ω t n : ℝ)
    (_hω : 0 < ω) (ht : 0 < t) (ht1 : t ≤ 1) (hn : 0 < n)
    (hsize : 1 ≤ t ^ 2 * n) (hsmall : 32 * (factor : ℝ) * t ≤ ω)
    (hXcyc : IsCyc (CatalogueColours.colour ∘ p) X)
    (hXcard : (X.card : ℝ) ≤ t ^ 2 * n ^ 2)
    (hXdeg : ∀ r, (deg X r : ℝ) ≤ 2 * t ^ 2 * n)
    (hB : DegBounded B (2 * t ^ 2 * n))
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 (ω * n)) :
    ∃ (σ : RootChannels.Perms (SplitPorts.root X))
      (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset (((RootCatalogueBudget.Vert X σ ⊕ U) × (RootCatalogueBudget.Vert X σ ⊕ U))))
      (lib : Finset (Finset (((RootCatalogueBudget.Vert X σ ⊕ U) × (RootCatalogueBudget.Vert X σ ⊕ U)))))
      (f : RootCatalogueBudget.Vert X σ ⊕ U → V)
      (x y z : ((RootCatalogueBudget.Vert X σ ⊕ U) × (RootCatalogueBudget.Vert X σ ⊕ U)) → V),
      let cA := Sum.elim (RootCatalogueBudget.colour X σ (CatalogueColours.colour ∘ p)) cU
      let I := (CatalogueWeights.arcs lib).filter (fun e =>
        e ∈ (RootCatalogueBudget.input X X σ).map (liftArc (RootCatalogueBudget.Vert X σ) U))
      IsCyc cA R ∧
      Disjoint R ((RootCatalogueBudget.network X σ ∪ RootCatalogueBudget.input X X σ).map
        (liftArc (RootCatalogueBudget.Vert X σ) U)) ∧
      (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪
        (RootCatalogueBudget.network X σ ∪ RootCatalogueBudget.input X X σ).map
          (liftArc (RootCatalogueBudget.Vert X σ) U) ∧ P.card ≤ 20 ∧
        (Balanced P ∨ P ∈ CatalogueLift.lift U (RootCatalogueBudget.extra X σ))) ∧
      IsCyc cA (CatalogueWeights.arcs lib) ∧
      lib.card ≤ (49 * RootCatalogueBudget.constant + 16) * X.card ∧
      (∀ v, f (Sum.inl (Sum.inl v)) = SplitPorts.root X v) ∧
      (∀ v, p (f v) = CatalogueColours.toFin (cA v)) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I,
        p (x e) = CatalogueColours.toFin (cA e.2) ∧
        p (y e) = CatalogueEmbedding.third (CatalogueColours.toFin (cA e.1))
          (CatalogueColours.toFin (cA e.2)) ∧
        p (z e) = CatalogueColours.toFin (cA e.1) ∧
        IsPath4 G (f e.1) (x e) (y e) (z e) (f e.2)) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I,
        Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) B) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I, ∀ q ∈ CatalogueWeights.arcs lib \ I,
        e ≠ q → Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2))
          (pathEdges (f q.1) (x q) (y q) (z q) (f q.2))) ∧
      (∀ r, (∑ e ∈ I, endpointCharge (CatalogueWeights.weight lib e : ℝ)
          (f e.1) (f e.2) r) +
        (∑ e ∈ CatalogueWeights.arcs lib \ I, (CatalogueWeights.weight lib e : ℝ) *
          (incidentLoad (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) r : ℝ)) ≤
          3 * (factor : ℝ) * t * n) ∧
      R ∪ (RootCatalogueBudget.network X σ).map (liftArc (RootCatalogueBudget.Vert X σ) U) ⊆
        CatalogueWeights.arcs lib ∧
      ∀ L ⊆ X, Balanced L →
        ∃ Q ⊆ lib, (Q : Set (Finset (((RootCatalogueBudget.Vert X σ ⊕ U) ×
          (RootCatalogueBudget.Vert X σ ⊕ U))))).PairwiseDisjoint id ∧
          Q.biUnion id = R ∪ (RootCatalogueBudget.network X σ ∪ RootCatalogueBudget.input X L σ).map
            (liftArc (RootCatalogueBudget.Vert X σ) U) := by
  obtain ⟨σ, hYcyc, U, hUf, hUd, cU, R, lib, hRcyc, hRdis, hp, hold, hnew,
    hcount, hmass, hcover, hpart⟩ := RootCatalogueBudget.exists_catalogue X
      (CatalogueColours.colour ∘ p) hXcyc
  let cA := Sum.elim (RootCatalogueBudget.colour X σ (CatalogueColours.colour ∘ p)) cU
  let label := fun a => CatalogueColours.toFin (cA a)
  let I := (CatalogueWeights.arcs lib).filter (fun e =>
    e ∈ (RootCatalogueBudget.input X X σ).map (liftArc (RootCatalogueBudget.Vert X σ) U))
  let q : ℝ := factor
  let T := q * t * n
  let M := q * t ^ 2 * n ^ 2
  have hq := WeightedEmbeddingBudget.factor_bounds RootCatalogueBudget.constant 20
  have hq1 : 1 ≤ q := by dsimp [q, factor]; linarith [hq.1]
  have hq0 : 0 ≤ q := by linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcyc : IsCyc cA (CatalogueWeights.arcs lib) := by
    intro e he
    obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
    rcases mem_union.mp ((hp P hP).2.1 heP) with heR | heY
    · exact hRcyc e heR
    · obtain ⟨a, ha, rfl⟩ := mem_map.mp heY
      exact hYcyc a ha
  have hproper : ∀ e ∈ CatalogueWeights.arcs lib, label e.1 ≠ label e.2 :=
    fun e he => CatalogueColours.fin_ne_of_step (hcyc e he)
  have hpin : ∀ a r, RootAnchorBudget.pin (SplitPorts.root X) a = some r → p r = label a := by
    intro a r ha
    rcases a with a | u
    · rcases a with v | j
      · have hr : SplitPorts.root X v = r := by simpa [RootAnchorBudget.pin] using ha
        subst r
        exact (ZMod.finEquiv 3).symm_apply_apply (p (SplitPorts.root X v)) |>.symm
      · simp [RootAnchorBudget.pin] at ha
    · simp [RootAnchorBudget.pin] at ha
  have hpinCap : ∀ r, CatalogueAnchors.pinnedLoad (RootAnchorBudget.pin (SplitPorts.root X))
      (fun a => (catalogLoad lib a : ℝ)) r ≤ T := by
    intro r
    apply WeightedEmbeddingBudget.pinned_load q t n _ hq.1 ht.le ht1 hn.le
    calc _ ≤ 1257 * (deg X r : ℝ) :=
            RootAnchorBudget.pinned_load_le X _ (fun v => by exact_mod_cast hold (Sum.inl v)) r
      _ ≤ 1257 * (2 * t ^ 2 * n) := mul_le_mul_of_nonneg_left (hXdeg r) (by norm_num)
      _ = _ := by ring
  have hweight : ∀ a, (catalogLoad lib a : ℝ) ≤ T := by
    intro a
    apply CatalogueScaleBudget.vertex_load (RootCatalogueBudget.constant : ℝ) q t n X.card
      (catalogLoad lib a) (Nat.cast_nonneg _) ht ht1 hn hsize hXcard (Nat.cast_nonneg _) hq.2.2.1
    rcases a with a | u
    · exact Or.inl (by exact_mod_cast hold a)
    · exact Or.inr (by exact_mod_cast hnew u)
  have htotal : (∑ a, (catalogLoad lib a : ℝ)) ≤ M := by
    have hnat : (∑ a, catalogLoad lib a) ≤ (1960 * RootCatalogueBudget.constant + 96) * X.card := by
      rw [CataloguePrecharge.total_degree]
      calc _ ≤ 2 * ((980 * RootCatalogueBudget.constant + 48) * X.card) := Nat.mul_le_mul_left 2 hmass
        _ = _ := by ring
    apply CatalogueScaleBudget.mass (RootCatalogueBudget.constant : ℝ) q t n X.card _
      (Nat.cast_nonneg _) hXcard ?_ (by exact_mod_cast hnat)
    have hc : 0 ≤ (RootCatalogueBudget.constant : ℝ) := Nat.cast_nonneg _
    have hqq := hq.2.1
    norm_num at hqq
    dsimp [q, factor]
    nlinarith
  have hbudget : 4 * M / T + 4 + 2 * (2 * t ^ 2 * n + T + 2 * T) < ω * n :=
    WeightedEmbeddingBudget.exclusion q t n ω M (2 * t ^ 2 * n) T hq1 ht ht1 hn
      hsize le_rfl le_rfl le_rfl hsmall
  have hanchor : M < (ω * n) * T :=
    CatalogueScaleBudget.anchor_budget _ _ _ _ _ (by positivity) hT hT.le hM hbudget
  have hsupply : ∀ i, ω * n ≤ (univ.filter (fun r : V => p r = i)).card := by
    intro i
    simpa [guardedNeighbours] using hs ∅ (by simp) i (by simp)
  obtain ⟨f, x, y, z, hfix, hcolour, hpath, havoid, hdis, hload⟩ :=
    CatalogueEmbedding.exists_embedding lib I (filter_subset _ _) (RootAnchorBudget.pin (SplitPorts.root X))
      label p G B (ω * n) (2 * t ^ 2 * n) T T M (by positivity) hT hT.le hs hB
      hpin hproper hpinCap hweight hsupply hanchor htotal hbudget
  refine ⟨σ, U, hUf, hUd, cU, R, lib, f, x, y, z, hRcyc, hRdis, hp, hcyc, hcount,
    ?_, hcolour, hpath, havoid, hdis, ?_, hcover, hpart⟩
  · intro v
    exact hfix (Sum.inl (Sum.inl v)) (SplitPorts.root X v) rfl
  · intro r
    have hh := hload r
    change _ ≤ 3 * q * t * n
    convert hh using 1
    dsimp [T]
    ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalEmbedding

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalEmbedding.exists_embedding
