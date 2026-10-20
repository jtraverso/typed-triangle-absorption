/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge

@[expose] public section

/-! Quantitative data for the same root catalogue produced from the actual
input X. All bounds and every residual partition use its single witness. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueBudget

open Finset Cycles Cycles.DenseRed

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev constant : ℕ := denseConst DenseProducer.Cdense Greedy.goodConst

abbrev Vert (X : Finset (V × V)) (σ : RootChannels.Perms (SplitPorts.root X)) :=
  RootPaths.Vert (SplitPorts.Port X) (RootChannels.Channel (SplitPorts.root X) σ)

def network (X : Finset (V × V)) (σ : RootChannels.Perms (SplitPorts.root X)) :
    Finset (Vert X σ × Vert X σ) :=
  RootPaths.arcs (RootChannels.src (SplitPorts.root X) σ)
    (RootChannels.dst (SplitPorts.root X) σ)

def input (X L : Finset (V × V)) (σ : RootChannels.Perms (SplitPorts.root X)) :
    Finset (Vert X σ × Vert X σ) :=
  (SplitPorts.arcsOf X L).map
    (liftArc (SplitPorts.Port X) (RootChannels.Channel (SplitPorts.root X) σ × Fin 2))

def colour (X : Finset (V × V)) (σ : RootChannels.Perms (SplitPorts.root X))
    (c : V → ZMod 3) : Vert X σ → ZMod 3 :=
  RootPaths.colour (RootChannels.src (SplitPorts.root X) σ) (c ∘ SplitPorts.root X)

def extra (X : Finset (V × V)) (σ : RootChannels.Perms (SplitPorts.root X)) :=
  ChannelCatalogue.pieces (RootChannels.src (SplitPorts.root X) σ)
    (RootChannels.dst (SplitPorts.root X) σ)

def Spec (X : Finset (V × V)) (c : V → ZMod 3)
    (σ : RootChannels.Perms (SplitPorts.root X)) : Prop :=
  IsCyc (colour X σ c) (network X σ ∪ input X X σ) ∧
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
    (R : Finset (((Vert X σ ⊕ U) × (Vert X σ ⊕ U))))
    (lib : Finset (Finset (((Vert X σ ⊕ U) × (Vert X σ ⊕ U))))),
    IsCyc (Sum.elim (colour X σ c) cU) R ∧
    Disjoint R ((network X σ ∪ input X X σ).map (liftArc (Vert X σ) U)) ∧
    (∀ P ∈ lib, P.Nonempty ∧
      P ⊆ R ∪ (network X σ ∪ input X X σ).map (liftArc (Vert X σ) U) ∧
      P.card ≤ 20 ∧ (Balanced P ∨ P ∈ CatalogueLift.lift U (extra X σ))) ∧
    (∀ a, catalogLoad lib (Sum.inl a) ≤ 1257) ∧
    (∀ u : U, catalogLoad lib (Sum.inr u) ^ 2 ≤ constant ^ 2 * (49 * X.card)) ∧
    lib.card ≤ (49 * constant + 16) * X.card ∧
    (∑ e ∈ CatalogueWeights.arcs lib, CatalogueWeights.weight lib e) ≤
      (980 * constant + 48) * X.card ∧
    R ∪ (network X σ).map (liftArc (Vert X σ) U) ⊆ CatalogueWeights.arcs lib ∧
    ∀ L ⊆ X, Balanced L →
      ∃ Q ⊆ lib, (Q : Set (Finset (((Vert X σ ⊕ U) × (Vert X σ ⊕ U))))).PairwiseDisjoint id ∧
        Q.biUnion id = R ∪ (network X σ ∪ input X L σ).map (liftArc (Vert X σ) U)

theorem exists_catalogue (X : Finset (V × V)) (c : V → ZMod 3) (hc : IsCyc c X) :
    ∃ σ : RootChannels.Perms (SplitPorts.root X), Spec X c σ := by
  obtain ⟨σ, hlift, hcat, hroute⟩ := RootCatalogue.exists_catalogue X c hc
  have hY : MaxDegLE (network X σ ∪ input X X σ) 17 := hlift.2.2.1
  have hYcard : (network X σ ∪ input X X σ).card ≤ 49 * X.card := hlift.2.2.2.1
  have hYcyc : IsCyc (colour X σ c) (network X σ ∪ input X X σ) := hlift.2.1
  have hN : MaxDegLE (network X σ) 16 :=
    RootAnchorBudget.network_degree (SplitPorts.root X) σ
  have hextra : (extra X σ).card ≤ 16 * X.card := by
    have h1 := ChannelCatalogue.size (RootChannels.src (SplitPorts.root X) σ)
      (RootChannels.dst (SplitPorts.root X) σ)
    have h2 := RootChannels.card_channels_le (SplitPorts.root X) σ
    rw [SplitPorts.port_card] at h2
    exact h1.trans (by omega)
  obtain ⟨U, hUf, hUd, cU, R, lib, hRcyc, hRdis, hp, hold, hnew, hcount, hmass, hpart⟩ := hcat
  have hold' : ∀ a, catalogLoad lib (Sum.inl a) ≤ 1257 := by
    apply RootAnchorBudget.old_load_cap (network X σ ∪ input X X σ)
      (network X σ) lib hY hN
    intro a
    exact (hold a).trans (Nat.add_le_add_left
      (ChannelCatalogue.load_le (RootChannels.src (SplitPorts.root X) σ)
        (RootChannels.dst (SplitPorts.root X) σ) a) _)
  have hpart' : ∀ L ⊆ X, Balanced L →
      ∃ Q ⊆ lib, (Q : Set (Finset (((Vert X σ ⊕ U) × (Vert X σ ⊕ U))))).PairwiseDisjoint id ∧
        Q.biUnion id = R ∪ (network X σ ∪ input X L σ).map (liftArc (Vert X σ) U) := by
    intro L hL hb
    exact hpart (input X L σ)
      (map_subset_map.mpr (SplitPorts.arcsOf_subset X L)) (hroute L hL hb)
  have hcover : R ∪ (network X σ).map (liftArc (Vert X σ) U) ⊆
      CatalogueWeights.arcs lib := by
    obtain ⟨Q, hQ, _, hQeq⟩ := hpart' ∅ (empty_subset X) balanced_empty
    have hempty : input X ∅ σ = ∅ := by simp [input, SplitPorts.arcsOf]
    rw [hempty, union_empty] at hQeq
    intro e he
    rw [← hQeq] at he
    obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨P, hQ hP, heP⟩
  refine ⟨σ, hYcyc, U, hUf, hUd, cU, R, lib, hRcyc, hRdis, ?_, hold', ?_, ?_, ?_,
    hcover, hpart'⟩
  · intro P hP
    obtain ⟨hn, hs, hk, hb⟩ := hp P hP
    exact ⟨hn, hs, by simpa using hk, hb⟩
  · intro u
    exact (hnew u).trans (Nat.mul_le_mul_left (constant ^ 2) hYcard)
  · change lib.card ≤ constant * (network X σ ∪ input X X σ).card + (extra X σ).card at hcount
    calc
      _ ≤ constant * (network X σ ∪ input X X σ).card + (extra X σ).card := hcount
      _ ≤ constant * (49 * X.card) + 16 * X.card :=
        Nat.add_le_add (Nat.mul_le_mul_left constant hYcard) hextra
      _ = _ := by ring
  · change (∑ e ∈ CatalogueWeights.arcs lib, CatalogueWeights.weight lib e) ≤
      20 * (constant * (network X σ ∪ input X X σ).card) + 3 * (extra X σ).card at hmass
    calc
      _ ≤ 20 * (constant * (network X σ ∪ input X X σ).card) + 3 * (extra X σ).card := hmass
      _ ≤ 20 * (constant * (49 * X.card)) + 3 * (16 * X.card) :=
        Nat.add_le_add (Nat.mul_le_mul_left 20 (Nat.mul_le_mul_left constant hYcard))
          (Nat.mul_le_mul_left 3 hextra)
      _ = _ := by ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueBudget

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueBudget.exists_catalogue
