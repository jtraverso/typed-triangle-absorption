/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CompletedCatalogue
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic

@[expose] public section

/-! One catalogue, fixed before every demand, includes the unused channel paths.
Their balance is deferred to physical root identification. No embedding is assumed. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue

open Finset Cycles Cycles.DenseRed

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 100000

theorem subset_lift {P W : Type} [DecidableEq P] [DecidableEq W]
    (f : P ↪ W) (S : Finset P) (L : Finset W) (hL : L ⊆ S.map f) :
    ∃ T ⊆ S, T.map f = L := by
  refine ⟨S.filter (fun e => f e ∈ L), filter_subset _ _, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, rfl⟩ := mem_map.mp ha
    exact (mem_filter.mp he).2
  · intro ha
    obtain ⟨e, he, rfl⟩ := mem_map.mp (hL ha)
    exact mem_map.mpr ⟨e, mem_filter.mpr ⟨he, ha⟩, rfl⟩

def CatalogueFor {P E : Type} [Fintype P] [DecidableEq P]
    [Fintype E] [DecidableEq E] (src dst : E → P) (c : RootPaths.Vert P E → ZMod 3)
    (S : Finset (P × P)) (C K : ℕ) : Prop :=
  CompletedCatalogue.Spec c (RootPaths.arcs src dst) (S.map (liftArc P (E × Fin 2)))
    (ChannelCatalogue.pieces src dst) C K 3

theorem assemble {P E : Type} [Fintype P] [DecidableEq P]
    [Fintype E] [DecidableEq E] (src dst : E → P) (c : RootPaths.Vert P E → ZMod 3)
    (S : Finset (P × P)) (C K : ℕ)
    (hmeso : RootedMesoscopicFor C K c
      (RootPaths.arcs src dst ∪ S.map (liftArc P (E × Fin 2)))) :
    CatalogueFor src dst c S C K := by
  apply CompletedCatalogue.assemble c _ _ _ C K 3
    (RootLift.disjoint_input src dst S) ?_ ?_ hmeso
  · intro Q hQ
    obtain ⟨e, _, rfl⟩ := mem_image.mp hQ
    refine ⟨?_, ?_, (ChannelCatalogue.card_path src dst e).le⟩
    · apply card_pos.mp
      rw [ChannelCatalogue.card_path]
      decide
    · intro a ha
      exact mem_biUnion.mpr ⟨e, mem_univ _, ha⟩
  · intro L hL A hA hb
    obtain ⟨T, _, rfl⟩ := subset_lift (liftArc P (E × Fin 2)) S L hL
    exact UnusedChannelSelection.unused_of_completed src dst T A hA hb

def Spec {P V : Type} [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V] (root : P → V) (c : V → ZMod 3)
    (S : Finset (P × P)) (σ : RootChannels.Perms root) : Prop :=
  CatalogueFor (RootChannels.src root σ) (RootChannels.dst root σ)
    (RootPaths.colour (RootChannels.src root σ) (c ∘ root)) S
    (denseConst DenseProducer.Cdense Greedy.goodConst) 20

theorem catalogue_of_mesoscopic {P V : Type} [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V] (root : P → V) (c : V → ZMod 3)
    (S : Finset (P × P)) (σ : RootChannels.Perms root)
    (h : RootMesoscopic.MesoscopicSpec root c S σ) : Spec root c S σ := by
  exact assemble _ _ _ _ _ _ h

/-- The input supplies the fixed catalogue and routing; no producer is a premise. -/
theorem exists_catalogue {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V × V)) (c : V → ZMod 3) (hc : IsCyc c X) :
    ∃ σ : RootChannels.Perms (SplitPorts.root X),
      RootInput.LiftSpec (SplitPorts.root X) c (SplitPorts.arcs X) (49 * X.card) σ ∧
      Spec (SplitPorts.root X) c (SplitPorts.arcs X) σ ∧
      ∀ L ⊆ X, Balanced L →
        RootInput.Completed (SplitPorts.root X) σ (SplitPorts.arcsOf X L) := by
  obtain ⟨σ, hlift, hmeso, hroute⟩ := RootMesoscopic.exists_refined_input X c hc
  exact ⟨σ, hlift, catalogue_of_mesoscopic _ _ _ _ hmeso, hroute⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue.assemble
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue.exists_catalogue
