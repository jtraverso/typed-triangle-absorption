/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogue
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FibrePathTransport
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Every piece of the completed root catalogue is balanced after one
arc-disjoint path replacement. The additional channel pieces close because
their endpoint ports have the same prescribed physical root. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueTransport

open Finset Cycles Positivization

set_option synthInstance.maxSize 1024

variable {P E U V : Type} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [DecidableEq V]

def channelVertex (src dst : E → P) (e : E) (j : ℕ) : RootPaths.Vert P E ⊕ U :=
  if j = 0 then Sum.inl (Sum.inl (src e))
  else if j = 1 then Sum.inl (Sum.inr (e,0))
  else if j = 2 then Sum.inl (Sum.inr (e,1)) else Sum.inl (Sum.inl (dst e))

omit [Fintype P] [Fintype E] [Fintype U] in
theorem channel_as_walk (src dst : E → P) (e : E) :
    (RootPaths.pathArcs src dst e).map (liftArc (RootPaths.Vert P E) U) =
      pathArcs (channelVertex src dst e) 3 := by
  have hr : range 3 = ({0,1,2} : Finset ℕ) := by decide
  simp [RootPaths.pathArcs, liftArc, pathArcs, hr, channelVertex]
  rfl

omit [Fintype P] [Fintype E] [Fintype U] in
theorem channel_balanced (root : P → V) (src dst : E → P) (e : E)
    (f : RootPaths.Vert P E ⊕ U → V)
    (path : ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U)) → Finset (V × V))
    (hpin : ∀ p, f (Sum.inl (Sum.inl p)) = root p)
    (hroot : root (src e) = root (dst e))
    (hdis : (((RootPaths.pathArcs src dst e).map (liftArc (RootPaths.Vert P E) U)) :
      Set ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))).PairwiseDisjoint path)
    (hnet : ∀ a ∈ (RootPaths.pathArcs src dst e).map (liftArc (RootPaths.Vert P E) U),
      ∀ r, net (path a) r = (if f a.2 = r then 1 else 0) - (if f a.1 = r then 1 else 0)) :
    Balanced (((RootPaths.pathArcs src dst e).map (liftArc (RootPaths.Vert P E) U)).biUnion path) := by
  rw [channel_as_walk] at hdis hnet ⊢
  apply FibrePathTransport.closed_walk_replace (channelVertex src dst e) 3 f path ?_
    hdis hnet ?_
  · intro i hi j hj hij
    have hi3 : i < 3 := mem_range.mp hi
    have hj3 : j < 3 := mem_range.mp hj
    have hfirst := congrArg Prod.fst hij
    interval_cases i <;> interval_cases j <;> simp_all [channelVertex]
  · simpa [channelVertex, hpin] using hroot.symm

theorem catalogue_balanced (root : P → V) (src dst : E → P)
    (lib : Finset (Finset (((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U)))))
    (f : RootPaths.Vert P E ⊕ U → V)
    (path : ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U)) → Finset (V × V))
    (hpin : ∀ p, f (Sum.inl (Sum.inl p)) = root p)
    (hroot : ∀ e, root (src e) = root (dst e))
    (hp : ∀ Q ∈ lib, Balanced Q ∨
      Q ∈ CatalogueLift.lift U (ChannelCatalogue.pieces src dst))
    (hdis : (CatalogueWeights.arcs lib :
      Set ((RootPaths.Vert P E ⊕ U) × (RootPaths.Vert P E ⊕ U))).PairwiseDisjoint path)
    (hnet : ∀ a ∈ CatalogueWeights.arcs lib, ∀ r, net (path a) r =
      (if f a.2 = r then 1 else 0) - (if f a.1 = r then 1 else 0)) :
    ∀ Q ∈ lib, Balanced (Q.biUnion path) := by
  intro Q hQ
  have hs : Q ⊆ CatalogueWeights.arcs lib :=
    fun a ha => mem_biUnion.mpr ⟨Q, hQ, ha⟩
  have hd : (Q : Set _).PairwiseDisjoint path :=
    fun a ha b hb hab => hdis (hs ha) (hs hb) hab
  have hn := fun a ha r => hnet a (hs ha) r
  rcases hp Q hQ with hb | hextra
  · exact PathReplacement.balanced_replace Q f path hd hn hb
  · obtain ⟨T, hT, rfl⟩ := mem_image.mp hextra
    obtain ⟨e, _, rfl⟩ := mem_image.mp hT
    exact channel_balanced root src dst e f path hpin (hroot e) hd hn

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueTransport

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueTransport.channel_balanced
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueTransport.catalogue_balanced
