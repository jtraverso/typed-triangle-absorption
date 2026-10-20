/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PortChannels
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelSelection

@[expose] public section

/-! Cut expansion gives a subset of real indexed directed channels for every
unit demand. The network is fixed before the demand. This does not construct
the expanding network or embed its channels in the physical host. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.UnitChannelRouting

open Finset ChannelSelection

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def channelGraph (src dst : E → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)
  symm := ⟨by
    intro u v h
    obtain ⟨huv, e, h⟩ := h
    exact ⟨huv.symm, e, h.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- All channel choices are constructed. No orientation, integer flow or
per-demand matching is required as a premise. -/
theorem exists_unit_routing (src dst : E → V) (hnoloop : ∀ e, src e ≠ dst e)
    (hexp : ∀ S : Finset V, min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
      ∑ u ∈ Sᶜ, ∑ v ∈ S, (capacity src dst u v : ℝ))
    (b : V → ℤ) (hsum : ∑ v, b v = 0) (hb : ∀ v, |(b v : ℝ)| ≤ 1) :
    ∃ T : Finset E, ∀ v,
      ((T.filter (fun e => dst e = v)).card : ℤ) -
        ((T.filter (fun e => src e = v)).card : ℤ) = b v := by
  classical
  let G := channelGraph src dst
  letI : DecidableRel G.Adj := Classical.decRel _
  have horient : ∀ e : G.edgeSet, ∃ d : G.Dart, d.edge = e.val := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v => exact ⟨⟨(u,v), he⟩, rfl⟩
  choose o ho using horient
  have hsupp : ∀ u v, ¬G.Adj u v → capacity src dst u v = 0 := by
    intro u v huv
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro e _ he
    apply huv
    obtain ⟨hes, hed⟩ := he
    exact ⟨by simpa only [← hes, ← hed] using hnoloop e, e, Or.inl ⟨hes, hed⟩⟩
  obtain ⟨f, hfcap, hfdiv⟩ := PortFlow.integer_directed_flow_of_cut G o ho
    (capacity src dst) hsupp b hsum
    (fun S => (PortFlow.unit_demand_cut b hsum hb S).trans (hexp S))
  obtain ⟨T, _, hT⟩ := exists_selection_with_demand src dst f hfcap b hfdiv
  exact ⟨T, hT⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.UnitChannelRouting

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.UnitChannelRouting.exists_unit_routing
