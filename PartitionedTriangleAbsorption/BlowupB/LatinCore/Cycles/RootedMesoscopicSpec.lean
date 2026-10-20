/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseReduction

@[expose] public section

/-! Mesoscopic witnesses with their old-vertex load, on the very same reserve and catalogue.
This is stronger than separate existential assertions about two unrelated catalogues. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseRed

open Finset MesoCutHub

def RootedMesoscopicFor (C K : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (c : V → ZMod 3) (Y : Finset (V × V)) : Prop :=
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
    (R : Finset ((V ⊕ U) × (V ⊕ U)))
    (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U)))),
    IsCyc (Sum.elim c cU) R ∧ Disjoint R (Y.map (liftArc V U)) ∧
    (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ Y.map (liftArc V U) ∧
      P.card ≤ K ∧ Balanced P) ∧
    lib.card ≤ C * Y.card ∧
    (∀ v, catalogLoad lib v ^ 2 ≤ C ^ 2 * Y.card) ∧
    (∀ L ⊆ Y, Balanced L →
      ∃ Q ⊆ lib, (Q : Set (Finset ((V ⊕ U) × (V ⊕ U)))).PairwiseDisjoint id ∧
        Q.biUnion id = R ∪ L.map (liftArc V U)) ∧
    ∀ v : V, catalogLoad lib (Sum.inl v) ≤ 73 * deg Y v

theorem RootedMesoscopicFor.forget {C K : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {c : V → ZMod 3} {Y : Finset (V × V)} (h : RootedMesoscopicFor C K c Y) :
    MesoscopicFor C K c Y := by
  obtain ⟨U, hUf, hUd, cU, R, lib, hcyc, hdis, hv, hc, hl, hp, _⟩ := h
  exact ⟨U, hUf, hUd, cU, R, lib, hcyc, hdis, hv, hc, hl, hp⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseRed
