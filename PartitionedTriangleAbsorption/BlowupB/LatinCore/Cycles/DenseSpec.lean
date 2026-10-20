/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoscopicSpec

@[expose] public section

/-!
# The dense hub-level refiner (the exact remaining lemma)

`DenseRefinerWith C K` is the **dense** analogue of `MesoscopicRefinerWith`: the input is an
arbitrary cyclically tripartite digraph `D` on a finite vertex set `H` of size `N`
(no degree bound, so up to `N^2/3` arcs), and the budgets are expressed in terms of `N`:

* `lib.card ≤ C N^2`,
* catalogue load `∑_{P ∈ lib} deg_P v ≤ C N` at every vertex,

with the same positive exact-partition requirement for every balanced `L ⊆ D`.

This is **not** asserted here; it is an OPEN proposition.  `DenseReduction.lean` proves
(without `sorry`) that `DenseRefiner → MesoscopicRefiner`.  The point of the reduction is that
a bounded-degree input with `m` arcs is replaced by a dense input on only `N = O(√m)` hubs, so
the mesoscopic budget `C √m` becomes the *linear-in-degree* budget `C N` of the dense regime.

`HasGoodPartition A c Y` is the combinatorial input of the reduction: a monochromatic vertex
partition without internal arcs whose quotient is simple, with `N^2 ≤ A |Y|` parts and part arc
loads `load_a^2 ≤ A |Y|`.  `GreedyPartition.lean` proves that every `Y` of maximum degree `≤ 17`
has one with an absolute `A`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

/-- **Dense refiner with explicit constants** (OPEN; no inhabitant is asserted). -/
def DenseRefinerWith (C K : ℕ) : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (c : H → ZMod 3) (D : Finset (H × H)),
    IsCyc c D →
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset ((H ⊕ U) × (H ⊕ U)))
      (lib : Finset (Finset ((H ⊕ U) × (H ⊕ U)))),
      IsCyc (Sum.elim c cU) R ∧ Disjoint R (D.map (liftArc H U)) ∧
      (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ D.map (liftArc H U) ∧ P.card ≤ K ∧ Balanced P) ∧
      lib.card ≤ C * Fintype.card H ^ 2 ∧
      (∀ v, catalogLoad lib v ≤ C * Fintype.card H) ∧
      ∀ L ⊆ D, Balanced L →
        ∃ Q ⊆ lib, (Q : Set (Finset ((H ⊕ U) × (H ⊕ U)))).PairwiseDisjoint id ∧
          Q.biUnion id = R ∪ L.map (liftArc H U)

/-- **The dense refiner** (OPEN): absolute constants exist. -/
def DenseRefiner : Prop := ∃ C K : ℕ, 1 ≤ C ∧ 3 ≤ K ∧ DenseRefinerWith C K

/-- A good hub partition of `Y` with constant `A`. -/
def HasGoodPartition {V : Type} [DecidableEq V] (A : ℕ) (c : V → ZMod 3)
    (Y : Finset (V × V)) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (p : V → P) (col : P → ZMod 3),
    (∀ e ∈ Y, col (p e.1) = c e.1 ∧ col (p e.2) = c e.2) ∧
    (∀ e ∈ Y, p e.1 ≠ p e.2) ∧
    (∀ e ∈ Y, ∀ e' ∈ Y, p e.1 = p e'.1 → p e.2 = p e'.2 → e = e') ∧
    Fintype.card P ^ 2 ≤ A * Y.card ∧
    (∀ a, (Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card ^ 2 ≤ A * Y.card)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
