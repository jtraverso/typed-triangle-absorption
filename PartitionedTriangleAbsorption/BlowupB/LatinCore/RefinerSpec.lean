/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Target

@[expose] public section

/-!
# The Latin core: the missing statement

`LatinRefiner` is the single statement that the reduction `latinTarget_of_latinRefiner`
(`BlowupB/LatinCore/Reduction.lean`) needs in order to prove `LatinTarget`. It is a *balanced
refiner* for the Latin core `F_latin = {012, 013}` at the scale of the existing Even3 refiner
(`FinT.exists_component_refiner`): a sparse reserve graph `R` and a finite library of bounded,
integrally divisible pieces such that, for every integrally divisible leftover `L ⊆ X`, the graph
`R ∪ L` is an edge-disjoint union of library pieces.

Compared with `FinT.exists_component_refiner` (which is proved, axiom-clean) the differences are:

* the pieces must be `IsIntDiv p F_latin` (balanced at every vertex for the cyclic orientation
  `0 → 1 → {2,3} → 0`, see `Flow.lean`), not merely `Even3`;
* the reserve is physical (`R ⊆ G.edgeFinset`), not a set of virtual edges;
* every bound carries a factor `1 / ω` and an unspecified constant `M`.

The constants `K` (piece size), `M` (degree / load / count constant) and `L0` (how small `lam`
must be compared with `ω ^ 3`) are existential and may be arbitrarily large.

This module only states the open interface. No inhabitant of `LatinRefiner` is assumed.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.AntiEdgeSelection

/-- **The balanced (Latin) refiner at the Even3-refiner scale.**

For every host whose edges are allowed for `F_latin` and which has guarded extension supply of
order `2 ^ 21` at density `ω`, every reserve density `rho` and refiner scale `lam` with
`2 ^ 24 * rho ≤ lam ^ 2`, `2 ^ L0 * lam ≤ ω ^ 3`, and every reserve `X ⊆ G` of maximum degree
`≤ 2 rho n`, there are a reserve `R ⊆ G` disjoint from `X` and a finite library of pieces `B i`
such that

* `R ∪ L` is a disjoint union of library pieces for every integrally divisible `L ⊆ X`;
* every piece lies in `X ∪ R`, has at most `K` edges and is integrally `F_latin`-divisible;
* `R` has maximum degree, the library has total vertex load, and the library has size, at most
  `M lam n / ω`, `M lam n / ω` and `M lam n ^ 2 / ω` respectively. -/
def LatinRefiner : Prop :=
  ∃ K M L0 : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 → 0 < lam → 2 ^ L0 * lam ≤ ω ^ 3 → 0 < rho → 2 ^ 24 * rho ≤ lam ^ 2 →
    1 ≤ rho * Fintype.card V →
    (∀ u v, G.Adj u v → ∃ k, Link F_latin (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F_latin i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
      ∃ (ι : Type) (lib : Finset ι) (B : ι → Finset (Sym2 V)) (R : Finset (Sym2 V)),
        R ⊆ G.edgeFinset ∧ Disjoint R X ∧
        DegBounded R (M * lam * Fintype.card V / ω) ∧
        RefinerAssembly.RefinesReserve (p := p) (F := F_latin) lib B X R ∧
        (∀ i ∈ lib, B i ⊆ X ∪ R ∧ (B i).card ≤ K ∧ IsIntDiv p F_latin (B i)) ∧
        ((lib.card : ℝ) ≤ M * lam * (Fintype.card V : ℝ) ^ 2 / ω) ∧
        ∀ v, ((∑ i ∈ lib, incidentLoad (B i) v : ℕ) : ℝ) ≤ M * lam * Fintype.card V / ω

end PartitionedTriangleAbsorption.BlowupB.LatinCore


