/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

@[expose] public section

/-!
# Bounded directed cycles in cyclically tripartite digraphs

Self-contained vocabulary (only Mathlib is imported) for the reduced combinatorial target
`CycleShortener` of `ARISTOTLE_CRUX_CICLOS_ACOTADOS_20261015.md`, section A.

* A digraph on a vertex type `W` is a `Finset (W × W)` of arcs `(tail, head)`.
* A colouring `c : W → ZMod 3` makes it *cyclically tripartite* (`IsCyc`) when every arc goes
  from class `i` to class `i + 1`. Such a digraph has no loops and no antiparallel pairs, so it is
  the same thing as a simple tripartite graph with its forced orientation `0 → 1 → 2 → 0`.
* `Balanced E`: in-degree equals out-degree at every vertex.
* `IsDirCycle E`: `E` is a *minimal nonempty balanced* arc set. For arc sets this is exactly a
  directed simple cycle (every nonempty balanced arc set contains a directed simple cycle, which
  is itself balanced); its length is `E.card`.
* `IsCyclePartition K P E`: `P` is a family of pairwise disjoint directed simple cycles, each with
  at most `K` arcs, whose union is exactly `E` (a positive, multiplicity-free edge partition).
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

section Basic

variable {W : Type*} [DecidableEq W]

/-- Every arc goes from colour class `i` to colour class `i + 1`. -/
def IsCyc (c : W → ZMod 3) (E : Finset (W × W)) : Prop :=
  ∀ e ∈ E, c e.2 = c e.1 + 1

/-- In-degree of `v` in the arc set `E`. -/
def inDeg (E : Finset (W × W)) (v : W) : ℕ := (E.filter (fun e => e.2 = v)).card

/-- Out-degree of `v` in the arc set `E`. -/
def outDeg (E : Finset (W × W)) (v : W) : ℕ := (E.filter (fun e => e.1 = v)).card

/-- Total degree (number of incident arcs for loopless digraphs). -/
def deg (E : Finset (W × W)) (v : W) : ℕ := inDeg E v + outDeg E v

/-- Balanced (Eulerian) arc set: in-degree equals out-degree everywhere. -/
def Balanced (E : Finset (W × W)) : Prop := ∀ v, inDeg E v = outDeg E v

/-- Maximum degree at most `d`. -/
def MaxDegLE (E : Finset (W × W)) (d : ℕ) : Prop := ∀ v, deg E v ≤ d

/-- A directed simple cycle, as an arc set: a minimal nonempty balanced arc set. -/
def IsDirCycle (E : Finset (W × W)) : Prop :=
  E.Nonempty ∧ Balanced E ∧ ∀ F ⊆ E, F.Nonempty → Balanced F → F = E

/-- `P` partitions `E` into pairwise disjoint directed simple cycles with at most `K` arcs. -/
def IsCyclePartition (K : ℕ) (P : Finset (Finset (W × W))) (E : Finset (W × W)) : Prop :=
  (∀ p ∈ P, IsDirCycle p ∧ p.card ≤ K) ∧ (P : Set (Finset (W × W))).PairwiseDisjoint id ∧
    P.biUnion id = E

omit [DecidableEq W] in
lemma IsCyc.mono {c : W → ZMod 3} {E F : Finset (W × W)} (h : IsCyc c E) (hFE : F ⊆ E) :
    IsCyc c F := fun e he => h e (hFE he)

lemma IsCyc.union {c : W → ZMod 3} {E F : Finset (W × W)} (hE : IsCyc c E) (hF : IsCyc c F) :
    IsCyc c (E ∪ F) := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · exact hE e h
  · exact hF e h

lemma balanced_empty : Balanced (∅ : Finset (W × W)) := by
  intro v; simp [inDeg, outDeg]

end Basic

/-- The arc embedding `V × V ↪ (V ⊕ U) × (V ⊕ U)` along `Sum.inl`. -/
def liftArc (V U : Type*) : V × V ↪ (V ⊕ U) × (V ⊕ U) :=
  ⟨fun e => (Sum.inl e.1, Sum.inl e.2), by
    intro a b h
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    exact Prod.ext h.1 h.2⟩

/-- **The reduced target A with explicit constants** (`ARISTOTLE_CRUX_…`, section A).

For every finite cyclically tripartite digraph `Y` on `V` of maximum degree `≤ 17` there are a
finite set `U` of new vertices with colours `cU`, and a cyclically tripartite reserve `R` on
`V ⊕ U`, fixed before the demand, such that

1. `R` is arc-disjoint from `Y`;
2. `|R| ≤ C0 |Y|` and `Δ(R) ≤ C0`;
3. for **every** balanced `L ⊆ Y` (including `L = ∅`), `R ∪ L` partitions into directed simple
   cycles of length `≤ K`.

Reserve first, demand second. -/
def CycleShortenerWith (C0 K : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V)),
    IsCyc c Y → MaxDegLE Y 17 →
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset ((V ⊕ U) × (V ⊕ U))),
      IsCyc (Sum.elim c cU) R ∧ Disjoint R (Y.map (liftArc V U)) ∧
      R.card ≤ C0 * Y.card ∧ MaxDegLE R C0 ∧
      ∀ L ⊆ Y, Balanced L →
        ∃ P : Finset (Finset ((V ⊕ U) × (V ⊕ U))),
          IsCyclePartition K P (R ∪ L.map (liftArc V U))

/-- **The reduced target A** (open): absolute constants `C0 ≥ 1`, `K ≥ 3` exist. -/
def CycleShortener : Prop := ∃ C0 K : ℕ, 1 ≤ C0 ∧ 3 ≤ K ∧ CycleShortenerWith C0 K

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
