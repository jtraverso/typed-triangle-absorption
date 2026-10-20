/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Cert

/-! # The physical gadget of a certificate

Vertex type `Ext W k = W ⊕ (occurrence clones) ⊕ (hinge clones)`:
* `occV (i, m)` is the clone of the corner `m` of occurrence `i` (same label);
* `hngV s false`, `hngV s true` are the two hinge clones of the side `s`, with the labels of
  `U s` and `V s` respectively (they are only used for negative sides).

Edges are named by slots:
* `wv s x`  : the edge `x – occV s` (`x ∈ W`); the wedge of side `s` is `wv s (U s), wv s (V s)`;
* `y i m`   : the edge `occV (i, m+1) – occV (i, m+2)` of the clone triangle `Y` of occurrence `i`;
* `h s κ`   : the seven hinge edges `ub, av, ab, az⁻, bz⁻, az⁺, bz⁺` of the side `s`
               (`z⁻ = occV s`, `z⁺ = occV (mu s)`);
* `pe e`    : an original edge `e` of `W` (only used for `P`).
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption

/-- The extended vertex type. -/
abbrev Ext (W : Type*) (k : ℕ) := W ⊕ (Fin k × Fin 3) ⊕ ((Fin k × Fin 3) × Bool)

/-- Occurrence clone. -/
def occV {W : Type*} {k : ℕ} (s : Fin k × Fin 3) : Ext W k := Sum.inr (Sum.inl s)
/-- Hinge clone. -/
def hngV {W : Type*} {k : ℕ} (s : Fin k × Fin 3) (b : Bool) : Ext W k := Sum.inr (Sum.inr (s, b))

/-- The seven hinge edges. -/
inductive HK
  | ub | av | ab | az | bz | az' | bz'
  deriving DecidableEq

/-- Edge names. -/
inductive Slot (W : Type*) (k : ℕ)
  | wv : Fin k × Fin 3 → W → Slot W k
  | y : Fin k → Fin 3 → Slot W k
  | h : Fin k × Fin 3 → HK → Slot W k
  | pe : Sym2 W → Slot W k
  deriving DecidableEq

/-- Triangle names. -/
inductive TriIx (k : ℕ)
  | r : Fin k → Fin 3 → TriIx k
  | yy : Fin k → TriIx k
  | hz0 : Fin k × Fin 3 → TriIx k
  | hz1 : Fin k × Fin 3 → TriIx k
  | hz2 : Fin k × Fin 3 → TriIx k
  | hp0 : Fin k × Fin 3 → TriIx k
  | hp1 : Fin k × Fin 3 → TriIx k
  | hp2 : Fin k × Fin 3 → TriIx k
  | cl : Fin k × Fin 3 → TriIx k
  deriving DecidableEq, Fintype

variable {W : Type*} [DecidableEq W] {t : ℕ}
variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable {c : SignedCert p F P}

namespace SignedCert

variable (c)

/-- Labels on the extended vertex type. -/
def extLabel : Ext W c.k → Fin t
  | Sum.inl x => p x
  | Sum.inr (Sum.inl s) => p (c.vtx s.1 s.2)
  | Sum.inr (Sum.inr (s, false)) => p (c.U s)
  | Sum.inr (Sum.inr (s, true)) => p (c.V s)

/-- Negative sides. -/
def negS : Finset (Fin c.k × Fin 3) := univ.filter fun s => c.pos s.1 = false

/-- Slots of the nine-edge block `R` of occurrence `i`. -/
def occSlots (i : Fin c.k) : Finset (Slot W c.k) :=
  univ.biUnion fun m : Fin 3 =>
    {.wv (i, m) (c.U (i, m)), .wv (i, m) (c.V (i, m)), .y i m}

/-- Slots of the seven-edge hinge of side `s`. -/
def hSlots (s : Fin c.k × Fin 3) : Finset (Slot W c.k) :=
  {.h s .ub, .h s .av, .h s .ab, .h s .az, .h s .bz, .h s .az', .h s .bz'}

/-- Slots of the absorber: all blocks `R` and all hinges of negative sides. -/
def aSlots : Finset (Slot W c.k) :=
  univ.biUnion c.occSlots ∪ c.negS.biUnion c.hSlots

/-- Triangles of the decomposition of `A` ("empty mode"): `R` of positive occurrences,
`Y` of negative occurrences, and the hinges with the negative wedges. -/
def inMode0 : TriIx c.k → Prop
  | .r i _ => c.pos i = true
  | .yy i => c.pos i = false
  | .hz0 s => c.pos s.1 = false
  | .hz1 s => c.pos s.1 = false
  | .hz2 s => c.pos s.1 = false
  | _ => False

instance : DecidablePred c.inMode0 := fun j => by cases j <;> unfold inMode0 <;> infer_instance

end SignedCert

namespace Matching

variable (M : Matching c)

/-- The seven hinge edges of side `s`. -/
def hEdge (s : Fin c.k × Fin 3) : HK → Sym2 (Ext W c.k)
  | .ub => s(Sum.inl (c.U s), hngV s true)
  | .av => s(hngV s false, Sum.inl (c.V s))
  | .ab => s(hngV s false, hngV s true)
  | .az => s(hngV s false, occV s)
  | .bz => s(hngV s true, occV s)
  | .az' => s(hngV s false, occV (M.mu s))
  | .bz' => s(hngV s true, occV (M.mu s))

/-- The physical edge named by a slot. -/
def ed : Slot W c.k → Sym2 (Ext W c.k)
  | .wv s x => s(Sum.inl x, occV s)
  | .y i m => s(occV (i, m + 1), occV (i, m + 2))
  | .h s κ => M.hEdge s κ
  | .pe e => e.map Sum.inl

/-- **The absorber** `A`: union of all `R` blocks and of all hinges. -/
def absorber : Finset (Sym2 (Ext W c.k)) := c.aSlots.image M.ed

/-- The triangles. -/
def tri : TriIx c.k → Finset (Ext W c.k)
  | .r i m => {Sum.inl (c.vtx i m), occV (i, m + 1), occV (i, m + 2)}
  | .yy i => {occV (i, 0), occV (i, 1), occV (i, 2)}
  | .hz0 s => {Sum.inl (c.U s), hngV s true, occV s}
  | .hz1 s => {hngV s false, Sum.inl (c.V s), occV s}
  | .hz2 s => {hngV s false, hngV s true, occV (M.mu s)}
  | .hp0 s => {Sum.inl (c.U s), hngV s true, occV (M.mu s)}
  | .hp1 s => {hngV s false, Sum.inl (c.V s), occV (M.mu s)}
  | .hp2 s => {hngV s false, hngV s true, occV s}
  | .cl s => {Sum.inl (c.U s), Sum.inl (c.V s), occV s}

/-- The three slots consumed by each triangle. -/
def sl : TriIx c.k → Finset (Slot W c.k)
  | .r i m => {.wv (i, m + 1) (c.V (i, m + 1)), .wv (i, m + 2) (c.U (i, m + 2)), .y i m}
  | .yy i => {.y i 0, .y i 1, .y i 2}
  | .hz0 s => {.h s .ub, .h s .bz, .wv s (c.U s)}
  | .hz1 s => {.h s .av, .h s .az, .wv s (c.V s)}
  | .hz2 s => {.h s .ab, .h s .az', .h s .bz'}
  | .hp0 s => {.h s .ub, .h s .bz', .wv (M.mu s) (c.U s)}
  | .hp1 s => {.h s .av, .h s .az', .wv (M.mu s) (c.V s)}
  | .hp2 s => {.h s .ab, .h s .az, .h s .bz}
  | .cl s => {.wv s (c.U s), .wv s (c.V s), .pe (c.side s)}

/-- Triangles of the decomposition of `A ∪ P` ("mode P"): `R` of negative occurrences,
`Y` of positive ones, hinges with the positive wedges, and the unmatched positive wedges
closed by their edge of `P`. -/
def inModeP : TriIx c.k → Prop
  | .r i _ => c.pos i = false
  | .yy i => c.pos i = true
  | .hp0 s => c.pos s.1 = false
  | .hp1 s => c.pos s.1 = false
  | .hp2 s => c.pos s.1 = false
  | .cl s => M.Unmatched s
  | _ => False

instance : DecidablePred M.inModeP := fun j => by cases j <;> unfold inModeP <;> infer_instance

end Matching

end PaperII.CertAbsorber
