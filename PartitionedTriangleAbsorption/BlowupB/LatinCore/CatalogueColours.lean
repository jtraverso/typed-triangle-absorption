/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueEmbedding
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs

@[expose] public section

/-! Translate the catalogue's ZMod3 colours to the Fin3 palette used by the
physical path constructor, and retain the cyclic orientation on every path. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueColours

open Cycles

def colour : Fin 3 → ZMod 3 := ZMod.finEquiv 3

def toFin : ZMod 3 → Fin 3 := (ZMod.finEquiv 3).symm

theorem colour_toFin (c : ZMod 3) : colour (toFin c) = c :=
  (ZMod.finEquiv 3).apply_symm_apply c

theorem step_ne : ∀ i j : Fin 3, colour j = colour i + 1 → i ≠ j := by decide

theorem third_step : ∀ i j : Fin 3, colour j = colour i + 1 →
    colour (CatalogueEmbedding.third i j) = colour j + 1 ∧
      colour i = colour (CatalogueEmbedding.third i j) + 1 := by decide

theorem fin_ne_of_step {a b : ZMod 3} (h : b = a + 1) : toFin a ≠ toFin b := by
  apply step_ne
  simpa only [colour_toFin] using h

theorem path_cyclic {V : Type} [DecidableEq V] (p : V → Fin 3)
    (u x y z v : V) (i j : Fin 3)
    (hu : p u = i) (hv : p v = j) (hx : p x = j)
    (hy : p y = CatalogueEmbedding.third i j) (hz : p z = i)
    (hstep : colour j = colour i + 1) :
    IsCyc (colour ∘ p) (PhysicalPathArcs.arcs u x y z v) := by
  have hthird := third_step i j hstep
  apply PhysicalPathArcs.cyclic
  · simpa only [Function.comp_apply, hx, hu] using hstep
  · simpa only [Function.comp_apply, hy, hx] using hthird.1
  · simpa only [Function.comp_apply, hz, hy] using hthird.2
  · simpa only [Function.comp_apply, hv, hz] using hstep

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueColours

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueColours.fin_ne_of_step
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueColours.path_cyclic
