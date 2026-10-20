/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Defs

@[expose] public section

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open VertexSplit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def case15 : Case where
  F := {{0, 0, 0}, {0, 0, 1}, {1, 2, 3}, {2, 2, 2}, {3, 3, 3}}
  t := 7
  S := {
    κ := ![![0, 0, 0, 0], ![1, 1, 2, 2], ![4, 4, 3, 4], ![5, 5, 5, 6]]
    π := ![0, 1, 1, 2, 2, 3, 3]
    π_κ := by decide +kernel
    dflt := ![0, 0, 1, 1]
    dflt_allowed := by unfold Link; decide +kernel
    obs := by unfold Link; decide +kernel
    F' := {{0, 0, 0}, {0, 0, 1}, {2, 4, 5}, {3, 3, 3}, {6, 6, 6}}
    sig := fun τ => if τ = {0, 0, 0} then ({0, 0, 0} : Multiset (Fin 7)) else if τ = {0, 0, 1} then ({0, 0, 1} : Multiset (Fin 7)) else if τ = {1, 2, 3} then ({2, 4, 5} : Multiset (Fin 7)) else if τ = {2, 2, 2} then ({3, 3, 3} : Multiset (Fin 7)) else if τ = {3, 3, 3} then ({6, 6, 6} : Multiset (Fin 7)) else 0
    sig_tri := by unfold Link; decide +kernel
    sig_mem := by decide +kernel
    π_mem := by decide +kernel }
  comp := ![0, 0, 2, 3, 2, 2, 6]
  core := 2
  colour := ![0, 0, 2, 0, 1, 0, 0]

theorem checked_case15 : Checked case15 where
  size := by decide +kernel
  card_three := by decide +kernel
  compat := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  pair := by unfold Link; decide +kernel
  surj := by decide +kernel
  component := by unfold Link; decide +kernel
  inside := by decide +kernel
  core_exact := by unfold Link; decide +kernel
  colours_present := by decide +kernel
  other_star := by unfold componentFamily; decide +kernel
  other_size := by unfold componentFamily; decide +kernel

def case16 : Case where
  F := {{0, 0, 0}, {0, 1, 2}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}
  t := 7
  S := {
    κ := ![![0, 1, 1, 0], ![3, 2, 3, 3], ![4, 4, 5, 4], ![6, 6, 6, 6]]
    π := ![0, 0, 1, 1, 2, 2, 3]
    π_κ := by decide +kernel
    dflt := ![0, 0, 0, 3]
    dflt_allowed := by unfold Link; decide +kernel
    obs := by unfold Link; decide +kernel
    F' := {{0, 0, 0}, {1, 3, 4}, {2, 2, 2}, {5, 5, 5}, {6, 6, 6}}
    sig := fun τ => if τ = {0, 0, 0} then ({0, 0, 0} : Multiset (Fin 7)) else if τ = {0, 1, 2} then ({1, 3, 4} : Multiset (Fin 7)) else if τ = {1, 1, 1} then ({2, 2, 2} : Multiset (Fin 7)) else if τ = {2, 2, 2} then ({5, 5, 5} : Multiset (Fin 7)) else if τ = {3, 3, 3} then ({6, 6, 6} : Multiset (Fin 7)) else 0
    sig_tri := by unfold Link; decide +kernel
    sig_mem := by decide +kernel
    π_mem := by decide +kernel }
  comp := ![0, 1, 2, 1, 1, 5, 6]
  core := 1
  colour := ![0, 2, 0, 1, 0, 0, 0]

theorem checked_case16 : Checked case16 where
  size := by decide +kernel
  card_three := by decide +kernel
  compat := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  pair := by unfold Link; decide +kernel
  surj := by decide +kernel
  component := by unfold Link; decide +kernel
  inside := by decide +kernel
  core_exact := by unfold Link; decide +kernel
  colours_present := by decide +kernel
  other_star := by unfold componentFamily; decide +kernel
  other_size := by unfold componentFamily; decide +kernel

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.checked_case15
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.checked_case16

