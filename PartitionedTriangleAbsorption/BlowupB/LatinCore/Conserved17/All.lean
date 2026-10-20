/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Batch0
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Batch1
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Batch2
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Batch3
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Transport
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-! The seventeen explicit structural reductions, not seventeen absorber
existence theorems. Closing the Latin producer remains a separate obligation. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cases : Fin 17 → Case := ![case00, case01, case02, case03, case04, case05, case06, case07, case08, case09, case10, case11, case12, case13, case14, case15, case16]

theorem all_checked : ∀ i : Fin 17, Checked (cases i) := by
  intro i
  fin_cases i
  · exact checked_case00
  · exact checked_case01
  · exact checked_case02
  · exact checked_case03
  · exact checked_case04
  · exact checked_case05
  · exact checked_case06
  · exact checked_case07
  · exact checked_case08
  · exact checked_case09
  · exact checked_case10
  · exact checked_case11
  · exact checked_case12
  · exact checked_case13
  · exact checked_case14
  · exact checked_case15
  · exact checked_case16

theorem families_injective : Function.Injective (fun i : Fin 17 => (cases i).F) := by
  decide +kernel

theorem families_inequivalent : ∀ (i j : Fin 17) (σ : Equiv.Perm (Fin 4)),
    (cases i).F.image (Multiset.map σ) = (cases j).F → i = j := by
  decide +kernel

theorem every_core_is_tripartite {V : Type*} [DecidableEq V]
    (i : Fin 17) (p : V → Fin (cases i).t)
    (hcore : ∀ v, (cases i).comp (p v) = (cases i).core)
    (E : Finset (Sym2 V)) :
    PartitionedTriangleAbsorption.HasDecomp p (cases i).S.F' E ↔
      PartitionedTriangleAbsorption.HasDecomp ((cases i).colour ∘ p) tripFamily E :=
  hasDecomp_iff (cases i) (all_checked i) p hcore E

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.all_checked
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.families_injective
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.families_inequivalent
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.every_core_is_tripartite

