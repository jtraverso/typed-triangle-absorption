/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Basic

@[expose] public section

/-! Finite structural data for the seventeen conserved families.
These checks do not assert an absorber or a decomposition theorem. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open VertexSplit

structure Case where
  F : Finset (Multiset (Fin 4))
  t : ℕ
  S : SplitData F t
  comp : Fin t → Fin t
  core : Fin t
  colour : Fin t → Fin 3

def componentFamily (d : Case) (k : Fin d.t) : Finset (Multiset (Fin d.t)) :=
  d.S.F'.filter fun τ => ∀ r ∈ τ, d.comp r = k

structure Checked (d : Case) : Prop where
  size : 0 < d.t ∧ d.t ≤ 8
  card_three : ∀ τ ∈ d.F, τ.card = 3
  compat : d.S.Compat
  pair : ∀ i j, (∃ k, Link d.S.F' i j k) →
    d.S.cls (d.S.π i) (d.S.π j) = i ∧ d.S.cls (d.S.π j) (d.S.π i) = j
  surj : ∀ j, ∃ s, d.S.cls (d.S.π j) s = j
  component : ∀ i j, (∃ k, Link d.S.F' i j k) → d.comp i = d.comp j
  inside : ∀ τ ∈ d.S.F', ∀ i j, 0 < τ.count i → 0 < τ.count j → d.comp i = d.comp j
  core_exact : ∀ a b c, d.comp a = d.core → d.comp b = d.core → d.comp c = d.core →
    (Link d.S.F' a b c ↔ ({d.colour a, d.colour b, d.colour c} : Multiset (Fin 3)) = {0, 1, 2})
  colours_present : ∀ j : Fin 3, ∃ r, d.comp r = d.core ∧ d.colour r = j
  other_star : ∀ k, k ≠ d.core → ∃ a, ∀ τ ∈ componentFamily d k,
    ∃ b, τ = ({a, a, b} : Multiset (Fin d.t))
  other_size : ∀ k, k ≠ d.core → (componentFamily d k).card ≤ 3

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

