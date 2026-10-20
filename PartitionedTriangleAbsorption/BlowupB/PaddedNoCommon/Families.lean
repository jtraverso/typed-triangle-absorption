/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.LatticeFrame

@[expose] public section

/-!
# The fourteen connected trivial-lattice families without common neighbour classes

`CENSUS_THREESTEP_NOCOMMON_20261013.md` (Python census) lists 14 `S₄`-classes with
`ThreeStepLinks`, a connected allowed-pair graph, a trivial lattice and no common neighbour classes.
They are `NC1`, …, `NC14` below, in the order of the census table. Each contains one of six
minimal base families `FnA`, …, `FnF` with the SAME allowed pairs:

| base | types | allowed pairs | census rows |
|---|---|---|---|
| `FnA` | 000 001 002 011 111 113 | 00 01 02 11 13 | NC1 |
| `FnB` | 000 001 002 011 113 133 | 00 01 02 11 13 33 | NC2, NC5 |
| `FnC` | 000 001 002 011 022 111 113 | 00 01 02 11 13 22 | NC3, NC9 |
| `FnD` | 000 001 002 011 022 113 133 | 00 01 02 11 13 22 33 | NC4, NC7, NC8, NC12, NC14 |
| `FnE` | 000 001 011 112 122 223 233 | 00 01 11 12 22 23 33 | NC6, NC11 |
| `FnF` | 000 001 002 011 022 111 223 233 | 00 01 02 11 22 23 33 | NC10, NC13 |

All finite facts here (card three, `ThreeStepLinks`, `Walk4`, a forbidden partner for every class,
inclusion and equality of allowed pairs) are checked by `decide`. The facts that the lattice is
trivial and that there are no common neighbour classes are NOT used as census input: the lattice is
proved in `PaddedNoCommon/Lattice.lean`, and the absence of common neighbours is only recorded
(`not_common_*`).
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PaddedGeneral

/-- Base family `FnA`. -/
noncomputable def FnA : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 1}, {1, 1, 3}}

/-- Base family `FnB`. -/
noncomputable def FnB : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}, {1, 3, 3}}

/-- Base family `FnC`. -/
noncomputable def FnC : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}}

/-- Base family `FnD`. -/
noncomputable def FnD : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}}

/-- Base family `FnE`. -/
noncomputable def FnE : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 3}, {2, 3, 3}}

/-- Base family `FnF`. -/
noncomputable def FnF : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 3}, {2, 3, 3}}

/-- Census family `NC1` (base `FnA`). -/
noncomputable def NC1 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 1}, {1, 1, 3}}

/-- Census family `NC2` (base `FnB`). -/
noncomputable def NC2 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}, {1, 3, 3}}

/-- Census family `NC3` (base `FnC`). -/
noncomputable def NC3 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}}

/-- Census family `NC4` (base `FnD`). -/
noncomputable def NC4 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}}

/-- Census family `NC5` (base `FnB`). -/
noncomputable def NC5 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}, {1, 3, 3}, {3, 3, 3}}

/-- Census family `NC6` (base `FnE`). -/
noncomputable def NC6 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 3}, {2, 3, 3}}

/-- Census family `NC7` (base `FnD`). -/
noncomputable def NC7 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}, {1, 3, 3}}

/-- Census family `NC8` (base `FnD`). -/
noncomputable def NC8 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}, {3, 3, 3}}

/-- Census family `NC9` (base `FnC`). -/
noncomputable def NC9 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}, {2, 2, 2}}

/-- Census family `NC10` (base `FnF`). -/
noncomputable def NC10 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 3}, {2, 3, 3}}

/-- Census family `NC11` (base `FnE`). -/
noncomputable def NC11 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 3}, {2, 3, 3}, {3, 3, 3}}

/-- Census family `NC12` (base `FnD`). -/
noncomputable def NC12 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}, {1, 3, 3}, {2, 2, 2}}

/-- Census family `NC13` (base `FnF`). -/
noncomputable def NC13 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 3}, {2, 3, 3}, {3, 3, 3}}

/-- Census family `NC14` (base `FnD`). -/
noncomputable def NC14 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}, {1, 3, 3}, {2, 2, 2}, {3, 3, 3}}

/-- The finite facts of a base family used by the universal certificate. -/
structure BaseFacts (F : Finset (Multiset (Fin 4))) : Prop where
  card : ∀ τ ∈ F, Multiset.card τ = 3
  three : ThreeStepLinks F
  walk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k)
  facts : FamilyFacts F

/-- A census family over a base: same allowed pairs, more types. -/
structure OverBase (F0 F : Finset (Multiset (Fin 4))) : Prop where
  sub : F0 ⊆ F
  allowed : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link F0 i j k)
  facts : FamilyFacts F

theorem baseFacts_FnA : BaseFacts FnA where
  card := by unfold FnA; decide
  three := by unfold ThreeStepLinks Link FnA; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnA; decide
  facts := ⟨by unfold FnA; decide, by unfold Link FnA; decide,
    by intro i; fin_cases i <;> (unfold Link FnA; decide)⟩

/-- `FnA` has no common neighbour class for some pair of classes. -/
theorem not_common_FnA : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnA a c k) ∧ (∃ k, Link FnA b c k) := by
  unfold Link FnA; decide

theorem baseFacts_FnB : BaseFacts FnB where
  card := by unfold FnB; decide
  three := by unfold ThreeStepLinks Link FnB; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnB; decide
  facts := ⟨by unfold FnB; decide, by unfold Link FnB; decide,
    by intro i; fin_cases i <;> (unfold Link FnB; decide)⟩

/-- `FnB` has no common neighbour class for some pair of classes. -/
theorem not_common_FnB : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnB a c k) ∧ (∃ k, Link FnB b c k) := by
  unfold Link FnB; decide

theorem baseFacts_FnC : BaseFacts FnC where
  card := by unfold FnC; decide
  three := by unfold ThreeStepLinks Link FnC; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnC; decide
  facts := ⟨by unfold FnC; decide, by unfold Link FnC; decide,
    by intro i; fin_cases i <;> (unfold Link FnC; decide)⟩

/-- `FnC` has no common neighbour class for some pair of classes. -/
theorem not_common_FnC : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnC a c k) ∧ (∃ k, Link FnC b c k) := by
  unfold Link FnC; decide

theorem baseFacts_FnD : BaseFacts FnD where
  card := by unfold FnD; decide
  three := by unfold ThreeStepLinks Link FnD; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnD; decide
  facts := ⟨by unfold FnD; decide, by unfold Link FnD; decide,
    by intro i; fin_cases i <;> (unfold Link FnD; decide)⟩

/-- `FnD` has no common neighbour class for some pair of classes. -/
theorem not_common_FnD : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnD a c k) ∧ (∃ k, Link FnD b c k) := by
  unfold Link FnD; decide

theorem baseFacts_FnE : BaseFacts FnE where
  card := by unfold FnE; decide
  three := by unfold ThreeStepLinks Link FnE; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnE; decide
  facts := ⟨by unfold FnE; decide, by unfold Link FnE; decide,
    by intro i; fin_cases i <;> (unfold Link FnE; decide)⟩

/-- `FnE` has no common neighbour class for some pair of classes. -/
theorem not_common_FnE : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnE a c k) ∧ (∃ k, Link FnE b c k) := by
  unfold Link FnE; decide

theorem baseFacts_FnF : BaseFacts FnF where
  card := by unfold FnF; decide
  three := by unfold ThreeStepLinks Link FnF; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnF; decide
  facts := ⟨by unfold FnF; decide, by unfold Link FnF; decide,
    by intro i; fin_cases i <;> (unfold Link FnF; decide)⟩

/-- `FnF` has no common neighbour class for some pair of classes. -/
theorem not_common_FnF : ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnF a c k) ∧ (∃ k, Link FnF b c k) := by
  unfold Link FnF; decide

theorem overBase_NC1 : OverBase FnA NC1 where
  sub := by unfold FnA NC1; decide
  allowed := by unfold Link FnA NC1; decide
  facts := ⟨by unfold NC1; decide, by unfold Link NC1; decide,
    by intro i; fin_cases i <;> (unfold Link NC1; decide)⟩

theorem overBase_NC2 : OverBase FnB NC2 where
  sub := by unfold FnB NC2; decide
  allowed := by unfold Link FnB NC2; decide
  facts := ⟨by unfold NC2; decide, by unfold Link NC2; decide,
    by intro i; fin_cases i <;> (unfold Link NC2; decide)⟩

theorem overBase_NC3 : OverBase FnC NC3 where
  sub := by unfold FnC NC3; decide
  allowed := by unfold Link FnC NC3; decide
  facts := ⟨by unfold NC3; decide, by unfold Link NC3; decide,
    by intro i; fin_cases i <;> (unfold Link NC3; decide)⟩

theorem overBase_NC4 : OverBase FnD NC4 where
  sub := by unfold FnD NC4; decide
  allowed := by unfold Link FnD NC4; decide
  facts := ⟨by unfold NC4; decide, by unfold Link NC4; decide,
    by intro i; fin_cases i <;> (unfold Link NC4; decide)⟩

theorem overBase_NC5 : OverBase FnB NC5 where
  sub := by unfold FnB NC5; decide
  allowed := by unfold Link FnB NC5; decide
  facts := ⟨by unfold NC5; decide, by unfold Link NC5; decide,
    by intro i; fin_cases i <;> (unfold Link NC5; decide)⟩

theorem overBase_NC6 : OverBase FnE NC6 where
  sub := by unfold FnE NC6; decide
  allowed := by unfold Link FnE NC6; decide
  facts := ⟨by unfold NC6; decide, by unfold Link NC6; decide,
    by intro i; fin_cases i <;> (unfold Link NC6; decide)⟩

theorem overBase_NC7 : OverBase FnD NC7 where
  sub := by unfold FnD NC7; decide
  allowed := by unfold Link FnD NC7; decide
  facts := ⟨by unfold NC7; decide, by unfold Link NC7; decide,
    by intro i; fin_cases i <;> (unfold Link NC7; decide)⟩

theorem overBase_NC8 : OverBase FnD NC8 where
  sub := by unfold FnD NC8; decide
  allowed := by unfold Link FnD NC8; decide
  facts := ⟨by unfold NC8; decide, by unfold Link NC8; decide,
    by intro i; fin_cases i <;> (unfold Link NC8; decide)⟩

theorem overBase_NC9 : OverBase FnC NC9 where
  sub := by unfold FnC NC9; decide
  allowed := by unfold Link FnC NC9; decide
  facts := ⟨by unfold NC9; decide, by unfold Link NC9; decide,
    by intro i; fin_cases i <;> (unfold Link NC9; decide)⟩

theorem overBase_NC10 : OverBase FnF NC10 where
  sub := by unfold FnF NC10; decide
  allowed := by unfold Link FnF NC10; decide
  facts := ⟨by unfold NC10; decide, by unfold Link NC10; decide,
    by intro i; fin_cases i <;> (unfold Link NC10; decide)⟩

theorem overBase_NC11 : OverBase FnE NC11 where
  sub := by unfold FnE NC11; decide
  allowed := by unfold Link FnE NC11; decide
  facts := ⟨by unfold NC11; decide, by unfold Link NC11; decide,
    by intro i; fin_cases i <;> (unfold Link NC11; decide)⟩

theorem overBase_NC12 : OverBase FnD NC12 where
  sub := by unfold FnD NC12; decide
  allowed := by unfold Link FnD NC12; decide
  facts := ⟨by unfold NC12; decide, by unfold Link NC12; decide,
    by intro i; fin_cases i <;> (unfold Link NC12; decide)⟩

theorem overBase_NC13 : OverBase FnF NC13 where
  sub := by unfold FnF NC13; decide
  allowed := by unfold Link FnF NC13; decide
  facts := ⟨by unfold NC13; decide, by unfold Link NC13; decide,
    by intro i; fin_cases i <;> (unfold Link NC13; decide)⟩

theorem overBase_NC14 : OverBase FnD NC14 where
  sub := by unfold FnD NC14; decide
  allowed := by unfold Link FnD NC14; decide
  facts := ⟨by unfold NC14; decide, by unfold Link NC14; decide,
    by intro i; fin_cases i <;> (unfold Link NC14; decide)⟩

end PaddedNoCommon
