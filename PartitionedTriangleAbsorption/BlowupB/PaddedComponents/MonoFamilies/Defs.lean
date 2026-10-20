/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.WitnessFrame
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoObstruction

@[expose] public section

/-!
# The 39 disconnected `ℤ/3` families with an isolated monochromatic class

Census rows `Y | N | 2 | N | Z/3` with a class `m` whose only type is `{m,m,m}` (`m = 3` with
component labels `cM3 = (0,0,0,3)`, or `m = 0` with `cM0 = (0,1,1,1)`). Definitions and finite facts
(all by `decide`). `FMxx` is the `xx`-th such row of `CENSUS_ALL_765_20261013.md`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- Component labels when class `3` is the isolated class. -/
def cM3 : Fin 4 → Fin 4 := ![0, 0, 0, 3]

/-- Component labels when class `0` is the isolated class. -/
def cM0 : Fin 4 → Fin 4 := ![0, 1, 1, 1]

/-- `{000 001 002 333}`. -/
noncomputable def FM01 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {3, 3, 3}}

theorem FM01_card : ∀ τ ∈ FM01, Multiset.card τ = 3 := by unfold FM01; decide

theorem FM01_card_eq : FM01.card = 4 := by unfold FM01; decide

theorem FM01_three : ThreeStepLinks FM01 := by unfold ThreeStepLinks Link FM01; decide

theorem familyFacts_FM01 : FamilyFacts FM01 :=
  ⟨FM01_card, by unfold Link FM01; decide,
    by intro i; fin_cases i <;> (unfold Link FM01; decide)⟩

theorem compLabel_FM01 : CompLabel FM01 cM3 := by
  unfold CompLabel Link FM01 cM3; decide

theorem typesInside_FM01 : TypesInside FM01 cM3 := by
  unfold TypesInside FM01 cM3; decide

theorem localWalk4_FM01 (k : Fin 4) : LocalWalk4 FM01 cM3 k := by
  revert k; unfold LocalWalk4 Link FM01 cM3; decide

theorem isolatedMono_FM01 : IsolatedMono FM01 3 := by unfold IsolatedMono FM01; decide

/-- `{000 001 002 011 333}`. -/
noncomputable def FM02 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {3, 3, 3}}

theorem FM02_card : ∀ τ ∈ FM02, Multiset.card τ = 3 := by unfold FM02; decide

theorem FM02_card_eq : FM02.card = 5 := by unfold FM02; decide

theorem FM02_three : ThreeStepLinks FM02 := by unfold ThreeStepLinks Link FM02; decide

theorem familyFacts_FM02 : FamilyFacts FM02 :=
  ⟨FM02_card, by unfold Link FM02; decide,
    by intro i; fin_cases i <;> (unfold Link FM02; decide)⟩

theorem compLabel_FM02 : CompLabel FM02 cM3 := by
  unfold CompLabel Link FM02 cM3; decide

theorem typesInside_FM02 : TypesInside FM02 cM3 := by
  unfold TypesInside FM02 cM3; decide

theorem localWalk4_FM02 (k : Fin 4) : LocalWalk4 FM02 cM3 k := by
  revert k; unfold LocalWalk4 Link FM02 cM3; decide

theorem isolatedMono_FM02 : IsolatedMono FM02 3 := by unfold IsolatedMono FM02; decide

/-- `{000 001 002 012 333}`. -/
noncomputable def FM03 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {3, 3, 3}}

theorem FM03_card : ∀ τ ∈ FM03, Multiset.card τ = 3 := by unfold FM03; decide

theorem FM03_card_eq : FM03.card = 5 := by unfold FM03; decide

theorem FM03_three : ThreeStepLinks FM03 := by unfold ThreeStepLinks Link FM03; decide

theorem familyFacts_FM03 : FamilyFacts FM03 :=
  ⟨FM03_card, by unfold Link FM03; decide,
    by intro i; fin_cases i <;> (unfold Link FM03; decide)⟩

theorem compLabel_FM03 : CompLabel FM03 cM3 := by
  unfold CompLabel Link FM03 cM3; decide

theorem typesInside_FM03 : TypesInside FM03 cM3 := by
  unfold TypesInside FM03 cM3; decide

theorem localWalk4_FM03 (k : Fin 4) : LocalWalk4 FM03 cM3 k := by
  revert k; unfold LocalWalk4 Link FM03 cM3; decide

theorem isolatedMono_FM03 : IsolatedMono FM03 3 := by unfold IsolatedMono FM03; decide

/-- `{000 001 002 011 012 333}`. -/
noncomputable def FM04 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {3, 3, 3}}

theorem FM04_card : ∀ τ ∈ FM04, Multiset.card τ = 3 := by unfold FM04; decide

theorem FM04_card_eq : FM04.card = 6 := by unfold FM04; decide

theorem FM04_three : ThreeStepLinks FM04 := by unfold ThreeStepLinks Link FM04; decide

theorem familyFacts_FM04 : FamilyFacts FM04 :=
  ⟨FM04_card, by unfold Link FM04; decide,
    by intro i; fin_cases i <;> (unfold Link FM04; decide)⟩

theorem compLabel_FM04 : CompLabel FM04 cM3 := by
  unfold CompLabel Link FM04 cM3; decide

theorem typesInside_FM04 : TypesInside FM04 cM3 := by
  unfold TypesInside FM04 cM3; decide

theorem localWalk4_FM04 (k : Fin 4) : LocalWalk4 FM04 cM3 k := by
  revert k; unfold LocalWalk4 Link FM04 cM3; decide

theorem isolatedMono_FM04 : IsolatedMono FM04 3 := by unfold IsolatedMono FM04; decide

/-- `{000 001 002 011 022 333}`. -/
noncomputable def FM05 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {3, 3, 3}}

theorem FM05_card : ∀ τ ∈ FM05, Multiset.card τ = 3 := by unfold FM05; decide

theorem FM05_card_eq : FM05.card = 6 := by unfold FM05; decide

theorem FM05_three : ThreeStepLinks FM05 := by unfold ThreeStepLinks Link FM05; decide

theorem familyFacts_FM05 : FamilyFacts FM05 :=
  ⟨FM05_card, by unfold Link FM05; decide,
    by intro i; fin_cases i <;> (unfold Link FM05; decide)⟩

theorem compLabel_FM05 : CompLabel FM05 cM3 := by
  unfold CompLabel Link FM05 cM3; decide

theorem typesInside_FM05 : TypesInside FM05 cM3 := by
  unfold TypesInside FM05 cM3; decide

theorem localWalk4_FM05 (k : Fin 4) : LocalWalk4 FM05 cM3 k := by
  revert k; unfold LocalWalk4 Link FM05 cM3; decide

theorem isolatedMono_FM05 : IsolatedMono FM05 3 := by unfold IsolatedMono FM05; decide

/-- `{000 001 002 011 111 333}`. -/
noncomputable def FM06 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 1}, {3, 3, 3}}

theorem FM06_card : ∀ τ ∈ FM06, Multiset.card τ = 3 := by unfold FM06; decide

theorem FM06_card_eq : FM06.card = 6 := by unfold FM06; decide

theorem FM06_three : ThreeStepLinks FM06 := by unfold ThreeStepLinks Link FM06; decide

theorem familyFacts_FM06 : FamilyFacts FM06 :=
  ⟨FM06_card, by unfold Link FM06; decide,
    by intro i; fin_cases i <;> (unfold Link FM06; decide)⟩

theorem compLabel_FM06 : CompLabel FM06 cM3 := by
  unfold CompLabel Link FM06 cM3; decide

theorem typesInside_FM06 : TypesInside FM06 cM3 := by
  unfold TypesInside FM06 cM3; decide

theorem localWalk4_FM06 (k : Fin 4) : LocalWalk4 FM06 cM3 k := by
  revert k; unfold LocalWalk4 Link FM06 cM3; decide

theorem isolatedMono_FM06 : IsolatedMono FM06 3 := by unfold IsolatedMono FM06; decide

/-- `{000 001 011 012 112 333}`. -/
noncomputable def FM07 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {3, 3, 3}}

theorem FM07_card : ∀ τ ∈ FM07, Multiset.card τ = 3 := by unfold FM07; decide

theorem FM07_card_eq : FM07.card = 6 := by unfold FM07; decide

theorem FM07_three : ThreeStepLinks FM07 := by unfold ThreeStepLinks Link FM07; decide

theorem familyFacts_FM07 : FamilyFacts FM07 :=
  ⟨FM07_card, by unfold Link FM07; decide,
    by intro i; fin_cases i <;> (unfold Link FM07; decide)⟩

theorem compLabel_FM07 : CompLabel FM07 cM3 := by
  unfold CompLabel Link FM07 cM3; decide

theorem typesInside_FM07 : TypesInside FM07 cM3 := by
  unfold TypesInside FM07 cM3; decide

theorem localWalk4_FM07 (k : Fin 4) : LocalWalk4 FM07 cM3 k := by
  revert k; unfold LocalWalk4 Link FM07 cM3; decide

theorem isolatedMono_FM07 : IsolatedMono FM07 3 := by unfold IsolatedMono FM07; decide

/-- `{000 001 011 112 122 333}`. -/
noncomputable def FM08 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM08_card : ∀ τ ∈ FM08, Multiset.card τ = 3 := by unfold FM08; decide

theorem FM08_card_eq : FM08.card = 6 := by unfold FM08; decide

theorem FM08_three : ThreeStepLinks FM08 := by unfold ThreeStepLinks Link FM08; decide

theorem familyFacts_FM08 : FamilyFacts FM08 :=
  ⟨FM08_card, by unfold Link FM08; decide,
    by intro i; fin_cases i <;> (unfold Link FM08; decide)⟩

theorem compLabel_FM08 : CompLabel FM08 cM3 := by
  unfold CompLabel Link FM08 cM3; decide

theorem typesInside_FM08 : TypesInside FM08 cM3 := by
  unfold TypesInside FM08 cM3; decide

theorem localWalk4_FM08 (k : Fin 4) : LocalWalk4 FM08 cM3 k := by
  revert k; unfold LocalWalk4 Link FM08 cM3; decide

theorem isolatedMono_FM08 : IsolatedMono FM08 3 := by unfold IsolatedMono FM08; decide

/-- `{000 112 113 122 123 223}`. -/
noncomputable def FM09 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {1, 1, 2}, {1, 1, 3}, {1, 2, 2}, {1, 2, 3}, {2, 2, 3}}

theorem FM09_card : ∀ τ ∈ FM09, Multiset.card τ = 3 := by unfold FM09; decide

theorem FM09_card_eq : FM09.card = 6 := by unfold FM09; decide

theorem FM09_three : ThreeStepLinks FM09 := by unfold ThreeStepLinks Link FM09; decide

theorem familyFacts_FM09 : FamilyFacts FM09 :=
  ⟨FM09_card, by unfold Link FM09; decide,
    by intro i; fin_cases i <;> (unfold Link FM09; decide)⟩

theorem compLabel_FM09 : CompLabel FM09 cM0 := by
  unfold CompLabel Link FM09 cM0; decide

theorem typesInside_FM09 : TypesInside FM09 cM0 := by
  unfold TypesInside FM09 cM0; decide

theorem localWalk4_FM09 (k : Fin 4) : LocalWalk4 FM09 cM0 k := by
  revert k; unfold LocalWalk4 Link FM09 cM0; decide

theorem isolatedMono_FM09 : IsolatedMono FM09 0 := by unfold IsolatedMono FM09; decide

/-- `{000 001 002 011 012 022 333}`. -/
noncomputable def FM10 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {3, 3, 3}}

theorem FM10_card : ∀ τ ∈ FM10, Multiset.card τ = 3 := by unfold FM10; decide

theorem FM10_card_eq : FM10.card = 7 := by unfold FM10; decide

theorem FM10_three : ThreeStepLinks FM10 := by unfold ThreeStepLinks Link FM10; decide

theorem familyFacts_FM10 : FamilyFacts FM10 :=
  ⟨FM10_card, by unfold Link FM10; decide,
    by intro i; fin_cases i <;> (unfold Link FM10; decide)⟩

theorem compLabel_FM10 : CompLabel FM10 cM3 := by
  unfold CompLabel Link FM10 cM3; decide

theorem typesInside_FM10 : TypesInside FM10 cM3 := by
  unfold TypesInside FM10 cM3; decide

theorem localWalk4_FM10 (k : Fin 4) : LocalWalk4 FM10 cM3 k := by
  revert k; unfold LocalWalk4 Link FM10 cM3; decide

theorem isolatedMono_FM10 : IsolatedMono FM10 3 := by unfold IsolatedMono FM10; decide

/-- `{000 001 002 011 012 111 333}`. -/
noncomputable def FM11 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 1}, {3, 3, 3}}

theorem FM11_card : ∀ τ ∈ FM11, Multiset.card τ = 3 := by unfold FM11; decide

theorem FM11_card_eq : FM11.card = 7 := by unfold FM11; decide

theorem FM11_three : ThreeStepLinks FM11 := by unfold ThreeStepLinks Link FM11; decide

theorem familyFacts_FM11 : FamilyFacts FM11 :=
  ⟨FM11_card, by unfold Link FM11; decide,
    by intro i; fin_cases i <;> (unfold Link FM11; decide)⟩

theorem compLabel_FM11 : CompLabel FM11 cM3 := by
  unfold CompLabel Link FM11 cM3; decide

theorem typesInside_FM11 : TypesInside FM11 cM3 := by
  unfold TypesInside FM11 cM3; decide

theorem localWalk4_FM11 (k : Fin 4) : LocalWalk4 FM11 cM3 k := by
  revert k; unfold LocalWalk4 Link FM11 cM3; decide

theorem isolatedMono_FM11 : IsolatedMono FM11 3 := by unfold IsolatedMono FM11; decide

/-- `{000 001 002 011 022 111 333}`. -/
noncomputable def FM12 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {3, 3, 3}}

theorem FM12_card : ∀ τ ∈ FM12, Multiset.card τ = 3 := by unfold FM12; decide

theorem FM12_card_eq : FM12.card = 7 := by unfold FM12; decide

theorem FM12_three : ThreeStepLinks FM12 := by unfold ThreeStepLinks Link FM12; decide

theorem familyFacts_FM12 : FamilyFacts FM12 :=
  ⟨FM12_card, by unfold Link FM12; decide,
    by intro i; fin_cases i <;> (unfold Link FM12; decide)⟩

theorem compLabel_FM12 : CompLabel FM12 cM3 := by
  unfold CompLabel Link FM12 cM3; decide

theorem typesInside_FM12 : TypesInside FM12 cM3 := by
  unfold TypesInside FM12 cM3; decide

theorem localWalk4_FM12 (k : Fin 4) : LocalWalk4 FM12 cM3 k := by
  revert k; unfold LocalWalk4 Link FM12 cM3; decide

theorem isolatedMono_FM12 : IsolatedMono FM12 3 := by unfold IsolatedMono FM12; decide

/-- `{000 001 011 012 112 122 333}`. -/
noncomputable def FM13 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM13_card : ∀ τ ∈ FM13, Multiset.card τ = 3 := by unfold FM13; decide

theorem FM13_card_eq : FM13.card = 7 := by unfold FM13; decide

theorem FM13_three : ThreeStepLinks FM13 := by unfold ThreeStepLinks Link FM13; decide

theorem familyFacts_FM13 : FamilyFacts FM13 :=
  ⟨FM13_card, by unfold Link FM13; decide,
    by intro i; fin_cases i <;> (unfold Link FM13; decide)⟩

theorem compLabel_FM13 : CompLabel FM13 cM3 := by
  unfold CompLabel Link FM13 cM3; decide

theorem typesInside_FM13 : TypesInside FM13 cM3 := by
  unfold TypesInside FM13 cM3; decide

theorem localWalk4_FM13 (k : Fin 4) : LocalWalk4 FM13 cM3 k := by
  revert k; unfold LocalWalk4 Link FM13 cM3; decide

theorem isolatedMono_FM13 : IsolatedMono FM13 3 := by unfold IsolatedMono FM13; decide

/-- `{000 001 002 011 012 112 333}`. -/
noncomputable def FM14 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {3, 3, 3}}

theorem FM14_card : ∀ τ ∈ FM14, Multiset.card τ = 3 := by unfold FM14; decide

theorem FM14_card_eq : FM14.card = 7 := by unfold FM14; decide

theorem FM14_three : ThreeStepLinks FM14 := by unfold ThreeStepLinks Link FM14; decide

theorem familyFacts_FM14 : FamilyFacts FM14 :=
  ⟨FM14_card, by unfold Link FM14; decide,
    by intro i; fin_cases i <;> (unfold Link FM14; decide)⟩

theorem compLabel_FM14 : CompLabel FM14 cM3 := by
  unfold CompLabel Link FM14 cM3; decide

theorem typesInside_FM14 : TypesInside FM14 cM3 := by
  unfold TypesInside FM14 cM3; decide

theorem localWalk4_FM14 (k : Fin 4) : LocalWalk4 FM14 cM3 k := by
  revert k; unfold LocalWalk4 Link FM14 cM3; decide

theorem isolatedMono_FM14 : IsolatedMono FM14 3 := by unfold IsolatedMono FM14; decide

/-- `{000 112 113 122 123 133 223}`. -/
noncomputable def FM15 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {1, 1, 2}, {1, 1, 3}, {1, 2, 2}, {1, 2, 3}, {1, 3, 3}, {2, 2, 3}}

theorem FM15_card : ∀ τ ∈ FM15, Multiset.card τ = 3 := by unfold FM15; decide

theorem FM15_card_eq : FM15.card = 7 := by unfold FM15; decide

theorem FM15_three : ThreeStepLinks FM15 := by unfold ThreeStepLinks Link FM15; decide

theorem familyFacts_FM15 : FamilyFacts FM15 :=
  ⟨FM15_card, by unfold Link FM15; decide,
    by intro i; fin_cases i <;> (unfold Link FM15; decide)⟩

theorem compLabel_FM15 : CompLabel FM15 cM0 := by
  unfold CompLabel Link FM15 cM0; decide

theorem typesInside_FM15 : TypesInside FM15 cM0 := by
  unfold TypesInside FM15 cM0; decide

theorem localWalk4_FM15 (k : Fin 4) : LocalWalk4 FM15 cM0 k := by
  revert k; unfold LocalWalk4 Link FM15 cM0; decide

theorem isolatedMono_FM15 : IsolatedMono FM15 0 := by unfold IsolatedMono FM15; decide

/-- `{000 001 002 012 111 112 333}`. -/
noncomputable def FM16 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 1}, {1, 1, 2}, {3, 3, 3}}

theorem FM16_card : ∀ τ ∈ FM16, Multiset.card τ = 3 := by unfold FM16; decide

theorem FM16_card_eq : FM16.card = 7 := by unfold FM16; decide

theorem FM16_three : ThreeStepLinks FM16 := by unfold ThreeStepLinks Link FM16; decide

theorem familyFacts_FM16 : FamilyFacts FM16 :=
  ⟨FM16_card, by unfold Link FM16; decide,
    by intro i; fin_cases i <;> (unfold Link FM16; decide)⟩

theorem compLabel_FM16 : CompLabel FM16 cM3 := by
  unfold CompLabel Link FM16 cM3; decide

theorem typesInside_FM16 : TypesInside FM16 cM3 := by
  unfold TypesInside FM16 cM3; decide

theorem localWalk4_FM16 (k : Fin 4) : LocalWalk4 FM16 cM3 k := by
  revert k; unfold LocalWalk4 Link FM16 cM3; decide

theorem isolatedMono_FM16 : IsolatedMono FM16 3 := by unfold IsolatedMono FM16; decide

/-- `{000 001 002 012 112 122 333}`. -/
noncomputable def FM17 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM17_card : ∀ τ ∈ FM17, Multiset.card τ = 3 := by unfold FM17; decide

theorem FM17_card_eq : FM17.card = 7 := by unfold FM17; decide

theorem FM17_three : ThreeStepLinks FM17 := by unfold ThreeStepLinks Link FM17; decide

theorem familyFacts_FM17 : FamilyFacts FM17 :=
  ⟨FM17_card, by unfold Link FM17; decide,
    by intro i; fin_cases i <;> (unfold Link FM17; decide)⟩

theorem compLabel_FM17 : CompLabel FM17 cM3 := by
  unfold CompLabel Link FM17 cM3; decide

theorem typesInside_FM17 : TypesInside FM17 cM3 := by
  unfold TypesInside FM17 cM3; decide

theorem localWalk4_FM17 (k : Fin 4) : LocalWalk4 FM17 cM3 k := by
  revert k; unfold LocalWalk4 Link FM17 cM3; decide

theorem isolatedMono_FM17 : IsolatedMono FM17 3 := by unfold IsolatedMono FM17; decide

/-- `{000 001 011 112 122 222 333}`. -/
noncomputable def FM18 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM18_card : ∀ τ ∈ FM18, Multiset.card τ = 3 := by unfold FM18; decide

theorem FM18_card_eq : FM18.card = 7 := by unfold FM18; decide

theorem FM18_three : ThreeStepLinks FM18 := by unfold ThreeStepLinks Link FM18; decide

theorem familyFacts_FM18 : FamilyFacts FM18 :=
  ⟨FM18_card, by unfold Link FM18; decide,
    by intro i; fin_cases i <;> (unfold Link FM18; decide)⟩

theorem compLabel_FM18 : CompLabel FM18 cM3 := by
  unfold CompLabel Link FM18 cM3; decide

theorem typesInside_FM18 : TypesInside FM18 cM3 := by
  unfold TypesInside FM18 cM3; decide

theorem localWalk4_FM18 (k : Fin 4) : LocalWalk4 FM18 cM3 k := by
  revert k; unfold LocalWalk4 Link FM18 cM3; decide

theorem isolatedMono_FM18 : IsolatedMono FM18 3 := by unfold IsolatedMono FM18; decide

/-- `{000 001 002 011 012 022 111 333}`. -/
noncomputable def FM19 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {3, 3, 3}}

theorem FM19_card : ∀ τ ∈ FM19, Multiset.card τ = 3 := by unfold FM19; decide

theorem FM19_card_eq : FM19.card = 8 := by unfold FM19; decide

theorem FM19_three : ThreeStepLinks FM19 := by unfold ThreeStepLinks Link FM19; decide

theorem familyFacts_FM19 : FamilyFacts FM19 :=
  ⟨FM19_card, by unfold Link FM19; decide,
    by intro i; fin_cases i <;> (unfold Link FM19; decide)⟩

theorem compLabel_FM19 : CompLabel FM19 cM3 := by
  unfold CompLabel Link FM19 cM3; decide

theorem typesInside_FM19 : TypesInside FM19 cM3 := by
  unfold TypesInside FM19 cM3; decide

theorem localWalk4_FM19 (k : Fin 4) : LocalWalk4 FM19 cM3 k := by
  revert k; unfold LocalWalk4 Link FM19 cM3; decide

theorem isolatedMono_FM19 : IsolatedMono FM19 3 := by unfold IsolatedMono FM19; decide

/-- `{000 001 002 011 012 022 112 333}`. -/
noncomputable def FM20 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {3, 3, 3}}

theorem FM20_card : ∀ τ ∈ FM20, Multiset.card τ = 3 := by unfold FM20; decide

theorem FM20_card_eq : FM20.card = 8 := by unfold FM20; decide

theorem FM20_three : ThreeStepLinks FM20 := by unfold ThreeStepLinks Link FM20; decide

theorem familyFacts_FM20 : FamilyFacts FM20 :=
  ⟨FM20_card, by unfold Link FM20; decide,
    by intro i; fin_cases i <;> (unfold Link FM20; decide)⟩

theorem compLabel_FM20 : CompLabel FM20 cM3 := by
  unfold CompLabel Link FM20 cM3; decide

theorem typesInside_FM20 : TypesInside FM20 cM3 := by
  unfold TypesInside FM20 cM3; decide

theorem localWalk4_FM20 (k : Fin 4) : LocalWalk4 FM20 cM3 k := by
  revert k; unfold LocalWalk4 Link FM20 cM3; decide

theorem isolatedMono_FM20 : IsolatedMono FM20 3 := by unfold IsolatedMono FM20; decide

/-- `{000 001 002 011 012 111 112 333}`. -/
noncomputable def FM21 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 1}, {1, 1, 2}, {3, 3, 3}}

theorem FM21_card : ∀ τ ∈ FM21, Multiset.card τ = 3 := by unfold FM21; decide

theorem FM21_card_eq : FM21.card = 8 := by unfold FM21; decide

theorem FM21_three : ThreeStepLinks FM21 := by unfold ThreeStepLinks Link FM21; decide

theorem familyFacts_FM21 : FamilyFacts FM21 :=
  ⟨FM21_card, by unfold Link FM21; decide,
    by intro i; fin_cases i <;> (unfold Link FM21; decide)⟩

theorem compLabel_FM21 : CompLabel FM21 cM3 := by
  unfold CompLabel Link FM21 cM3; decide

theorem typesInside_FM21 : TypesInside FM21 cM3 := by
  unfold TypesInside FM21 cM3; decide

theorem localWalk4_FM21 (k : Fin 4) : LocalWalk4 FM21 cM3 k := by
  revert k; unfold LocalWalk4 Link FM21 cM3; decide

theorem isolatedMono_FM21 : IsolatedMono FM21 3 := by unfold IsolatedMono FM21; decide

/-- `{000 001 002 011 012 122 222 333}`. -/
noncomputable def FM22 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM22_card : ∀ τ ∈ FM22, Multiset.card τ = 3 := by unfold FM22; decide

theorem FM22_card_eq : FM22.card = 8 := by unfold FM22; decide

theorem FM22_three : ThreeStepLinks FM22 := by unfold ThreeStepLinks Link FM22; decide

theorem familyFacts_FM22 : FamilyFacts FM22 :=
  ⟨FM22_card, by unfold Link FM22; decide,
    by intro i; fin_cases i <;> (unfold Link FM22; decide)⟩

theorem compLabel_FM22 : CompLabel FM22 cM3 := by
  unfold CompLabel Link FM22 cM3; decide

theorem typesInside_FM22 : TypesInside FM22 cM3 := by
  unfold TypesInside FM22 cM3; decide

theorem localWalk4_FM22 (k : Fin 4) : LocalWalk4 FM22 cM3 k := by
  revert k; unfold LocalWalk4 Link FM22 cM3; decide

theorem isolatedMono_FM22 : IsolatedMono FM22 3 := by unfold IsolatedMono FM22; decide

/-- `{000 001 002 012 111 112 122 333}`. -/
noncomputable def FM23 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM23_card : ∀ τ ∈ FM23, Multiset.card τ = 3 := by unfold FM23; decide

theorem FM23_card_eq : FM23.card = 8 := by unfold FM23; decide

theorem FM23_three : ThreeStepLinks FM23 := by unfold ThreeStepLinks Link FM23; decide

theorem familyFacts_FM23 : FamilyFacts FM23 :=
  ⟨FM23_card, by unfold Link FM23; decide,
    by intro i; fin_cases i <;> (unfold Link FM23; decide)⟩

theorem compLabel_FM23 : CompLabel FM23 cM3 := by
  unfold CompLabel Link FM23 cM3; decide

theorem typesInside_FM23 : TypesInside FM23 cM3 := by
  unfold TypesInside FM23 cM3; decide

theorem localWalk4_FM23 (k : Fin 4) : LocalWalk4 FM23 cM3 k := by
  revert k; unfold LocalWalk4 Link FM23 cM3; decide

theorem isolatedMono_FM23 : IsolatedMono FM23 3 := by unfold IsolatedMono FM23; decide

/-- `{000 001 002 011 012 112 122 333}`. -/
noncomputable def FM24 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM24_card : ∀ τ ∈ FM24, Multiset.card τ = 3 := by unfold FM24; decide

theorem FM24_card_eq : FM24.card = 8 := by unfold FM24; decide

theorem FM24_three : ThreeStepLinks FM24 := by unfold ThreeStepLinks Link FM24; decide

theorem familyFacts_FM24 : FamilyFacts FM24 :=
  ⟨FM24_card, by unfold Link FM24; decide,
    by intro i; fin_cases i <;> (unfold Link FM24; decide)⟩

theorem compLabel_FM24 : CompLabel FM24 cM3 := by
  unfold CompLabel Link FM24 cM3; decide

theorem typesInside_FM24 : TypesInside FM24 cM3 := by
  unfold TypesInside FM24 cM3; decide

theorem localWalk4_FM24 (k : Fin 4) : LocalWalk4 FM24 cM3 k := by
  revert k; unfold LocalWalk4 Link FM24 cM3; decide

theorem isolatedMono_FM24 : IsolatedMono FM24 3 := by unfold IsolatedMono FM24; decide

/-- `{000 001 011 012 022 112 222 333}`. -/
noncomputable def FM25 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM25_card : ∀ τ ∈ FM25, Multiset.card τ = 3 := by unfold FM25; decide

theorem FM25_card_eq : FM25.card = 8 := by unfold FM25; decide

theorem FM25_three : ThreeStepLinks FM25 := by unfold ThreeStepLinks Link FM25; decide

theorem familyFacts_FM25 : FamilyFacts FM25 :=
  ⟨FM25_card, by unfold Link FM25; decide,
    by intro i; fin_cases i <;> (unfold Link FM25; decide)⟩

theorem compLabel_FM25 : CompLabel FM25 cM3 := by
  unfold CompLabel Link FM25 cM3; decide

theorem typesInside_FM25 : TypesInside FM25 cM3 := by
  unfold TypesInside FM25 cM3; decide

theorem localWalk4_FM25 (k : Fin 4) : LocalWalk4 FM25 cM3 k := by
  revert k; unfold LocalWalk4 Link FM25 cM3; decide

theorem isolatedMono_FM25 : IsolatedMono FM25 3 := by unfold IsolatedMono FM25; decide

/-- `{000 001 011 012 022 112 122 333}`. -/
noncomputable def FM26 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM26_card : ∀ τ ∈ FM26, Multiset.card τ = 3 := by unfold FM26; decide

theorem FM26_card_eq : FM26.card = 8 := by unfold FM26; decide

theorem FM26_three : ThreeStepLinks FM26 := by unfold ThreeStepLinks Link FM26; decide

theorem familyFacts_FM26 : FamilyFacts FM26 :=
  ⟨FM26_card, by unfold Link FM26; decide,
    by intro i; fin_cases i <;> (unfold Link FM26; decide)⟩

theorem compLabel_FM26 : CompLabel FM26 cM3 := by
  unfold CompLabel Link FM26 cM3; decide

theorem typesInside_FM26 : TypesInside FM26 cM3 := by
  unfold TypesInside FM26 cM3; decide

theorem localWalk4_FM26 (k : Fin 4) : LocalWalk4 FM26 cM3 k := by
  revert k; unfold LocalWalk4 Link FM26 cM3; decide

theorem isolatedMono_FM26 : IsolatedMono FM26 3 := by unfold IsolatedMono FM26; decide

/-- `{000 112 113 122 123 133 223 233}`. -/
noncomputable def FM27 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {1, 1, 2}, {1, 1, 3}, {1, 2, 2}, {1, 2, 3}, {1, 3, 3}, {2, 2, 3}, {2, 3, 3}}

theorem FM27_card : ∀ τ ∈ FM27, Multiset.card τ = 3 := by unfold FM27; decide

theorem FM27_card_eq : FM27.card = 8 := by unfold FM27; decide

theorem FM27_three : ThreeStepLinks FM27 := by unfold ThreeStepLinks Link FM27; decide

theorem familyFacts_FM27 : FamilyFacts FM27 :=
  ⟨FM27_card, by unfold Link FM27; decide,
    by intro i; fin_cases i <;> (unfold Link FM27; decide)⟩

theorem compLabel_FM27 : CompLabel FM27 cM0 := by
  unfold CompLabel Link FM27 cM0; decide

theorem typesInside_FM27 : TypesInside FM27 cM0 := by
  unfold TypesInside FM27 cM0; decide

theorem localWalk4_FM27 (k : Fin 4) : LocalWalk4 FM27 cM0 k := by
  revert k; unfold LocalWalk4 Link FM27 cM0; decide

theorem isolatedMono_FM27 : IsolatedMono FM27 0 := by unfold IsolatedMono FM27; decide

/-- `{000 001 011 012 112 122 222 333}`. -/
noncomputable def FM28 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM28_card : ∀ τ ∈ FM28, Multiset.card τ = 3 := by unfold FM28; decide

theorem FM28_card_eq : FM28.card = 8 := by unfold FM28; decide

theorem FM28_three : ThreeStepLinks FM28 := by unfold ThreeStepLinks Link FM28; decide

theorem familyFacts_FM28 : FamilyFacts FM28 :=
  ⟨FM28_card, by unfold Link FM28; decide,
    by intro i; fin_cases i <;> (unfold Link FM28; decide)⟩

theorem compLabel_FM28 : CompLabel FM28 cM3 := by
  unfold CompLabel Link FM28 cM3; decide

theorem typesInside_FM28 : TypesInside FM28 cM3 := by
  unfold TypesInside FM28 cM3; decide

theorem localWalk4_FM28 (k : Fin 4) : LocalWalk4 FM28 cM3 k := by
  revert k; unfold LocalWalk4 Link FM28 cM3; decide

theorem isolatedMono_FM28 : IsolatedMono FM28 3 := by unfold IsolatedMono FM28; decide

/-- `{000 001 002 011 022 111 222 333}`. -/
noncomputable def FM29 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem FM29_card : ∀ τ ∈ FM29, Multiset.card τ = 3 := by unfold FM29; decide

theorem FM29_card_eq : FM29.card = 8 := by unfold FM29; decide

theorem FM29_three : ThreeStepLinks FM29 := by unfold ThreeStepLinks Link FM29; decide

theorem familyFacts_FM29 : FamilyFacts FM29 :=
  ⟨FM29_card, by unfold Link FM29; decide,
    by intro i; fin_cases i <;> (unfold Link FM29; decide)⟩

theorem compLabel_FM29 : CompLabel FM29 cM3 := by
  unfold CompLabel Link FM29 cM3; decide

theorem typesInside_FM29 : TypesInside FM29 cM3 := by
  unfold TypesInside FM29 cM3; decide

theorem localWalk4_FM29 (k : Fin 4) : LocalWalk4 FM29 cM3 k := by
  revert k; unfold LocalWalk4 Link FM29 cM3; decide

theorem isolatedMono_FM29 : IsolatedMono FM29 3 := by unfold IsolatedMono FM29; decide

/-- `{000 001 002 011 012 022 111 112 333}`. -/
noncomputable def FM30 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {3, 3, 3}}

theorem FM30_card : ∀ τ ∈ FM30, Multiset.card τ = 3 := by unfold FM30; decide

theorem FM30_card_eq : FM30.card = 9 := by unfold FM30; decide

theorem FM30_three : ThreeStepLinks FM30 := by unfold ThreeStepLinks Link FM30; decide

theorem familyFacts_FM30 : FamilyFacts FM30 :=
  ⟨FM30_card, by unfold Link FM30; decide,
    by intro i; fin_cases i <;> (unfold Link FM30; decide)⟩

theorem compLabel_FM30 : CompLabel FM30 cM3 := by
  unfold CompLabel Link FM30 cM3; decide

theorem typesInside_FM30 : TypesInside FM30 cM3 := by
  unfold TypesInside FM30 cM3; decide

theorem localWalk4_FM30 (k : Fin 4) : LocalWalk4 FM30 cM3 k := by
  revert k; unfold LocalWalk4 Link FM30 cM3; decide

theorem isolatedMono_FM30 : IsolatedMono FM30 3 := by unfold IsolatedMono FM30; decide

/-- `{000 001 002 011 012 022 111 122 333}`. -/
noncomputable def FM31 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 2, 2}, {3, 3, 3}}

theorem FM31_card : ∀ τ ∈ FM31, Multiset.card τ = 3 := by unfold FM31; decide

theorem FM31_card_eq : FM31.card = 9 := by unfold FM31; decide

theorem FM31_three : ThreeStepLinks FM31 := by unfold ThreeStepLinks Link FM31; decide

theorem familyFacts_FM31 : FamilyFacts FM31 :=
  ⟨FM31_card, by unfold Link FM31; decide,
    by intro i; fin_cases i <;> (unfold Link FM31; decide)⟩

theorem compLabel_FM31 : CompLabel FM31 cM3 := by
  unfold CompLabel Link FM31 cM3; decide

theorem typesInside_FM31 : TypesInside FM31 cM3 := by
  unfold TypesInside FM31 cM3; decide

theorem localWalk4_FM31 (k : Fin 4) : LocalWalk4 FM31 cM3 k := by
  revert k; unfold LocalWalk4 Link FM31 cM3; decide

theorem isolatedMono_FM31 : IsolatedMono FM31 3 := by unfold IsolatedMono FM31; decide

/-- `{000 001 002 011 012 022 112 122 333}`. -/
noncomputable def FM32 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM32_card : ∀ τ ∈ FM32, Multiset.card τ = 3 := by unfold FM32; decide

theorem FM32_card_eq : FM32.card = 9 := by unfold FM32; decide

theorem FM32_three : ThreeStepLinks FM32 := by unfold ThreeStepLinks Link FM32; decide

theorem familyFacts_FM32 : FamilyFacts FM32 :=
  ⟨FM32_card, by unfold Link FM32; decide,
    by intro i; fin_cases i <;> (unfold Link FM32; decide)⟩

theorem compLabel_FM32 : CompLabel FM32 cM3 := by
  unfold CompLabel Link FM32 cM3; decide

theorem typesInside_FM32 : TypesInside FM32 cM3 := by
  unfold TypesInside FM32 cM3; decide

theorem localWalk4_FM32 (k : Fin 4) : LocalWalk4 FM32 cM3 k := by
  revert k; unfold LocalWalk4 Link FM32 cM3; decide

theorem isolatedMono_FM32 : IsolatedMono FM32 3 := by unfold IsolatedMono FM32; decide

/-- `{000 001 002 011 012 112 122 222 333}`. -/
noncomputable def FM33 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM33_card : ∀ τ ∈ FM33, Multiset.card τ = 3 := by unfold FM33; decide

theorem FM33_card_eq : FM33.card = 9 := by unfold FM33; decide

theorem FM33_three : ThreeStepLinks FM33 := by unfold ThreeStepLinks Link FM33; decide

theorem familyFacts_FM33 : FamilyFacts FM33 :=
  ⟨FM33_card, by unfold Link FM33; decide,
    by intro i; fin_cases i <;> (unfold Link FM33; decide)⟩

theorem compLabel_FM33 : CompLabel FM33 cM3 := by
  unfold CompLabel Link FM33 cM3; decide

theorem typesInside_FM33 : TypesInside FM33 cM3 := by
  unfold TypesInside FM33 cM3; decide

theorem localWalk4_FM33 (k : Fin 4) : LocalWalk4 FM33 cM3 k := by
  revert k; unfold LocalWalk4 Link FM33 cM3; decide

theorem isolatedMono_FM33 : IsolatedMono FM33 3 := by unfold IsolatedMono FM33; decide

/-- `{000 001 002 011 012 022 111 222 333}`. -/
noncomputable def FM34 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {2, 2, 2}, {3, 3, 3}}

theorem FM34_card : ∀ τ ∈ FM34, Multiset.card τ = 3 := by unfold FM34; decide

theorem FM34_card_eq : FM34.card = 9 := by unfold FM34; decide

theorem FM34_three : ThreeStepLinks FM34 := by unfold ThreeStepLinks Link FM34; decide

theorem familyFacts_FM34 : FamilyFacts FM34 :=
  ⟨FM34_card, by unfold Link FM34; decide,
    by intro i; fin_cases i <;> (unfold Link FM34; decide)⟩

theorem compLabel_FM34 : CompLabel FM34 cM3 := by
  unfold CompLabel Link FM34 cM3; decide

theorem typesInside_FM34 : TypesInside FM34 cM3 := by
  unfold TypesInside FM34 cM3; decide

theorem localWalk4_FM34 (k : Fin 4) : LocalWalk4 FM34 cM3 k := by
  revert k; unfold LocalWalk4 Link FM34 cM3; decide

theorem isolatedMono_FM34 : IsolatedMono FM34 3 := by unfold IsolatedMono FM34; decide

/-- `{000 001 002 011 012 111 122 222 333}`. -/
noncomputable def FM35 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {1, 1, 1}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM35_card : ∀ τ ∈ FM35, Multiset.card τ = 3 := by unfold FM35; decide

theorem FM35_card_eq : FM35.card = 9 := by unfold FM35; decide

theorem FM35_three : ThreeStepLinks FM35 := by unfold ThreeStepLinks Link FM35; decide

theorem familyFacts_FM35 : FamilyFacts FM35 :=
  ⟨FM35_card, by unfold Link FM35; decide,
    by intro i; fin_cases i <;> (unfold Link FM35; decide)⟩

theorem compLabel_FM35 : CompLabel FM35 cM3 := by
  unfold CompLabel Link FM35 cM3; decide

theorem typesInside_FM35 : TypesInside FM35 cM3 := by
  unfold TypesInside FM35 cM3; decide

theorem localWalk4_FM35 (k : Fin 4) : LocalWalk4 FM35 cM3 k := by
  revert k; unfold LocalWalk4 Link FM35 cM3; decide

theorem isolatedMono_FM35 : IsolatedMono FM35 3 := by unfold IsolatedMono FM35; decide

/-- `{000 001 002 012 111 112 122 222 333}`. -/
noncomputable def FM36 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM36_card : ∀ τ ∈ FM36, Multiset.card τ = 3 := by unfold FM36; decide

theorem FM36_card_eq : FM36.card = 9 := by unfold FM36; decide

theorem FM36_three : ThreeStepLinks FM36 := by unfold ThreeStepLinks Link FM36; decide

theorem familyFacts_FM36 : FamilyFacts FM36 :=
  ⟨FM36_card, by unfold Link FM36; decide,
    by intro i; fin_cases i <;> (unfold Link FM36; decide)⟩

theorem compLabel_FM36 : CompLabel FM36 cM3 := by
  unfold CompLabel Link FM36 cM3; decide

theorem typesInside_FM36 : TypesInside FM36 cM3 := by
  unfold TypesInside FM36 cM3; decide

theorem localWalk4_FM36 (k : Fin 4) : LocalWalk4 FM36 cM3 k := by
  revert k; unfold LocalWalk4 Link FM36 cM3; decide

theorem isolatedMono_FM36 : IsolatedMono FM36 3 := by unfold IsolatedMono FM36; decide

/-- `{000 001 002 011 012 022 111 112 122 333}`. -/
noncomputable def FM37 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {3, 3, 3}}

theorem FM37_card : ∀ τ ∈ FM37, Multiset.card τ = 3 := by unfold FM37; decide

theorem FM37_card_eq : FM37.card = 10 := by unfold FM37; decide

theorem FM37_three : ThreeStepLinks FM37 := by unfold ThreeStepLinks Link FM37; decide

theorem familyFacts_FM37 : FamilyFacts FM37 :=
  ⟨FM37_card, by unfold Link FM37; decide,
    by intro i; fin_cases i <;> (unfold Link FM37; decide)⟩

theorem compLabel_FM37 : CompLabel FM37 cM3 := by
  unfold CompLabel Link FM37 cM3; decide

theorem typesInside_FM37 : TypesInside FM37 cM3 := by
  unfold TypesInside FM37 cM3; decide

theorem localWalk4_FM37 (k : Fin 4) : LocalWalk4 FM37 cM3 k := by
  revert k; unfold LocalWalk4 Link FM37 cM3; decide

theorem isolatedMono_FM37 : IsolatedMono FM37 3 := by unfold IsolatedMono FM37; decide

/-- `{000 001 002 011 012 022 111 112 222 333}`. -/
noncomputable def FM38 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM38_card : ∀ τ ∈ FM38, Multiset.card τ = 3 := by unfold FM38; decide

theorem FM38_card_eq : FM38.card = 10 := by unfold FM38; decide

theorem FM38_three : ThreeStepLinks FM38 := by unfold ThreeStepLinks Link FM38; decide

theorem familyFacts_FM38 : FamilyFacts FM38 :=
  ⟨FM38_card, by unfold Link FM38; decide,
    by intro i; fin_cases i <;> (unfold Link FM38; decide)⟩

theorem compLabel_FM38 : CompLabel FM38 cM3 := by
  unfold CompLabel Link FM38 cM3; decide

theorem typesInside_FM38 : TypesInside FM38 cM3 := by
  unfold TypesInside FM38 cM3; decide

theorem localWalk4_FM38 (k : Fin 4) : LocalWalk4 FM38 cM3 k := by
  revert k; unfold LocalWalk4 Link FM38 cM3; decide

theorem isolatedMono_FM38 : IsolatedMono FM38 3 := by unfold IsolatedMono FM38; decide

/-- `{000 001 002 011 012 022 111 112 122 222 333}`. -/
noncomputable def FM39 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {0, 2, 2}, {1, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 2}, {3, 3, 3}}

theorem FM39_card : ∀ τ ∈ FM39, Multiset.card τ = 3 := by unfold FM39; decide

theorem FM39_card_eq : FM39.card = 11 := by unfold FM39; decide

theorem FM39_three : ThreeStepLinks FM39 := by unfold ThreeStepLinks Link FM39; decide

theorem familyFacts_FM39 : FamilyFacts FM39 :=
  ⟨FM39_card, by unfold Link FM39; decide,
    by intro i; fin_cases i <;> (unfold Link FM39; decide)⟩

theorem compLabel_FM39 : CompLabel FM39 cM3 := by
  unfold CompLabel Link FM39 cM3; decide

theorem typesInside_FM39 : TypesInside FM39 cM3 := by
  unfold TypesInside FM39 cM3; decide

theorem localWalk4_FM39 (k : Fin 4) : LocalWalk4 FM39 cM3 k := by
  revert k; unfold LocalWalk4 Link FM39 cM3; decide

theorem isolatedMono_FM39 : IsolatedMono FM39 3 := by unfold IsolatedMono FM39; decide

end PaddedComponents
