/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ClosedZ3
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.UniversalA
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.UniversalB
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.UniversalC
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.UniversalD
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.UniversalE
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM01
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM02
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM03
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM04
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM05
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM06
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM07
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM08
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM09
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM10
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM11
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM12
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM13
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM14
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM15
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM16
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM17
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM18
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM19
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM20
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM21
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM22
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM23
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM24
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM25
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM26
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM27
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM28
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM29
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM30
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM31
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM32
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM33
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM34
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM35
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM36
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM37
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM38
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.InverseFM39

@[expose] public section

/-!
# The 39 disconnected `ℤ/3` families with an isolated monochromatic class

For each `FMxx` (`xx = 01, …, 39`, census order) and every relabelling:
`UniversalCert FMxx` (componentwise refiner, `UniversalA`–`UniversalE`),
`CompleteInverseCert₈ FMxx` (ternary inverse with the large-`γn` mono zero-row mode),
hence `KeevashPaddedSpec FMxx` by the unconditional reduction `keevashPaddedSpec_of_certs₈`.
For these families the original `CompleteInverseCert` is false
(`not_completeInverseCert_FMxx`), so the `₈` reduction is genuinely needed.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption PaddedGeneral PaddedNoCommon

theorem keevashPaddedSpec_FM01 : PaddedInputs.KeevashPaddedSpec FM01 :=
  keevashPaddedSpec_of_certs₈ FM01 familyFacts_FM01 universalCert_FM01 completeInverseCert₈_FM01

theorem not_completeInverseCert_FM01 : ¬ CompleteInverseCert FM01 :=
  not_completeInverseCert_of_isolatedMono FM01 3 isolatedMono_FM01

theorem keevashPaddedSpec_FM02 : PaddedInputs.KeevashPaddedSpec FM02 :=
  keevashPaddedSpec_of_certs₈ FM02 familyFacts_FM02 universalCert_FM02 completeInverseCert₈_FM02

theorem not_completeInverseCert_FM02 : ¬ CompleteInverseCert FM02 :=
  not_completeInverseCert_of_isolatedMono FM02 3 isolatedMono_FM02

theorem keevashPaddedSpec_FM03 : PaddedInputs.KeevashPaddedSpec FM03 :=
  keevashPaddedSpec_of_certs₈ FM03 familyFacts_FM03 universalCert_FM03 completeInverseCert₈_FM03

theorem not_completeInverseCert_FM03 : ¬ CompleteInverseCert FM03 :=
  not_completeInverseCert_of_isolatedMono FM03 3 isolatedMono_FM03

theorem keevashPaddedSpec_FM04 : PaddedInputs.KeevashPaddedSpec FM04 :=
  keevashPaddedSpec_of_certs₈ FM04 familyFacts_FM04 universalCert_FM04 completeInverseCert₈_FM04

theorem not_completeInverseCert_FM04 : ¬ CompleteInverseCert FM04 :=
  not_completeInverseCert_of_isolatedMono FM04 3 isolatedMono_FM04

theorem keevashPaddedSpec_FM05 : PaddedInputs.KeevashPaddedSpec FM05 :=
  keevashPaddedSpec_of_certs₈ FM05 familyFacts_FM05 universalCert_FM05 completeInverseCert₈_FM05

theorem not_completeInverseCert_FM05 : ¬ CompleteInverseCert FM05 :=
  not_completeInverseCert_of_isolatedMono FM05 3 isolatedMono_FM05

theorem keevashPaddedSpec_FM06 : PaddedInputs.KeevashPaddedSpec FM06 :=
  keevashPaddedSpec_of_certs₈ FM06 familyFacts_FM06 universalCert_FM06 completeInverseCert₈_FM06

theorem not_completeInverseCert_FM06 : ¬ CompleteInverseCert FM06 :=
  not_completeInverseCert_of_isolatedMono FM06 3 isolatedMono_FM06

theorem keevashPaddedSpec_FM07 : PaddedInputs.KeevashPaddedSpec FM07 :=
  keevashPaddedSpec_of_certs₈ FM07 familyFacts_FM07 universalCert_FM07 completeInverseCert₈_FM07

theorem not_completeInverseCert_FM07 : ¬ CompleteInverseCert FM07 :=
  not_completeInverseCert_of_isolatedMono FM07 3 isolatedMono_FM07

theorem keevashPaddedSpec_FM08 : PaddedInputs.KeevashPaddedSpec FM08 :=
  keevashPaddedSpec_of_certs₈ FM08 familyFacts_FM08 universalCert_FM08 completeInverseCert₈_FM08

theorem not_completeInverseCert_FM08 : ¬ CompleteInverseCert FM08 :=
  not_completeInverseCert_of_isolatedMono FM08 3 isolatedMono_FM08

theorem keevashPaddedSpec_FM09 : PaddedInputs.KeevashPaddedSpec FM09 :=
  keevashPaddedSpec_of_certs₈ FM09 familyFacts_FM09 universalCert_FM09 completeInverseCert₈_FM09

theorem not_completeInverseCert_FM09 : ¬ CompleteInverseCert FM09 :=
  not_completeInverseCert_of_isolatedMono FM09 0 isolatedMono_FM09

theorem keevashPaddedSpec_FM10 : PaddedInputs.KeevashPaddedSpec FM10 :=
  keevashPaddedSpec_of_certs₈ FM10 familyFacts_FM10 universalCert_FM10 completeInverseCert₈_FM10

theorem not_completeInverseCert_FM10 : ¬ CompleteInverseCert FM10 :=
  not_completeInverseCert_of_isolatedMono FM10 3 isolatedMono_FM10

theorem keevashPaddedSpec_FM11 : PaddedInputs.KeevashPaddedSpec FM11 :=
  keevashPaddedSpec_of_certs₈ FM11 familyFacts_FM11 universalCert_FM11 completeInverseCert₈_FM11

theorem not_completeInverseCert_FM11 : ¬ CompleteInverseCert FM11 :=
  not_completeInverseCert_of_isolatedMono FM11 3 isolatedMono_FM11

theorem keevashPaddedSpec_FM12 : PaddedInputs.KeevashPaddedSpec FM12 :=
  keevashPaddedSpec_of_certs₈ FM12 familyFacts_FM12 universalCert_FM12 completeInverseCert₈_FM12

theorem not_completeInverseCert_FM12 : ¬ CompleteInverseCert FM12 :=
  not_completeInverseCert_of_isolatedMono FM12 3 isolatedMono_FM12

theorem keevashPaddedSpec_FM13 : PaddedInputs.KeevashPaddedSpec FM13 :=
  keevashPaddedSpec_of_certs₈ FM13 familyFacts_FM13 universalCert_FM13 completeInverseCert₈_FM13

theorem not_completeInverseCert_FM13 : ¬ CompleteInverseCert FM13 :=
  not_completeInverseCert_of_isolatedMono FM13 3 isolatedMono_FM13

theorem keevashPaddedSpec_FM14 : PaddedInputs.KeevashPaddedSpec FM14 :=
  keevashPaddedSpec_of_certs₈ FM14 familyFacts_FM14 universalCert_FM14 completeInverseCert₈_FM14

theorem not_completeInverseCert_FM14 : ¬ CompleteInverseCert FM14 :=
  not_completeInverseCert_of_isolatedMono FM14 3 isolatedMono_FM14

theorem keevashPaddedSpec_FM15 : PaddedInputs.KeevashPaddedSpec FM15 :=
  keevashPaddedSpec_of_certs₈ FM15 familyFacts_FM15 universalCert_FM15 completeInverseCert₈_FM15

theorem not_completeInverseCert_FM15 : ¬ CompleteInverseCert FM15 :=
  not_completeInverseCert_of_isolatedMono FM15 0 isolatedMono_FM15

theorem keevashPaddedSpec_FM16 : PaddedInputs.KeevashPaddedSpec FM16 :=
  keevashPaddedSpec_of_certs₈ FM16 familyFacts_FM16 universalCert_FM16 completeInverseCert₈_FM16

theorem not_completeInverseCert_FM16 : ¬ CompleteInverseCert FM16 :=
  not_completeInverseCert_of_isolatedMono FM16 3 isolatedMono_FM16

theorem keevashPaddedSpec_FM17 : PaddedInputs.KeevashPaddedSpec FM17 :=
  keevashPaddedSpec_of_certs₈ FM17 familyFacts_FM17 universalCert_FM17 completeInverseCert₈_FM17

theorem not_completeInverseCert_FM17 : ¬ CompleteInverseCert FM17 :=
  not_completeInverseCert_of_isolatedMono FM17 3 isolatedMono_FM17

theorem keevashPaddedSpec_FM18 : PaddedInputs.KeevashPaddedSpec FM18 :=
  keevashPaddedSpec_of_certs₈ FM18 familyFacts_FM18 universalCert_FM18 completeInverseCert₈_FM18

theorem not_completeInverseCert_FM18 : ¬ CompleteInverseCert FM18 :=
  not_completeInverseCert_of_isolatedMono FM18 3 isolatedMono_FM18

theorem keevashPaddedSpec_FM19 : PaddedInputs.KeevashPaddedSpec FM19 :=
  keevashPaddedSpec_of_certs₈ FM19 familyFacts_FM19 universalCert_FM19 completeInverseCert₈_FM19

theorem not_completeInverseCert_FM19 : ¬ CompleteInverseCert FM19 :=
  not_completeInverseCert_of_isolatedMono FM19 3 isolatedMono_FM19

theorem keevashPaddedSpec_FM20 : PaddedInputs.KeevashPaddedSpec FM20 :=
  keevashPaddedSpec_of_certs₈ FM20 familyFacts_FM20 universalCert_FM20 completeInverseCert₈_FM20

theorem not_completeInverseCert_FM20 : ¬ CompleteInverseCert FM20 :=
  not_completeInverseCert_of_isolatedMono FM20 3 isolatedMono_FM20

theorem keevashPaddedSpec_FM21 : PaddedInputs.KeevashPaddedSpec FM21 :=
  keevashPaddedSpec_of_certs₈ FM21 familyFacts_FM21 universalCert_FM21 completeInverseCert₈_FM21

theorem not_completeInverseCert_FM21 : ¬ CompleteInverseCert FM21 :=
  not_completeInverseCert_of_isolatedMono FM21 3 isolatedMono_FM21

theorem keevashPaddedSpec_FM22 : PaddedInputs.KeevashPaddedSpec FM22 :=
  keevashPaddedSpec_of_certs₈ FM22 familyFacts_FM22 universalCert_FM22 completeInverseCert₈_FM22

theorem not_completeInverseCert_FM22 : ¬ CompleteInverseCert FM22 :=
  not_completeInverseCert_of_isolatedMono FM22 3 isolatedMono_FM22

theorem keevashPaddedSpec_FM23 : PaddedInputs.KeevashPaddedSpec FM23 :=
  keevashPaddedSpec_of_certs₈ FM23 familyFacts_FM23 universalCert_FM23 completeInverseCert₈_FM23

theorem not_completeInverseCert_FM23 : ¬ CompleteInverseCert FM23 :=
  not_completeInverseCert_of_isolatedMono FM23 3 isolatedMono_FM23

theorem keevashPaddedSpec_FM24 : PaddedInputs.KeevashPaddedSpec FM24 :=
  keevashPaddedSpec_of_certs₈ FM24 familyFacts_FM24 universalCert_FM24 completeInverseCert₈_FM24

theorem not_completeInverseCert_FM24 : ¬ CompleteInverseCert FM24 :=
  not_completeInverseCert_of_isolatedMono FM24 3 isolatedMono_FM24

theorem keevashPaddedSpec_FM25 : PaddedInputs.KeevashPaddedSpec FM25 :=
  keevashPaddedSpec_of_certs₈ FM25 familyFacts_FM25 universalCert_FM25 completeInverseCert₈_FM25

theorem not_completeInverseCert_FM25 : ¬ CompleteInverseCert FM25 :=
  not_completeInverseCert_of_isolatedMono FM25 3 isolatedMono_FM25

theorem keevashPaddedSpec_FM26 : PaddedInputs.KeevashPaddedSpec FM26 :=
  keevashPaddedSpec_of_certs₈ FM26 familyFacts_FM26 universalCert_FM26 completeInverseCert₈_FM26

theorem not_completeInverseCert_FM26 : ¬ CompleteInverseCert FM26 :=
  not_completeInverseCert_of_isolatedMono FM26 3 isolatedMono_FM26

theorem keevashPaddedSpec_FM27 : PaddedInputs.KeevashPaddedSpec FM27 :=
  keevashPaddedSpec_of_certs₈ FM27 familyFacts_FM27 universalCert_FM27 completeInverseCert₈_FM27

theorem not_completeInverseCert_FM27 : ¬ CompleteInverseCert FM27 :=
  not_completeInverseCert_of_isolatedMono FM27 0 isolatedMono_FM27

theorem keevashPaddedSpec_FM28 : PaddedInputs.KeevashPaddedSpec FM28 :=
  keevashPaddedSpec_of_certs₈ FM28 familyFacts_FM28 universalCert_FM28 completeInverseCert₈_FM28

theorem not_completeInverseCert_FM28 : ¬ CompleteInverseCert FM28 :=
  not_completeInverseCert_of_isolatedMono FM28 3 isolatedMono_FM28

theorem keevashPaddedSpec_FM29 : PaddedInputs.KeevashPaddedSpec FM29 :=
  keevashPaddedSpec_of_certs₈ FM29 familyFacts_FM29 universalCert_FM29 completeInverseCert₈_FM29

theorem not_completeInverseCert_FM29 : ¬ CompleteInverseCert FM29 :=
  not_completeInverseCert_of_isolatedMono FM29 3 isolatedMono_FM29

theorem keevashPaddedSpec_FM30 : PaddedInputs.KeevashPaddedSpec FM30 :=
  keevashPaddedSpec_of_certs₈ FM30 familyFacts_FM30 universalCert_FM30 completeInverseCert₈_FM30

theorem not_completeInverseCert_FM30 : ¬ CompleteInverseCert FM30 :=
  not_completeInverseCert_of_isolatedMono FM30 3 isolatedMono_FM30

theorem keevashPaddedSpec_FM31 : PaddedInputs.KeevashPaddedSpec FM31 :=
  keevashPaddedSpec_of_certs₈ FM31 familyFacts_FM31 universalCert_FM31 completeInverseCert₈_FM31

theorem not_completeInverseCert_FM31 : ¬ CompleteInverseCert FM31 :=
  not_completeInverseCert_of_isolatedMono FM31 3 isolatedMono_FM31

theorem keevashPaddedSpec_FM32 : PaddedInputs.KeevashPaddedSpec FM32 :=
  keevashPaddedSpec_of_certs₈ FM32 familyFacts_FM32 universalCert_FM32 completeInverseCert₈_FM32

theorem not_completeInverseCert_FM32 : ¬ CompleteInverseCert FM32 :=
  not_completeInverseCert_of_isolatedMono FM32 3 isolatedMono_FM32

theorem keevashPaddedSpec_FM33 : PaddedInputs.KeevashPaddedSpec FM33 :=
  keevashPaddedSpec_of_certs₈ FM33 familyFacts_FM33 universalCert_FM33 completeInverseCert₈_FM33

theorem not_completeInverseCert_FM33 : ¬ CompleteInverseCert FM33 :=
  not_completeInverseCert_of_isolatedMono FM33 3 isolatedMono_FM33

theorem keevashPaddedSpec_FM34 : PaddedInputs.KeevashPaddedSpec FM34 :=
  keevashPaddedSpec_of_certs₈ FM34 familyFacts_FM34 universalCert_FM34 completeInverseCert₈_FM34

theorem not_completeInverseCert_FM34 : ¬ CompleteInverseCert FM34 :=
  not_completeInverseCert_of_isolatedMono FM34 3 isolatedMono_FM34

theorem keevashPaddedSpec_FM35 : PaddedInputs.KeevashPaddedSpec FM35 :=
  keevashPaddedSpec_of_certs₈ FM35 familyFacts_FM35 universalCert_FM35 completeInverseCert₈_FM35

theorem not_completeInverseCert_FM35 : ¬ CompleteInverseCert FM35 :=
  not_completeInverseCert_of_isolatedMono FM35 3 isolatedMono_FM35

theorem keevashPaddedSpec_FM36 : PaddedInputs.KeevashPaddedSpec FM36 :=
  keevashPaddedSpec_of_certs₈ FM36 familyFacts_FM36 universalCert_FM36 completeInverseCert₈_FM36

theorem not_completeInverseCert_FM36 : ¬ CompleteInverseCert FM36 :=
  not_completeInverseCert_of_isolatedMono FM36 3 isolatedMono_FM36

theorem keevashPaddedSpec_FM37 : PaddedInputs.KeevashPaddedSpec FM37 :=
  keevashPaddedSpec_of_certs₈ FM37 familyFacts_FM37 universalCert_FM37 completeInverseCert₈_FM37

theorem not_completeInverseCert_FM37 : ¬ CompleteInverseCert FM37 :=
  not_completeInverseCert_of_isolatedMono FM37 3 isolatedMono_FM37

theorem keevashPaddedSpec_FM38 : PaddedInputs.KeevashPaddedSpec FM38 :=
  keevashPaddedSpec_of_certs₈ FM38 familyFacts_FM38 universalCert_FM38 completeInverseCert₈_FM38

theorem not_completeInverseCert_FM38 : ¬ CompleteInverseCert FM38 :=
  not_completeInverseCert_of_isolatedMono FM38 3 isolatedMono_FM38

theorem keevashPaddedSpec_FM39 : PaddedInputs.KeevashPaddedSpec FM39 :=
  keevashPaddedSpec_of_certs₈ FM39 familyFacts_FM39 universalCert_FM39 completeInverseCert₈_FM39

theorem not_completeInverseCert_FM39 : ¬ CompleteInverseCert FM39 :=
  not_completeInverseCert_of_isolatedMono FM39 3 isolatedMono_FM39

/-- The 39 isolated-mono `ℤ/3` families, in census order. -/
noncomputable def monoList : List (Finset (Multiset (Fin 4))) :=
  [FM01, FM02, FM03, FM04, FM05, FM06, FM07, FM08,
   FM09, FM10, FM11, FM12, FM13, FM14, FM15, FM16,
   FM17, FM18, FM19, FM20, FM21, FM22, FM23, FM24,
   FM25, FM26, FM27, FM28, FM29, FM30, FM31, FM32,
   FM33, FM34, FM35, FM36, FM37, FM38, FM39]

theorem keevashPaddedSpec_of_mem_monoList : ∀ G ∈ monoList, PaddedInputs.KeevashPaddedSpec G := by
  intro G hG
  simp only [monoList, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [keevashPaddedSpec_FM01, keevashPaddedSpec_FM02, keevashPaddedSpec_FM03, keevashPaddedSpec_FM04,
    keevashPaddedSpec_FM05, keevashPaddedSpec_FM06, keevashPaddedSpec_FM07, keevashPaddedSpec_FM08,
    keevashPaddedSpec_FM09, keevashPaddedSpec_FM10, keevashPaddedSpec_FM11, keevashPaddedSpec_FM12,
    keevashPaddedSpec_FM13, keevashPaddedSpec_FM14, keevashPaddedSpec_FM15, keevashPaddedSpec_FM16,
    keevashPaddedSpec_FM17, keevashPaddedSpec_FM18, keevashPaddedSpec_FM19, keevashPaddedSpec_FM20,
    keevashPaddedSpec_FM21, keevashPaddedSpec_FM22, keevashPaddedSpec_FM23, keevashPaddedSpec_FM24,
    keevashPaddedSpec_FM25, keevashPaddedSpec_FM26, keevashPaddedSpec_FM27, keevashPaddedSpec_FM28,
    keevashPaddedSpec_FM29, keevashPaddedSpec_FM30, keevashPaddedSpec_FM31, keevashPaddedSpec_FM32,
    keevashPaddedSpec_FM33, keevashPaddedSpec_FM34, keevashPaddedSpec_FM35, keevashPaddedSpec_FM36,
    keevashPaddedSpec_FM37, keevashPaddedSpec_FM38, keevashPaddedSpec_FM39]

theorem card_three_of_mem_monoList : ∀ G ∈ monoList, ∀ τ ∈ G, Multiset.card τ = 3 := by
  intro G hG
  simp only [monoList, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [FM01_card, FM02_card, FM03_card, FM04_card,
    FM05_card, FM06_card, FM07_card, FM08_card,
    FM09_card, FM10_card, FM11_card, FM12_card,
    FM13_card, FM14_card, FM15_card, FM16_card,
    FM17_card, FM18_card, FM19_card, FM20_card,
    FM21_card, FM22_card, FM23_card, FM24_card,
    FM25_card, FM26_card, FM27_card, FM28_card,
    FM29_card, FM30_card, FM31_card, FM32_card,
    FM33_card, FM34_card, FM35_card, FM36_card,
    FM37_card, FM38_card, FM39_card]

theorem not_completeInverseCert_of_mem_monoList : ∀ G ∈ monoList, ¬ CompleteInverseCert G := by
  intro G hG
  simp only [monoList, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [not_completeInverseCert_FM01, not_completeInverseCert_FM02, not_completeInverseCert_FM03, not_completeInverseCert_FM04,
    not_completeInverseCert_FM05, not_completeInverseCert_FM06, not_completeInverseCert_FM07, not_completeInverseCert_FM08,
    not_completeInverseCert_FM09, not_completeInverseCert_FM10, not_completeInverseCert_FM11, not_completeInverseCert_FM12,
    not_completeInverseCert_FM13, not_completeInverseCert_FM14, not_completeInverseCert_FM15, not_completeInverseCert_FM16,
    not_completeInverseCert_FM17, not_completeInverseCert_FM18, not_completeInverseCert_FM19, not_completeInverseCert_FM20,
    not_completeInverseCert_FM21, not_completeInverseCert_FM22, not_completeInverseCert_FM23, not_completeInverseCert_FM24,
    not_completeInverseCert_FM25, not_completeInverseCert_FM26, not_completeInverseCert_FM27, not_completeInverseCert_FM28,
    not_completeInverseCert_FM29, not_completeInverseCert_FM30, not_completeInverseCert_FM31, not_completeInverseCert_FM32,
    not_completeInverseCert_FM33, not_completeInverseCert_FM34, not_completeInverseCert_FM35, not_completeInverseCert_FM36,
    not_completeInverseCert_FM37, not_completeInverseCert_FM38, not_completeInverseCert_FM39]

/-- The 39 isolated-mono `ℤ/3` families, up to relabelling of the classes. Decidable. -/
def CoveredMono (F : Finset (Multiset (Fin 4))) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∃ G ∈ monoList, F = BlowupB.permFam σ G

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredMono F) := by
  unfold CoveredMono; infer_instance

/-- **The padded Keevash statement for every family in `CoveredMono`.** -/
theorem keevashPaddedSpec_of_coveredMono (F : Finset (Multiset (Fin 4))) (hF : CoveredMono F) :
    PaddedInputs.KeevashPaddedSpec F := by
  obtain ⟨σ, G, hG, rfl⟩ := hF
  exact BlowupB.keevashPaddedSpec_perm σ (keevashPaddedSpec_of_mem_monoList G hG)

theorem card_three_of_coveredMono (F : Finset (Multiset (Fin 4))) (hF : CoveredMono F) :
    ∀ τ ∈ F, Multiset.card τ = 3 := by
  obtain ⟨σ, G, hG, rfl⟩ := hF
  exact BlowupB.card_three_perm (σ := σ) (card_three_of_mem_monoList G hG)

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks TypedTransformer PaddedComponents

/-- `CoveredFamily₇` plus the 39 isolated-mono `ℤ/3` families of `CoveredMono`. -/
def CoveredFamily₈ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₇ F ∨ CoveredMono F

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily₈ F) := by
  unfold CoveredFamily₈; infer_instance

theorem keevashPaddedSpec_of_covered₈ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₈ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | hF
  · exact keevashPaddedSpec_of_covered₇ F hF
  · exact keevashPaddedSpec_of_coveredMono F hF

/-- The proved fragment of `TeoremaBTarget.TargetFour`, extended by the 39 mono families. -/
theorem targetFour_on_covered₈ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₈ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₈ F hF

/-- **Theorem B** (weighted form) for every family in `CoveredFamily₈`. -/
theorem teoremaB_covered₈ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily₈ F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ F, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair F a b →
            |(∑ τ ∈ F, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset :=
  teoremaB_of_keevash (keevashTypedSpec_of_padded hcard (keevashPaddedSpec_of_covered₈ F hF))
    γ ω₁ hγ hω₁

/-- **Theorem B** (weighted form) for every family in `CoveredMono`, with no card hypothesis. -/
theorem teoremaB_coveredMono (F : Finset (Multiset (Fin 4))) (hF : CoveredMono F)
    (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ F, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair F a b →
            |(∑ τ ∈ F, wt τ * ((∑ c ∈ univ.filter
                (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset :=
  teoremaB_covered₈ F (Or.inr hF) (card_three_of_coveredMono F hF) γ ω₁ hγ hω₁

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_covered₈
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_covered₈
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_coveredMono
#print axioms PaddedComponents.not_completeInverseCert_of_mem_monoList
