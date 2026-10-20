/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Certificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

def certificate12_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate12_root0000_checked :
    certificate12_root0000.verify [13,15,16,19] ∅ = true := rfl

def certificate12_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 16) (.leaf 23)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate12_root0001_checked :
    certificate12_root0001.verify [13,15,16,19] {9} = true := rfl

def certificate12_root000 : OrbitCertificate :=
  (.split certificate12_root0000 certificate12_root0001)

theorem certificate12_root000_checked :
    certificate12_root000.verify [9,13,15,16,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root0000_checked, certificate12_root0001_checked⟩

def certificate12_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 22) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate12_root0010_checked :
    certificate12_root0010.verify [13,15,16,19] {7} = true := rfl

def certificate12_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate12_root0011_checked :
    certificate12_root0011.verify [13,15,16,19] {9,7} = true := rfl

def certificate12_root001 : OrbitCertificate :=
  (.split certificate12_root0010 certificate12_root0011)

theorem certificate12_root001_checked :
    certificate12_root001.verify [9,13,15,16,19] {7} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root0010_checked, certificate12_root0011_checked⟩

def certificate12_root00 : OrbitCertificate :=
  (.split certificate12_root000 certificate12_root001)

theorem certificate12_root00_checked :
    certificate12_root00.verify [7,9,13,15,16,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root000_checked, certificate12_root001_checked⟩

def certificate12_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 19)) (.split (.leaf 12) (.leaf 23))) (.split (.split (.leaf 19) (.leaf 19)) (.split (.leaf 18) (.leaf 23)))))

theorem certificate12_root0100_checked :
    certificate12_root0100.verify [13,15,16,19] {6} = true := rfl

def certificate12_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate12_root0101_checked :
    certificate12_root0101.verify [13,15,16,19] {9,6} = true := rfl

def certificate12_root010 : OrbitCertificate :=
  (.split certificate12_root0100 certificate12_root0101)

theorem certificate12_root010_checked :
    certificate12_root010.verify [9,13,15,16,19] {6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root0100_checked, certificate12_root0101_checked⟩

def certificate12_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 17)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 23)) (.split (.leaf 12) (.leaf 23)))))

theorem certificate12_root0110_checked :
    certificate12_root0110.verify [13,15,16,19] {7,6} = true := rfl

def certificate12_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 5) (.leaf 5)) (.split (.leaf 4) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 17)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate12_root0111_checked :
    certificate12_root0111.verify [13,15,16,19] {9,7,6} = true := rfl

def certificate12_root011 : OrbitCertificate :=
  (.split certificate12_root0110 certificate12_root0111)

theorem certificate12_root011_checked :
    certificate12_root011.verify [9,13,15,16,19] {7,6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root0110_checked, certificate12_root0111_checked⟩

def certificate12_root01 : OrbitCertificate :=
  (.split certificate12_root010 certificate12_root011)

theorem certificate12_root01_checked :
    certificate12_root01.verify [7,9,13,15,16,19] {6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root010_checked, certificate12_root011_checked⟩

def certificate12_root0 : OrbitCertificate :=
  (.split certificate12_root00 certificate12_root01)

theorem certificate12_root0_checked :
    certificate12_root0.verify [6,7,9,13,15,16,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root00_checked, certificate12_root01_checked⟩

def certificate12_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 18) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 22)))))

theorem certificate12_root1000_checked :
    certificate12_root1000.verify [13,15,16,19] {5} = true := rfl

def certificate12_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 4) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate12_root1001_checked :
    certificate12_root1001.verify [13,15,16,19] {9,5} = true := rfl

def certificate12_root100 : OrbitCertificate :=
  (.split certificate12_root1000 certificate12_root1001)

theorem certificate12_root100_checked :
    certificate12_root100.verify [9,13,15,16,19] {5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root1000_checked, certificate12_root1001_checked⟩

def certificate12_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate12_root1010_checked :
    certificate12_root1010.verify [13,15,16,19] {7,5} = true := rfl

def certificate12_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 4) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate12_root1011_checked :
    certificate12_root1011.verify [13,15,16,19] {9,7,5} = true := rfl

def certificate12_root101 : OrbitCertificate :=
  (.split certificate12_root1010 certificate12_root1011)

theorem certificate12_root101_checked :
    certificate12_root101.verify [9,13,15,16,19] {7,5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root1010_checked, certificate12_root1011_checked⟩

def certificate12_root10 : OrbitCertificate :=
  (.split certificate12_root100 certificate12_root101)

theorem certificate12_root10_checked :
    certificate12_root10.verify [7,9,13,15,16,19] {5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root100_checked, certificate12_root101_checked⟩

def certificate12_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 18) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 19)) (.split (.leaf 12) (.leaf 22))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 22)))))

theorem certificate12_root1100_checked :
    certificate12_root1100.verify [13,15,16,19] {6,5} = true := rfl

def certificate12_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 4) (.leaf 17))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 13)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate12_root1101_checked :
    certificate12_root1101.verify [13,15,16,19] {9,6,5} = true := rfl

def certificate12_root110 : OrbitCertificate :=
  (.split certificate12_root1100 certificate12_root1101)

theorem certificate12_root110_checked :
    certificate12_root110.verify [9,13,15,16,19] {6,5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root1100_checked, certificate12_root1101_checked⟩

def certificate12_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate12_root1110_checked :
    certificate12_root1110.verify [13,15,16,19] {7,6,5} = true := rfl

def certificate12_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 4) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate12_root1111_checked :
    certificate12_root1111.verify [13,15,16,19] {9,7,6,5} = true := rfl

def certificate12_root111 : OrbitCertificate :=
  (.split certificate12_root1110 certificate12_root1111)

theorem certificate12_root111_checked :
    certificate12_root111.verify [9,13,15,16,19] {7,6,5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root1110_checked, certificate12_root1111_checked⟩

def certificate12_root11 : OrbitCertificate :=
  (.split certificate12_root110 certificate12_root111)

theorem certificate12_root11_checked :
    certificate12_root11.verify [7,9,13,15,16,19] {6,5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root110_checked, certificate12_root111_checked⟩

def certificate12_root1 : OrbitCertificate :=
  (.split certificate12_root10 certificate12_root11)

theorem certificate12_root1_checked :
    certificate12_root1.verify [6,7,9,13,15,16,19] {5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root10_checked, certificate12_root11_checked⟩

def certificate12_root : OrbitCertificate :=
  (.split certificate12_root0 certificate12_root1)

theorem certificate12_root_checked :
    certificate12_root.verify [5,6,7,9,13,15,16,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate12_root0_checked, certificate12_root1_checked⟩

theorem covered_12 : ∀ C ∈ (box 12).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [5,6,7,9,13,15,16,19] ∅ certificate12_root
    certificate12_root_checked C
  have hs : C ⊆ ([5,6,7,9,13,15,16,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_12
