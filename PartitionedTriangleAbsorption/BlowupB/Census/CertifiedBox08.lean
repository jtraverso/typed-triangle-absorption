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

def certificate08_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate08_root0000_checked :
    certificate08_root0000.verify [10,11,18,19] ∅ = true := rfl

def certificate08_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate08_root0001_checked :
    certificate08_root0001.verify [10,11,18,19] {9} = true := rfl

def certificate08_root000 : OrbitCertificate :=
  (.split certificate08_root0000 certificate08_root0001)

theorem certificate08_root000_checked :
    certificate08_root000.verify [9,10,11,18,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root0000_checked, certificate08_root0001_checked⟩

def certificate08_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 8) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 14) (.leaf 21)) (.split (.leaf 20) (.leaf 21)))))

theorem certificate08_root0010_checked :
    certificate08_root0010.verify [10,11,18,19] {8} = true := rfl

def certificate08_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate08_root0011_checked :
    certificate08_root0011.verify [10,11,18,19] {9,8} = true := rfl

def certificate08_root001 : OrbitCertificate :=
  (.split certificate08_root0010 certificate08_root0011)

theorem certificate08_root001_checked :
    certificate08_root001.verify [9,10,11,18,19] {8} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root0010_checked, certificate08_root0011_checked⟩

def certificate08_root00 : OrbitCertificate :=
  (.split certificate08_root000 certificate08_root001)

theorem certificate08_root00_checked :
    certificate08_root00.verify [8,9,10,11,18,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root000_checked, certificate08_root001_checked⟩

def certificate08_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 19)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 20) (.leaf 19))) (.split (.split (.leaf 0) (.leaf 19)) (.split (.leaf 20) (.leaf 19)))))

theorem certificate08_root0100_checked :
    certificate08_root0100.verify [10,11,18,19] {5} = true := rfl

def certificate08_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate08_root0101_checked :
    certificate08_root0101.verify [10,11,18,19] {9,5} = true := rfl

def certificate08_root010 : OrbitCertificate :=
  (.split certificate08_root0100 certificate08_root0101)

theorem certificate08_root010_checked :
    certificate08_root010.verify [9,10,11,18,19] {5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root0100_checked, certificate08_root0101_checked⟩

def certificate08_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 5)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 20) (.leaf 21))) (.split (.split (.leaf 14) (.leaf 19)) (.split (.leaf 20) (.leaf 19)))))

theorem certificate08_root0110_checked :
    certificate08_root0110.verify [10,11,18,19] {8,5} = true := rfl

def certificate08_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate08_root0111_checked :
    certificate08_root0111.verify [10,11,18,19] {9,8,5} = true := rfl

def certificate08_root011 : OrbitCertificate :=
  (.split certificate08_root0110 certificate08_root0111)

theorem certificate08_root011_checked :
    certificate08_root011.verify [9,10,11,18,19] {8,5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root0110_checked, certificate08_root0111_checked⟩

def certificate08_root01 : OrbitCertificate :=
  (.split certificate08_root010 certificate08_root011)

theorem certificate08_root01_checked :
    certificate08_root01.verify [8,9,10,11,18,19] {5} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root010_checked, certificate08_root011_checked⟩

def certificate08_root0 : OrbitCertificate :=
  (.split certificate08_root00 certificate08_root01)

theorem certificate08_root0_checked :
    certificate08_root0.verify [5,8,9,10,11,18,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root00_checked, certificate08_root01_checked⟩

def certificate08_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 19) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate08_root1000_checked :
    certificate08_root1000.verify [10,11,18,19] {4} = true := rfl

def certificate08_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))))

theorem certificate08_root1001_checked :
    certificate08_root1001.verify [10,11,18,19] {9,4} = true := rfl

def certificate08_root100 : OrbitCertificate :=
  (.split certificate08_root1000 certificate08_root1001)

theorem certificate08_root100_checked :
    certificate08_root100.verify [9,10,11,18,19] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root1000_checked, certificate08_root1001_checked⟩

def certificate08_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 3)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 14) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 14) (.leaf 21)))))

theorem certificate08_root1010_checked :
    certificate08_root1010.verify [10,11,18,19] {8,4} = true := rfl

def certificate08_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate08_root1011_checked :
    certificate08_root1011.verify [10,11,18,19] {9,8,4} = true := rfl

def certificate08_root101 : OrbitCertificate :=
  (.split certificate08_root1010 certificate08_root1011)

theorem certificate08_root101_checked :
    certificate08_root101.verify [9,10,11,18,19] {8,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root1010_checked, certificate08_root1011_checked⟩

def certificate08_root10 : OrbitCertificate :=
  (.split certificate08_root100 certificate08_root101)

theorem certificate08_root10_checked :
    certificate08_root10.verify [8,9,10,11,18,19] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root100_checked, certificate08_root101_checked⟩

def certificate08_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate08_root1100_checked :
    certificate08_root1100.verify [10,11,18,19] {5,4} = true := rfl

def certificate08_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))) (.split (.split (.split (.leaf 1) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))))

theorem certificate08_root1101_checked :
    certificate08_root1101.verify [10,11,18,19] {9,5,4} = true := rfl

def certificate08_root110 : OrbitCertificate :=
  (.split certificate08_root1100 certificate08_root1101)

theorem certificate08_root110_checked :
    certificate08_root110.verify [9,10,11,18,19] {5,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root1100_checked, certificate08_root1101_checked⟩

def certificate08_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 14) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 14) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 14) (.leaf 19)))))

theorem certificate08_root1110_checked :
    certificate08_root1110.verify [10,11,18,19] {8,5,4} = true := rfl

def certificate08_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))) (.split (.split (.split (.leaf 1) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))))

theorem certificate08_root1111_checked :
    certificate08_root1111.verify [10,11,18,19] {9,8,5,4} = true := rfl

def certificate08_root111 : OrbitCertificate :=
  (.split certificate08_root1110 certificate08_root1111)

theorem certificate08_root111_checked :
    certificate08_root111.verify [9,10,11,18,19] {8,5,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root1110_checked, certificate08_root1111_checked⟩

def certificate08_root11 : OrbitCertificate :=
  (.split certificate08_root110 certificate08_root111)

theorem certificate08_root11_checked :
    certificate08_root11.verify [8,9,10,11,18,19] {5,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root110_checked, certificate08_root111_checked⟩

def certificate08_root1 : OrbitCertificate :=
  (.split certificate08_root10 certificate08_root11)

theorem certificate08_root1_checked :
    certificate08_root1.verify [5,8,9,10,11,18,19] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root10_checked, certificate08_root11_checked⟩

def certificate08_root : OrbitCertificate :=
  (.split certificate08_root0 certificate08_root1)

theorem certificate08_root_checked :
    certificate08_root.verify [4,5,8,9,10,11,18,19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate08_root0_checked, certificate08_root1_checked⟩

theorem covered_08 : ∀ C ∈ (box 8).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [4,5,8,9,10,11,18,19] ∅ certificate08_root
    certificate08_root_checked C
  have hs : C ⊆ ([4,5,8,9,10,11,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_08
