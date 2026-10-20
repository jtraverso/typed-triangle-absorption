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

def certificate20_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate20_root0000_checked :
    certificate20_root0000.verify [13,14,16,17] ∅ = true := rfl

def certificate20_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 18) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 18)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 19) (.leaf 18)) (.split (.leaf 18) (.leaf 18)))))

theorem certificate20_root0001_checked :
    certificate20_root0001.verify [13,14,16,17] {6} = true := rfl

def certificate20_root000 : OrbitCertificate :=
  (.split certificate20_root0000 certificate20_root0001)

theorem certificate20_root000_checked :
    certificate20_root000.verify [6,13,14,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root0000_checked, certificate20_root0001_checked⟩

def certificate20_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 15) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 10) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))))

theorem certificate20_root0010_checked :
    certificate20_root0010.verify [13,14,16,17] {3} = true := rfl

def certificate20_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 4) (.leaf 17))) (.split (.split (.leaf 15) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 23)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate20_root0011_checked :
    certificate20_root0011.verify [13,14,16,17] {6,3} = true := rfl

def certificate20_root001 : OrbitCertificate :=
  (.split certificate20_root0010 certificate20_root0011)

theorem certificate20_root001_checked :
    certificate20_root001.verify [6,13,14,16,17] {3} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root0010_checked, certificate20_root0011_checked⟩

def certificate20_root00 : OrbitCertificate :=
  (.split certificate20_root000 certificate20_root001)

theorem certificate20_root00_checked :
    certificate20_root00.verify [3,6,13,14,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root000_checked, certificate20_root001_checked⟩

def certificate20_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 12) (.leaf 8)) (.split (.leaf 12) (.leaf 8)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 12) (.leaf 8)) (.split (.leaf 12) (.leaf 8)))))

theorem certificate20_root0100_checked :
    certificate20_root0100.verify [13,14,16,17] {1} = true := rfl

def certificate20_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 13) (.leaf 9)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 6) (.leaf 18)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 6) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate20_root0101_checked :
    certificate20_root0101.verify [13,14,16,17] {6,1} = true := rfl

def certificate20_root010 : OrbitCertificate :=
  (.split certificate20_root0100 certificate20_root0101)

theorem certificate20_root010_checked :
    certificate20_root010.verify [6,13,14,16,17] {1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root0100_checked, certificate20_root0101_checked⟩

def certificate20_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 2) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 7) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))))

theorem certificate20_root0110_checked :
    certificate20_root0110.verify [13,14,16,17] {3,1} = true := rfl

def certificate20_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 2) (.leaf 4)))) (.split (.split (.split (.leaf 2) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 2)) (.split (.leaf 2) (.leaf 8)))))

theorem certificate20_root0111_checked :
    certificate20_root0111.verify [13,14,16,17] {6,3,1} = true := rfl

def certificate20_root011 : OrbitCertificate :=
  (.split certificate20_root0110 certificate20_root0111)

theorem certificate20_root011_checked :
    certificate20_root011.verify [6,13,14,16,17] {3,1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root0110_checked, certificate20_root0111_checked⟩

def certificate20_root01 : OrbitCertificate :=
  (.split certificate20_root010 certificate20_root011)

theorem certificate20_root01_checked :
    certificate20_root01.verify [3,6,13,14,16,17] {1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root010_checked, certificate20_root011_checked⟩

def certificate20_root0 : OrbitCertificate :=
  (.split certificate20_root00 certificate20_root01)

theorem certificate20_root0_checked :
    certificate20_root0.verify [1,3,6,13,14,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root00_checked, certificate20_root01_checked⟩

def certificate20_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 6) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 8) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))))

theorem certificate20_root1000_checked :
    certificate20_root1000.verify [13,14,16,17] {0} = true := rfl

def certificate20_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 11)) (.split (.leaf 2) (.leaf 10)))) (.split (.split (.split (.leaf 6) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 6) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))))

theorem certificate20_root1001_checked :
    certificate20_root1001.verify [13,14,16,17] {6,0} = true := rfl

def certificate20_root100 : OrbitCertificate :=
  (.split certificate20_root1000 certificate20_root1001)

theorem certificate20_root100_checked :
    certificate20_root100.verify [6,13,14,16,17] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root1000_checked, certificate20_root1001_checked⟩

def certificate20_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 11)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 10) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))))

theorem certificate20_root1010_checked :
    certificate20_root1010.verify [13,14,16,17] {3,0} = true := rfl

def certificate20_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 4) (.leaf 4))) (.split (.split (.leaf 9) (.leaf 11)) (.split (.leaf 4) (.leaf 4)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 10)) (.split (.leaf 2) (.leaf 10)))))

theorem certificate20_root1011_checked :
    certificate20_root1011.verify [13,14,16,17] {6,3,0} = true := rfl

def certificate20_root101 : OrbitCertificate :=
  (.split certificate20_root1010 certificate20_root1011)

theorem certificate20_root101_checked :
    certificate20_root101.verify [6,13,14,16,17] {3,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root1010_checked, certificate20_root1011_checked⟩

def certificate20_root10 : OrbitCertificate :=
  (.split certificate20_root100 certificate20_root101)

theorem certificate20_root10_checked :
    certificate20_root10.verify [3,6,13,14,16,17] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root100_checked, certificate20_root101_checked⟩

def certificate20_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))))

theorem certificate20_root1100_checked :
    certificate20_root1100.verify [13,14,16,17] {1,0} = true := rfl

def certificate20_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 2) (.leaf 4)))) (.split (.split (.split (.leaf 6) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 6) (.leaf 8)) (.split (.leaf 2) (.leaf 8)))))

theorem certificate20_root1101_checked :
    certificate20_root1101.verify [13,14,16,17] {6,1,0} = true := rfl

def certificate20_root110 : OrbitCertificate :=
  (.split certificate20_root1100 certificate20_root1101)

theorem certificate20_root110_checked :
    certificate20_root110.verify [6,13,14,16,17] {1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root1100_checked, certificate20_root1101_checked⟩

def certificate20_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 2) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 8)) (.split (.leaf 8) (.leaf 8)))))

theorem certificate20_root1110_checked :
    certificate20_root1110.verify [13,14,16,17] {3,1,0} = true := rfl

def certificate20_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 2) (.leaf 4)))) (.split (.split (.split (.leaf 2) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 2)) (.split (.leaf 2) (.leaf 2)))))

theorem certificate20_root1111_checked :
    certificate20_root1111.verify [13,14,16,17] {6,3,1,0} = true := rfl

def certificate20_root111 : OrbitCertificate :=
  (.split certificate20_root1110 certificate20_root1111)

theorem certificate20_root111_checked :
    certificate20_root111.verify [6,13,14,16,17] {3,1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root1110_checked, certificate20_root1111_checked⟩

def certificate20_root11 : OrbitCertificate :=
  (.split certificate20_root110 certificate20_root111)

theorem certificate20_root11_checked :
    certificate20_root11.verify [3,6,13,14,16,17] {1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root110_checked, certificate20_root111_checked⟩

def certificate20_root1 : OrbitCertificate :=
  (.split certificate20_root10 certificate20_root11)

theorem certificate20_root1_checked :
    certificate20_root1.verify [1,3,6,13,14,16,17] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root10_checked, certificate20_root11_checked⟩

def certificate20_root : OrbitCertificate :=
  (.split certificate20_root0 certificate20_root1)

theorem certificate20_root_checked :
    certificate20_root.verify [0,1,3,6,13,14,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate20_root0_checked, certificate20_root1_checked⟩

theorem covered_20 : ∀ C ∈ (box 20).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [0,1,3,6,13,14,16,17] ∅ certificate20_root
    certificate20_root_checked C
  have hs : C ⊆ ([0,1,3,6,13,14,16,17] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_20
