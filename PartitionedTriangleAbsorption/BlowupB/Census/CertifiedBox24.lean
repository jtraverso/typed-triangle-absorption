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

def certificate24_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate24_root0000_checked :
    certificate24_root0000.verify [10,11,12,14] ∅ = true := rfl

def certificate24_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 9) (.leaf 23))) (.split (.split (.leaf 8) (.leaf 22)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 15) (.leaf 21))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate24_root0001_checked :
    certificate24_root0001.verify [10,11,12,14] {8} = true := rfl

def certificate24_root000 : OrbitCertificate :=
  (.split certificate24_root0000 certificate24_root0001)

theorem certificate24_root000_checked :
    certificate24_root000.verify [8,10,11,12,14] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root0000_checked, certificate24_root0001_checked⟩

def certificate24_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 0) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 7) (.leaf 7)))) (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 0) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 7) (.leaf 7)))))

theorem certificate24_root0010_checked :
    certificate24_root0010.verify [10,11,12,14] {3} = true := rfl

def certificate24_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate24_root0011_checked :
    certificate24_root0011.verify [10,11,12,14] {8,3} = true := rfl

def certificate24_root001 : OrbitCertificate :=
  (.split certificate24_root0010 certificate24_root0011)

theorem certificate24_root001_checked :
    certificate24_root001.verify [8,10,11,12,14] {3} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root0010_checked, certificate24_root0011_checked⟩

def certificate24_root00 : OrbitCertificate :=
  (.split certificate24_root000 certificate24_root001)

theorem certificate24_root00_checked :
    certificate24_root00.verify [3,8,10,11,12,14] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root000_checked, certificate24_root001_checked⟩

def certificate24_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 1) (.leaf 6))) (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate24_root0100_checked :
    certificate24_root0100.verify [10,11,12,14] {2} = true := rfl

def certificate24_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 8) (.leaf 8)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 1) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 14)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate24_root0101_checked :
    certificate24_root0101.verify [10,11,12,14] {8,2} = true := rfl

def certificate24_root010 : OrbitCertificate :=
  (.split certificate24_root0100 certificate24_root0101)

theorem certificate24_root010_checked :
    certificate24_root010.verify [8,10,11,12,14] {2} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root0100_checked, certificate24_root0101_checked⟩

def certificate24_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 1) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate24_root0110_checked :
    certificate24_root0110.verify [10,11,12,14] {3,2} = true := rfl

def certificate24_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 1) (.leaf 1))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 6)))))

theorem certificate24_root0111_checked :
    certificate24_root0111.verify [10,11,12,14] {8,3,2} = true := rfl

def certificate24_root011 : OrbitCertificate :=
  (.split certificate24_root0110 certificate24_root0111)

theorem certificate24_root011_checked :
    certificate24_root011.verify [8,10,11,12,14] {3,2} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root0110_checked, certificate24_root0111_checked⟩

def certificate24_root01 : OrbitCertificate :=
  (.split certificate24_root010 certificate24_root011)

theorem certificate24_root01_checked :
    certificate24_root01.verify [3,8,10,11,12,14] {2} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root010_checked, certificate24_root011_checked⟩

def certificate24_root0 : OrbitCertificate :=
  (.split certificate24_root00 certificate24_root01)

theorem certificate24_root0_checked :
    certificate24_root0.verify [2,3,8,10,11,12,14] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root00_checked, certificate24_root01_checked⟩

def certificate24_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 0) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 0) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate24_root1000_checked :
    certificate24_root1000.verify [10,11,12,14] {0} = true := rfl

def certificate24_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 8) (.leaf 8)) (.split (.leaf 0) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 1) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 0) (.leaf 6)))))

theorem certificate24_root1001_checked :
    certificate24_root1001.verify [10,11,12,14] {8,0} = true := rfl

def certificate24_root100 : OrbitCertificate :=
  (.split certificate24_root1000 certificate24_root1001)

theorem certificate24_root100_checked :
    certificate24_root100.verify [8,10,11,12,14] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root1000_checked, certificate24_root1001_checked⟩

def certificate24_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 0) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 7) (.leaf 7)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 7) (.leaf 7)))))

theorem certificate24_root1010_checked :
    certificate24_root1010.verify [10,11,12,14] {3,0} = true := rfl

def certificate24_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 7)))) (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 1) (.leaf 1))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 1) (.leaf 7)))))

theorem certificate24_root1011_checked :
    certificate24_root1011.verify [10,11,12,14] {8,3,0} = true := rfl

def certificate24_root101 : OrbitCertificate :=
  (.split certificate24_root1010 certificate24_root1011)

theorem certificate24_root101_checked :
    certificate24_root101.verify [8,10,11,12,14] {3,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root1010_checked, certificate24_root1011_checked⟩

def certificate24_root10 : OrbitCertificate :=
  (.split certificate24_root100 certificate24_root101)

theorem certificate24_root10_checked :
    certificate24_root10.verify [3,8,10,11,12,14] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root100_checked, certificate24_root101_checked⟩

def certificate24_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 1) (.leaf 6))) (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 1) (.leaf 6))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate24_root1100_checked :
    certificate24_root1100.verify [10,11,12,14] {2,0} = true := rfl

def certificate24_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 8) (.leaf 8)) (.split (.leaf 0) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 1) (.leaf 1))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 6)))))

theorem certificate24_root1101_checked :
    certificate24_root1101.verify [10,11,12,14] {8,2,0} = true := rfl

def certificate24_root110 : OrbitCertificate :=
  (.split certificate24_root1100 certificate24_root1101)

theorem certificate24_root110_checked :
    certificate24_root110.verify [8,10,11,12,14] {2,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root1100_checked, certificate24_root1101_checked⟩

def certificate24_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 1) (.leaf 7))) (.split (.split (.leaf 0) (.leaf 6)) (.split (.leaf 0) (.leaf 6)))))

theorem certificate24_root1110_checked :
    certificate24_root1110.verify [10,11,12,14] {3,2,0} = true := rfl

def certificate24_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 1) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 1) (.leaf 1))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate24_root1111_checked :
    certificate24_root1111.verify [10,11,12,14] {8,3,2,0} = true := rfl

def certificate24_root111 : OrbitCertificate :=
  (.split certificate24_root1110 certificate24_root1111)

theorem certificate24_root111_checked :
    certificate24_root111.verify [8,10,11,12,14] {3,2,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root1110_checked, certificate24_root1111_checked⟩

def certificate24_root11 : OrbitCertificate :=
  (.split certificate24_root110 certificate24_root111)

theorem certificate24_root11_checked :
    certificate24_root11.verify [3,8,10,11,12,14] {2,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root110_checked, certificate24_root111_checked⟩

def certificate24_root1 : OrbitCertificate :=
  (.split certificate24_root10 certificate24_root11)

theorem certificate24_root1_checked :
    certificate24_root1.verify [2,3,8,10,11,12,14] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root10_checked, certificate24_root11_checked⟩

def certificate24_root : OrbitCertificate :=
  (.split certificate24_root0 certificate24_root1)

theorem certificate24_root_checked :
    certificate24_root.verify [0,2,3,8,10,11,12,14] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate24_root0_checked, certificate24_root1_checked⟩

theorem covered_24 : ∀ C ∈ (box 24).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [0,2,3,8,10,11,12,14] ∅ certificate24_root
    certificate24_root_checked C
  have hs : C ⊆ ([0,2,3,8,10,11,12,14] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_24
