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

def certificate07_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate07_root0000_checked :
    certificate07_root0000.verify [14, 15, 18, 19] ∅ = true := rfl

def certificate07_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate07_root0001_checked :
    certificate07_root0001.verify [14, 15, 18, 19] {5} = true := rfl

def certificate07_root000 : OrbitCertificate :=
  (.split certificate07_root0000 certificate07_root0001)

theorem certificate07_root000_checked :
    certificate07_root000.verify [5, 14, 15, 18, 19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root0000_checked, certificate07_root0001_checked⟩

def certificate07_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate07_root0010_checked :
    certificate07_root0010.verify [14, 15, 18, 19] {2} = true := rfl

def certificate07_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate07_root0011_checked :
    certificate07_root0011.verify [14, 15, 18, 19] {5,2} = true := rfl

def certificate07_root001 : OrbitCertificate :=
  (.split certificate07_root0010 certificate07_root0011)

theorem certificate07_root001_checked :
    certificate07_root001.verify [5, 14, 15, 18, 19] {2} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root0010_checked, certificate07_root0011_checked⟩

def certificate07_root00 : OrbitCertificate :=
  (.split certificate07_root000 certificate07_root001)

theorem certificate07_root00_checked :
    certificate07_root00.verify [2, 5, 14, 15, 18, 19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root000_checked, certificate07_root001_checked⟩

def certificate07_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 5) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root0100_checked :
    certificate07_root0100.verify [14, 15, 18, 19] {1} = true := rfl

def certificate07_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))) (.split (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 8) (.leaf 19))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate07_root0101_checked :
    certificate07_root0101.verify [14, 15, 18, 19] {5,1} = true := rfl

def certificate07_root010 : OrbitCertificate :=
  (.split certificate07_root0100 certificate07_root0101)

theorem certificate07_root010_checked :
    certificate07_root010.verify [5, 14, 15, 18, 19] {1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root0100_checked, certificate07_root0101_checked⟩

def certificate07_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 3) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 8) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root0110_checked :
    certificate07_root0110.verify [14, 15, 18, 19] {2,1} = true := rfl

def certificate07_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 8) (.leaf 5))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 3) (.leaf 9)))))

theorem certificate07_root0111_checked :
    certificate07_root0111.verify [14, 15, 18, 19] {5,2,1} = true := rfl

def certificate07_root011 : OrbitCertificate :=
  (.split certificate07_root0110 certificate07_root0111)

theorem certificate07_root011_checked :
    certificate07_root011.verify [5, 14, 15, 18, 19] {2,1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root0110_checked, certificate07_root0111_checked⟩

def certificate07_root01 : OrbitCertificate :=
  (.split certificate07_root010 certificate07_root011)

theorem certificate07_root01_checked :
    certificate07_root01.verify [2, 5, 14, 15, 18, 19] {1} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root010_checked, certificate07_root011_checked⟩

def certificate07_root0 : OrbitCertificate :=
  (.split certificate07_root00 certificate07_root01)

theorem certificate07_root0_checked :
    certificate07_root0.verify [1, 2, 5, 14, 15, 18, 19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root00_checked, certificate07_root01_checked⟩

def certificate07_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root1000_checked :
    certificate07_root1000.verify [14, 15, 18, 19] {0} = true := rfl

def certificate07_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 10) (.leaf 5))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 10) (.leaf 11))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root1001_checked :
    certificate07_root1001.verify [14, 15, 18, 19] {5,0} = true := rfl

def certificate07_root100 : OrbitCertificate :=
  (.split certificate07_root1000 certificate07_root1001)

theorem certificate07_root100_checked :
    certificate07_root100.verify [5, 14, 15, 18, 19] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root1000_checked, certificate07_root1001_checked⟩

def certificate07_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 8) (.leaf 11)) (.split (.leaf 10) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate07_root1010_checked :
    certificate07_root1010.verify [14, 15, 18, 19] {2,0} = true := rfl

def certificate07_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 10) (.leaf 5))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 8) (.leaf 5)) (.split (.leaf 10) (.leaf 5))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate07_root1011_checked :
    certificate07_root1011.verify [14, 15, 18, 19] {5,2,0} = true := rfl

def certificate07_root101 : OrbitCertificate :=
  (.split certificate07_root1010 certificate07_root1011)

theorem certificate07_root101_checked :
    certificate07_root101.verify [5, 14, 15, 18, 19] {2,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root1010_checked, certificate07_root1011_checked⟩

def certificate07_root10 : OrbitCertificate :=
  (.split certificate07_root100 certificate07_root101)

theorem certificate07_root10_checked :
    certificate07_root10.verify [2, 5, 14, 15, 18, 19] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root100_checked, certificate07_root101_checked⟩

def certificate07_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root1100_checked :
    certificate07_root1100.verify [14, 15, 18, 19] {1,0} = true := rfl

def certificate07_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 8) (.leaf 5))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root1101_checked :
    certificate07_root1101.verify [14, 15, 18, 19] {5,1,0} = true := rfl

def certificate07_root110 : OrbitCertificate :=
  (.split certificate07_root1100 certificate07_root1101)

theorem certificate07_root110_checked :
    certificate07_root110.verify [5, 14, 15, 18, 19] {1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root1100_checked, certificate07_root1101_checked⟩

def certificate07_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 8) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate07_root1110_checked :
    certificate07_root1110.verify [14, 15, 18, 19] {2,1,0} = true := rfl

def certificate07_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 8) (.leaf 5))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 3) (.leaf 3)))))

theorem certificate07_root1111_checked :
    certificate07_root1111.verify [14, 15, 18, 19] {5,2,1,0} = true := rfl

def certificate07_root111 : OrbitCertificate :=
  (.split certificate07_root1110 certificate07_root1111)

theorem certificate07_root111_checked :
    certificate07_root111.verify [5, 14, 15, 18, 19] {2,1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root1110_checked, certificate07_root1111_checked⟩

def certificate07_root11 : OrbitCertificate :=
  (.split certificate07_root110 certificate07_root111)

theorem certificate07_root11_checked :
    certificate07_root11.verify [2, 5, 14, 15, 18, 19] {1,0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root110_checked, certificate07_root111_checked⟩

def certificate07_root1 : OrbitCertificate :=
  (.split certificate07_root10 certificate07_root11)

theorem certificate07_root1_checked :
    certificate07_root1.verify [1, 2, 5, 14, 15, 18, 19] {0} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root10_checked, certificate07_root11_checked⟩

def certificate07_root : OrbitCertificate :=
  (.split certificate07_root0 certificate07_root1)

theorem certificate07_root_checked :
    certificate07_root.verify [0, 1, 2, 5, 14, 15, 18, 19] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate07_root0_checked, certificate07_root1_checked⟩

theorem covered_07 : ∀ C ∈ (box 7).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [0, 1, 2, 5, 14, 15, 18, 19] ∅ certificate07_root
    certificate07_root_checked C
  have hs : C ⊆ ([0, 1, 2, 5, 14, 15, 18, 19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_07
