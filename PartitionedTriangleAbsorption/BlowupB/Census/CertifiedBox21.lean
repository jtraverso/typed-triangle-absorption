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

def certificate21_root0000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate21_root0000_checked :
    certificate21_root0000.verify [10,12,16,17] ∅ = true := rfl

def certificate21_root0001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 15) (.leaf 21)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate21_root0001_checked :
    certificate21_root0001.verify [10,12,16,17] {8} = true := rfl

def certificate21_root000 : OrbitCertificate :=
  (.split certificate21_root0000 certificate21_root0001)

theorem certificate21_root000_checked :
    certificate21_root000.verify [8,10,12,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root0000_checked, certificate21_root0001_checked⟩

def certificate21_root0010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate21_root0010_checked :
    certificate21_root0010.verify [10,12,16,17] {7} = true := rfl

def certificate21_root0011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 14) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate21_root0011_checked :
    certificate21_root0011.verify [10,12,16,17] {8,7} = true := rfl

def certificate21_root001 : OrbitCertificate :=
  (.split certificate21_root0010 certificate21_root0011)

theorem certificate21_root001_checked :
    certificate21_root001.verify [8,10,12,16,17] {7} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root0010_checked, certificate21_root0011_checked⟩

def certificate21_root00 : OrbitCertificate :=
  (.split certificate21_root000 certificate21_root001)

theorem certificate21_root00_checked :
    certificate21_root00.verify [7,8,10,12,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root000_checked, certificate21_root001_checked⟩

def certificate21_root0100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 11)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 18) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 18) (.leaf 18)))))

theorem certificate21_root0100_checked :
    certificate21_root0100.verify [10,12,16,17] {6} = true := rfl

def certificate21_root0101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 4) (.leaf 17))) (.split (.split (.leaf 9) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 1) (.leaf 21)) (.split (.leaf 12) (.leaf 20))) (.split (.split (.leaf 15) (.leaf 21)) (.split (.leaf 18) (.leaf 18)))))

theorem certificate21_root0101_checked :
    certificate21_root0101.verify [10,12,16,17] {8,6} = true := rfl

def certificate21_root010 : OrbitCertificate :=
  (.split certificate21_root0100 certificate21_root0101)

theorem certificate21_root010_checked :
    certificate21_root010.verify [8,10,12,16,17] {6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root0100_checked, certificate21_root0101_checked⟩

def certificate21_root0110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 12)) (.split (.leaf 12) (.leaf 12))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate21_root0110_checked :
    certificate21_root0110.verify [10,12,16,17] {7,6} = true := rfl

def certificate21_root0111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 5) (.leaf 4)) (.split (.leaf 4) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate21_root0111_checked :
    certificate21_root0111.verify [10,12,16,17] {8,7,6} = true := rfl

def certificate21_root011 : OrbitCertificate :=
  (.split certificate21_root0110 certificate21_root0111)

theorem certificate21_root011_checked :
    certificate21_root011.verify [8,10,12,16,17] {7,6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root0110_checked, certificate21_root0111_checked⟩

def certificate21_root01 : OrbitCertificate :=
  (.split certificate21_root010 certificate21_root011)

theorem certificate21_root01_checked :
    certificate21_root01.verify [7,8,10,12,16,17] {6} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root010_checked, certificate21_root011_checked⟩

def certificate21_root0 : OrbitCertificate :=
  (.split certificate21_root00 certificate21_root01)

theorem certificate21_root0_checked :
    certificate21_root0.verify [6,7,8,10,12,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root00_checked, certificate21_root01_checked⟩

def certificate21_root1000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate21_root1000_checked :
    certificate21_root1000.verify [10,12,16,17] {4} = true := rfl

def certificate21_root1001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 14)) (.split (.leaf 2) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 14) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate21_root1001_checked :
    certificate21_root1001.verify [10,12,16,17] {8,4} = true := rfl

def certificate21_root100 : OrbitCertificate :=
  (.split certificate21_root1000 certificate21_root1001)

theorem certificate21_root100_checked :
    certificate21_root100.verify [8,10,12,16,17] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root1000_checked, certificate21_root1001_checked⟩

def certificate21_root1010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 12) (.leaf 12)) (.split (.leaf 12) (.leaf 14)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 12) (.leaf 12)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate21_root1010_checked :
    certificate21_root1010.verify [10,12,16,17] {7,4} = true := rfl

def certificate21_root1011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 14)) (.split (.leaf 2) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 14) (.leaf 14)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 14) (.leaf 14)))))

theorem certificate21_root1011_checked :
    certificate21_root1011.verify [10,12,16,17] {8,7,4} = true := rfl

def certificate21_root101 : OrbitCertificate :=
  (.split certificate21_root1010 certificate21_root1011)

theorem certificate21_root101_checked :
    certificate21_root101.verify [8,10,12,16,17] {7,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root1010_checked, certificate21_root1011_checked⟩

def certificate21_root10 : OrbitCertificate :=
  (.split certificate21_root100 certificate21_root101)

theorem certificate21_root10_checked :
    certificate21_root10.verify [7,8,10,12,16,17] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root100_checked, certificate21_root101_checked⟩

def certificate21_root1100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate21_root1100_checked :
    certificate21_root1100.verify [10,12,16,17] {6,4} = true := rfl

def certificate21_root1101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 3) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 12) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate21_root1101_checked :
    certificate21_root1101.verify [10,12,16,17] {8,6,4} = true := rfl

def certificate21_root110 : OrbitCertificate :=
  (.split certificate21_root1100 certificate21_root1101)

theorem certificate21_root110_checked :
    certificate21_root110.verify [8,10,12,16,17] {6,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root1100_checked, certificate21_root1101_checked⟩

def certificate21_root1110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 12) (.leaf 12)) (.split (.leaf 12) (.leaf 12)))) (.split (.split (.split (.leaf 0) (.leaf 12)) (.split (.leaf 12) (.leaf 12))) (.split (.split (.leaf 12) (.leaf 12)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate21_root1110_checked :
    certificate21_root1110.verify [10,12,16,17] {7,6,4} = true := rfl

def certificate21_root1111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 12)) (.split (.leaf 12) (.leaf 14)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 12) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 12)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate21_root1111_checked :
    certificate21_root1111.verify [10,12,16,17] {8,7,6,4} = true := rfl

def certificate21_root111 : OrbitCertificate :=
  (.split certificate21_root1110 certificate21_root1111)

theorem certificate21_root111_checked :
    certificate21_root111.verify [8,10,12,16,17] {7,6,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root1110_checked, certificate21_root1111_checked⟩

def certificate21_root11 : OrbitCertificate :=
  (.split certificate21_root110 certificate21_root111)

theorem certificate21_root11_checked :
    certificate21_root11.verify [7,8,10,12,16,17] {6,4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root110_checked, certificate21_root111_checked⟩

def certificate21_root1 : OrbitCertificate :=
  (.split certificate21_root10 certificate21_root11)

theorem certificate21_root1_checked :
    certificate21_root1.verify [6,7,8,10,12,16,17] {4} = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root10_checked, certificate21_root11_checked⟩

def certificate21_root : OrbitCertificate :=
  (.split certificate21_root0 certificate21_root1)

theorem certificate21_root_checked :
    certificate21_root.verify [4,6,7,8,10,12,16,17] ∅ = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate21_root0_checked, certificate21_root1_checked⟩

theorem covered_21 : ∀ C ∈ (box 21).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.verify_sound [4,6,7,8,10,12,16,17] ∅ certificate21_root
    certificate21_root_checked C
  have hs : C ⊆ ([4,6,7,8,10,12,16,17] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [Finset.empty_union] using
    hh hs (by simpa only [Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_21
