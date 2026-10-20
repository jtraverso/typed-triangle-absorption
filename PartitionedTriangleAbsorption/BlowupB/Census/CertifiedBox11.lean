/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.FastCertificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

def certificate11_root00000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000000_checked :
    certificate11_root00000000.fastVerify [13,15,16,19] [] = true := rfl

def certificate11_root00000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000001_checked :
    certificate11_root00000001.fastVerify [13,15,16,19] [12] = true := rfl

def certificate11_root0000000 : OrbitCertificate :=
  (.split certificate11_root00000000 certificate11_root00000001)

theorem certificate11_root0000000_checked :
    certificate11_root0000000.fastVerify [12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00000000_checked, certificate11_root00000001_checked⟩

def certificate11_root00000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000010_checked :
    certificate11_root00000010.fastVerify [13,15,16,19] [11] = true := rfl

def certificate11_root00000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000011_checked :
    certificate11_root00000011.fastVerify [13,15,16,19] [12,11] = true := rfl

def certificate11_root0000001 : OrbitCertificate :=
  (.split certificate11_root00000010 certificate11_root00000011)

theorem certificate11_root0000001_checked :
    certificate11_root0000001.fastVerify [12,13,15,16,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00000010_checked, certificate11_root00000011_checked⟩

def certificate11_root000000 : OrbitCertificate :=
  (.split certificate11_root0000000 certificate11_root0000001)

theorem certificate11_root000000_checked :
    certificate11_root000000.fastVerify [11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0000000_checked, certificate11_root0000001_checked⟩

def certificate11_root00000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000100_checked :
    certificate11_root00000100.fastVerify [13,15,16,19] [10] = true := rfl

def certificate11_root00000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000101_checked :
    certificate11_root00000101.fastVerify [13,15,16,19] [12,10] = true := rfl

def certificate11_root0000010 : OrbitCertificate :=
  (.split certificate11_root00000100 certificate11_root00000101)

theorem certificate11_root0000010_checked :
    certificate11_root0000010.fastVerify [12,13,15,16,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00000100_checked, certificate11_root00000101_checked⟩

def certificate11_root00000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000110_checked :
    certificate11_root00000110.fastVerify [13,15,16,19] [11,10] = true := rfl

def certificate11_root00000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root00000111_checked :
    certificate11_root00000111.fastVerify [13,15,16,19] [12,11,10] = true := rfl

def certificate11_root0000011 : OrbitCertificate :=
  (.split certificate11_root00000110 certificate11_root00000111)

theorem certificate11_root0000011_checked :
    certificate11_root0000011.fastVerify [12,13,15,16,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00000110_checked, certificate11_root00000111_checked⟩

def certificate11_root000001 : OrbitCertificate :=
  (.split certificate11_root0000010 certificate11_root0000011)

theorem certificate11_root000001_checked :
    certificate11_root000001.fastVerify [11,12,13,15,16,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0000010_checked, certificate11_root0000011_checked⟩

def certificate11_root00000 : OrbitCertificate :=
  (.split certificate11_root000000 certificate11_root000001)

theorem certificate11_root00000_checked :
    certificate11_root00000.fastVerify [10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root000000_checked, certificate11_root000001_checked⟩

def certificate11_root00001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 16) (.leaf 23)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00001000_checked :
    certificate11_root00001000.fastVerify [13,15,16,19] [9] = true := rfl

def certificate11_root00001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00001001_checked :
    certificate11_root00001001.fastVerify [13,15,16,19] [12,9] = true := rfl

def certificate11_root0000100 : OrbitCertificate :=
  (.split certificate11_root00001000 certificate11_root00001001)

theorem certificate11_root0000100_checked :
    certificate11_root0000100.fastVerify [12,13,15,16,19] [9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00001000_checked, certificate11_root00001001_checked⟩

def certificate11_root00001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00001010_checked :
    certificate11_root00001010.fastVerify [13,15,16,19] [11,9] = true := rfl

def certificate11_root00001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00001011_checked :
    certificate11_root00001011.fastVerify [13,15,16,19] [12,11,9] = true := rfl

def certificate11_root0000101 : OrbitCertificate :=
  (.split certificate11_root00001010 certificate11_root00001011)

theorem certificate11_root0000101_checked :
    certificate11_root0000101.fastVerify [12,13,15,16,19] [11,9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00001010_checked, certificate11_root00001011_checked⟩

def certificate11_root000010 : OrbitCertificate :=
  (.split certificate11_root0000100 certificate11_root0000101)

theorem certificate11_root000010_checked :
    certificate11_root000010.fastVerify [11,12,13,15,16,19] [9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0000100_checked, certificate11_root0000101_checked⟩

def certificate11_root00001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00001100_checked :
    certificate11_root00001100.fastVerify [13,15,16,19] [10,9] = true := rfl

def certificate11_root00001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00001101_checked :
    certificate11_root00001101.fastVerify [13,15,16,19] [12,10,9] = true := rfl

def certificate11_root0000110 : OrbitCertificate :=
  (.split certificate11_root00001100 certificate11_root00001101)

theorem certificate11_root0000110_checked :
    certificate11_root0000110.fastVerify [12,13,15,16,19] [10,9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00001100_checked, certificate11_root00001101_checked⟩

def certificate11_root00001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate11_root00001110_checked :
    certificate11_root00001110.fastVerify [13,15,16,19] [11,10,9] = true := rfl

def certificate11_root00001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 19) (.leaf 19)))))

theorem certificate11_root00001111_checked :
    certificate11_root00001111.fastVerify [13,15,16,19] [12,11,10,9] = true := rfl

def certificate11_root0000111 : OrbitCertificate :=
  (.split certificate11_root00001110 certificate11_root00001111)

theorem certificate11_root0000111_checked :
    certificate11_root0000111.fastVerify [12,13,15,16,19] [11,10,9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00001110_checked, certificate11_root00001111_checked⟩

def certificate11_root000011 : OrbitCertificate :=
  (.split certificate11_root0000110 certificate11_root0000111)

theorem certificate11_root000011_checked :
    certificate11_root000011.fastVerify [11,12,13,15,16,19] [10,9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0000110_checked, certificate11_root0000111_checked⟩

def certificate11_root00001 : OrbitCertificate :=
  (.split certificate11_root000010 certificate11_root000011)

theorem certificate11_root00001_checked :
    certificate11_root00001.fastVerify [10,11,12,13,15,16,19] [9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root000010_checked, certificate11_root000011_checked⟩

def certificate11_root0000 : OrbitCertificate :=
  (.split certificate11_root00000 certificate11_root00001)

theorem certificate11_root0000_checked :
    certificate11_root0000.fastVerify [9,10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00000_checked, certificate11_root00001_checked⟩

def certificate11_root00010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 22) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00010000_checked :
    certificate11_root00010000.fastVerify [13,15,16,19] [7] = true := rfl

def certificate11_root00010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 20) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 20) (.leaf 23)) (.split (.leaf 20) (.leaf 23))) (.split (.split (.leaf 12) (.leaf 23)) (.split (.leaf 12) (.leaf 23)))))

theorem certificate11_root00010001_checked :
    certificate11_root00010001.fastVerify [13,15,16,19] [12,7] = true := rfl

def certificate11_root0001000 : OrbitCertificate :=
  (.split certificate11_root00010000 certificate11_root00010001)

theorem certificate11_root0001000_checked :
    certificate11_root0001000.fastVerify [12,13,15,16,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00010000_checked, certificate11_root00010001_checked⟩

def certificate11_root00010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00010010_checked :
    certificate11_root00010010.fastVerify [13,15,16,19] [11,7] = true := rfl

def certificate11_root00010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root00010011_checked :
    certificate11_root00010011.fastVerify [13,15,16,19] [12,11,7] = true := rfl

def certificate11_root0001001 : OrbitCertificate :=
  (.split certificate11_root00010010 certificate11_root00010011)

theorem certificate11_root0001001_checked :
    certificate11_root0001001.fastVerify [12,13,15,16,19] [11,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00010010_checked, certificate11_root00010011_checked⟩

def certificate11_root000100 : OrbitCertificate :=
  (.split certificate11_root0001000 certificate11_root0001001)

theorem certificate11_root000100_checked :
    certificate11_root000100.fastVerify [11,12,13,15,16,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0001000_checked, certificate11_root0001001_checked⟩

def certificate11_root00010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root00010100_checked :
    certificate11_root00010100.fastVerify [13,15,16,19] [10,7] = true := rfl

def certificate11_root00010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate11_root00010101_checked :
    certificate11_root00010101.fastVerify [13,15,16,19] [12,10,7] = true := rfl

def certificate11_root0001010 : OrbitCertificate :=
  (.split certificate11_root00010100 certificate11_root00010101)

theorem certificate11_root0001010_checked :
    certificate11_root0001010.fastVerify [12,13,15,16,19] [10,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00010100_checked, certificate11_root00010101_checked⟩

def certificate11_root00010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root00010110_checked :
    certificate11_root00010110.fastVerify [13,15,16,19] [11,10,7] = true := rfl

def certificate11_root00010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate11_root00010111_checked :
    certificate11_root00010111.fastVerify [13,15,16,19] [12,11,10,7] = true := rfl

def certificate11_root0001011 : OrbitCertificate :=
  (.split certificate11_root00010110 certificate11_root00010111)

theorem certificate11_root0001011_checked :
    certificate11_root0001011.fastVerify [12,13,15,16,19] [11,10,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00010110_checked, certificate11_root00010111_checked⟩

def certificate11_root000101 : OrbitCertificate :=
  (.split certificate11_root0001010 certificate11_root0001011)

theorem certificate11_root000101_checked :
    certificate11_root000101.fastVerify [11,12,13,15,16,19] [10,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0001010_checked, certificate11_root0001011_checked⟩

def certificate11_root00010 : OrbitCertificate :=
  (.split certificate11_root000100 certificate11_root000101)

theorem certificate11_root00010_checked :
    certificate11_root00010.fastVerify [10,11,12,13,15,16,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root000100_checked, certificate11_root000101_checked⟩

def certificate11_root00011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root00011000_checked :
    certificate11_root00011000.fastVerify [13,15,16,19] [9,7] = true := rfl

def certificate11_root00011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00011001_checked :
    certificate11_root00011001.fastVerify [13,15,16,19] [12,9,7] = true := rfl

def certificate11_root0001100 : OrbitCertificate :=
  (.split certificate11_root00011000 certificate11_root00011001)

theorem certificate11_root0001100_checked :
    certificate11_root0001100.fastVerify [12,13,15,16,19] [9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00011000_checked, certificate11_root00011001_checked⟩

def certificate11_root00011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00011010_checked :
    certificate11_root00011010.fastVerify [13,15,16,19] [11,9,7] = true := rfl

def certificate11_root00011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 22) (.leaf 23)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00011011_checked :
    certificate11_root00011011.fastVerify [13,15,16,19] [12,11,9,7] = true := rfl

def certificate11_root0001101 : OrbitCertificate :=
  (.split certificate11_root00011010 certificate11_root00011011)

theorem certificate11_root0001101_checked :
    certificate11_root0001101.fastVerify [12,13,15,16,19] [11,9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00011010_checked, certificate11_root00011011_checked⟩

def certificate11_root000110 : OrbitCertificate :=
  (.split certificate11_root0001100 certificate11_root0001101)

theorem certificate11_root000110_checked :
    certificate11_root000110.fastVerify [11,12,13,15,16,19] [9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0001100_checked, certificate11_root0001101_checked⟩

def certificate11_root00011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00011100_checked :
    certificate11_root00011100.fastVerify [13,15,16,19] [10,9,7] = true := rfl

def certificate11_root00011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00011101_checked :
    certificate11_root00011101.fastVerify [13,15,16,19] [12,10,9,7] = true := rfl

def certificate11_root0001110 : OrbitCertificate :=
  (.split certificate11_root00011100 certificate11_root00011101)

theorem certificate11_root0001110_checked :
    certificate11_root0001110.fastVerify [12,13,15,16,19] [10,9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00011100_checked, certificate11_root00011101_checked⟩

def certificate11_root00011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00011110_checked :
    certificate11_root00011110.fastVerify [13,15,16,19] [11,10,9,7] = true := rfl

def certificate11_root00011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root00011111_checked :
    certificate11_root00011111.fastVerify [13,15,16,19] [12,11,10,9,7] = true := rfl

def certificate11_root0001111 : OrbitCertificate :=
  (.split certificate11_root00011110 certificate11_root00011111)

theorem certificate11_root0001111_checked :
    certificate11_root0001111.fastVerify [12,13,15,16,19] [11,10,9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00011110_checked, certificate11_root00011111_checked⟩

def certificate11_root000111 : OrbitCertificate :=
  (.split certificate11_root0001110 certificate11_root0001111)

theorem certificate11_root000111_checked :
    certificate11_root000111.fastVerify [11,12,13,15,16,19] [10,9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0001110_checked, certificate11_root0001111_checked⟩

def certificate11_root00011 : OrbitCertificate :=
  (.split certificate11_root000110 certificate11_root000111)

theorem certificate11_root00011_checked :
    certificate11_root00011.fastVerify [10,11,12,13,15,16,19] [9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root000110_checked, certificate11_root000111_checked⟩

def certificate11_root0001 : OrbitCertificate :=
  (.split certificate11_root00010 certificate11_root00011)

theorem certificate11_root0001_checked :
    certificate11_root0001.fastVerify [9,10,11,12,13,15,16,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00010_checked, certificate11_root00011_checked⟩

def certificate11_root000 : OrbitCertificate :=
  (.split certificate11_root0000 certificate11_root0001)

theorem certificate11_root000_checked :
    certificate11_root000.fastVerify [7,9,10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0000_checked, certificate11_root0001_checked⟩

def certificate11_root00100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 23)) (.split (.leaf 10) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100000_checked :
    certificate11_root00100000.fastVerify [13,15,16,19] [3] = true := rfl

def certificate11_root00100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100001_checked :
    certificate11_root00100001.fastVerify [13,15,16,19] [12,3] = true := rfl

def certificate11_root0010000 : OrbitCertificate :=
  (.split certificate11_root00100000 certificate11_root00100001)

theorem certificate11_root0010000_checked :
    certificate11_root0010000.fastVerify [12,13,15,16,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00100000_checked, certificate11_root00100001_checked⟩

def certificate11_root00100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100010_checked :
    certificate11_root00100010.fastVerify [13,15,16,19] [11,3] = true := rfl

def certificate11_root00100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100011_checked :
    certificate11_root00100011.fastVerify [13,15,16,19] [12,11,3] = true := rfl

def certificate11_root0010001 : OrbitCertificate :=
  (.split certificate11_root00100010 certificate11_root00100011)

theorem certificate11_root0010001_checked :
    certificate11_root0010001.fastVerify [12,13,15,16,19] [11,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00100010_checked, certificate11_root00100011_checked⟩

def certificate11_root001000 : OrbitCertificate :=
  (.split certificate11_root0010000 certificate11_root0010001)

theorem certificate11_root001000_checked :
    certificate11_root001000.fastVerify [11,12,13,15,16,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0010000_checked, certificate11_root0010001_checked⟩

def certificate11_root00100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100100_checked :
    certificate11_root00100100.fastVerify [13,15,16,19] [10,3] = true := rfl

def certificate11_root00100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00100101_checked :
    certificate11_root00100101.fastVerify [13,15,16,19] [12,10,3] = true := rfl

def certificate11_root0010010 : OrbitCertificate :=
  (.split certificate11_root00100100 certificate11_root00100101)

theorem certificate11_root0010010_checked :
    certificate11_root0010010.fastVerify [12,13,15,16,19] [10,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00100100_checked, certificate11_root00100101_checked⟩

def certificate11_root00100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21)))))

theorem certificate11_root00100110_checked :
    certificate11_root00100110.fastVerify [13,15,16,19] [11,10,3] = true := rfl

def certificate11_root00100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21)))))

theorem certificate11_root00100111_checked :
    certificate11_root00100111.fastVerify [13,15,16,19] [12,11,10,3] = true := rfl

def certificate11_root0010011 : OrbitCertificate :=
  (.split certificate11_root00100110 certificate11_root00100111)

theorem certificate11_root0010011_checked :
    certificate11_root0010011.fastVerify [12,13,15,16,19] [11,10,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00100110_checked, certificate11_root00100111_checked⟩

def certificate11_root001001 : OrbitCertificate :=
  (.split certificate11_root0010010 certificate11_root0010011)

theorem certificate11_root001001_checked :
    certificate11_root001001.fastVerify [11,12,13,15,16,19] [10,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0010010_checked, certificate11_root0010011_checked⟩

def certificate11_root00100 : OrbitCertificate :=
  (.split certificate11_root001000 certificate11_root001001)

theorem certificate11_root00100_checked :
    certificate11_root00100.fastVerify [10,11,12,13,15,16,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root001000_checked, certificate11_root001001_checked⟩

def certificate11_root00101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 23)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101000_checked :
    certificate11_root00101000.fastVerify [13,15,16,19] [9,3] = true := rfl

def certificate11_root00101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101001_checked :
    certificate11_root00101001.fastVerify [13,15,16,19] [12,9,3] = true := rfl

def certificate11_root0010100 : OrbitCertificate :=
  (.split certificate11_root00101000 certificate11_root00101001)

theorem certificate11_root0010100_checked :
    certificate11_root0010100.fastVerify [12,13,15,16,19] [9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00101000_checked, certificate11_root00101001_checked⟩

def certificate11_root00101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101010_checked :
    certificate11_root00101010.fastVerify [13,15,16,19] [11,9,3] = true := rfl

def certificate11_root00101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101011_checked :
    certificate11_root00101011.fastVerify [13,15,16,19] [12,11,9,3] = true := rfl

def certificate11_root0010101 : OrbitCertificate :=
  (.split certificate11_root00101010 certificate11_root00101011)

theorem certificate11_root0010101_checked :
    certificate11_root0010101.fastVerify [12,13,15,16,19] [11,9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00101010_checked, certificate11_root00101011_checked⟩

def certificate11_root001010 : OrbitCertificate :=
  (.split certificate11_root0010100 certificate11_root0010101)

theorem certificate11_root001010_checked :
    certificate11_root001010.fastVerify [11,12,13,15,16,19] [9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0010100_checked, certificate11_root0010101_checked⟩

def certificate11_root00101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101100_checked :
    certificate11_root00101100.fastVerify [13,15,16,19] [10,9,3] = true := rfl

def certificate11_root00101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00101101_checked :
    certificate11_root00101101.fastVerify [13,15,16,19] [12,10,9,3] = true := rfl

def certificate11_root0010110 : OrbitCertificate :=
  (.split certificate11_root00101100 certificate11_root00101101)

theorem certificate11_root0010110_checked :
    certificate11_root0010110.fastVerify [12,13,15,16,19] [10,9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00101100_checked, certificate11_root00101101_checked⟩

def certificate11_root00101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate11_root00101110_checked :
    certificate11_root00101110.fastVerify [13,15,16,19] [11,10,9,3] = true := rfl

def certificate11_root00101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate11_root00101111_checked :
    certificate11_root00101111.fastVerify [13,15,16,19] [12,11,10,9,3] = true := rfl

def certificate11_root0010111 : OrbitCertificate :=
  (.split certificate11_root00101110 certificate11_root00101111)

theorem certificate11_root0010111_checked :
    certificate11_root0010111.fastVerify [12,13,15,16,19] [11,10,9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00101110_checked, certificate11_root00101111_checked⟩

def certificate11_root001011 : OrbitCertificate :=
  (.split certificate11_root0010110 certificate11_root0010111)

theorem certificate11_root001011_checked :
    certificate11_root001011.fastVerify [11,12,13,15,16,19] [10,9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0010110_checked, certificate11_root0010111_checked⟩

def certificate11_root00101 : OrbitCertificate :=
  (.split certificate11_root001010 certificate11_root001011)

theorem certificate11_root00101_checked :
    certificate11_root00101.fastVerify [10,11,12,13,15,16,19] [9,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root001010_checked, certificate11_root001011_checked⟩

def certificate11_root0010 : OrbitCertificate :=
  (.split certificate11_root00100 certificate11_root00101)

theorem certificate11_root0010_checked :
    certificate11_root0010.fastVerify [9,10,11,12,13,15,16,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00100_checked, certificate11_root00101_checked⟩

def certificate11_root00110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 10) (.leaf 17)) (.split (.leaf 10) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root00110000_checked :
    certificate11_root00110000.fastVerify [13,15,16,19] [7,3] = true := rfl

def certificate11_root00110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00110001_checked :
    certificate11_root00110001.fastVerify [13,15,16,19] [12,7,3] = true := rfl

def certificate11_root0011000 : OrbitCertificate :=
  (.split certificate11_root00110000 certificate11_root00110001)

theorem certificate11_root0011000_checked :
    certificate11_root0011000.fastVerify [12,13,15,16,19] [7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00110000_checked, certificate11_root00110001_checked⟩

def certificate11_root00110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root00110010_checked :
    certificate11_root00110010.fastVerify [13,15,16,19] [11,7,3] = true := rfl

def certificate11_root00110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00110011_checked :
    certificate11_root00110011.fastVerify [13,15,16,19] [12,11,7,3] = true := rfl

def certificate11_root0011001 : OrbitCertificate :=
  (.split certificate11_root00110010 certificate11_root00110011)

theorem certificate11_root0011001_checked :
    certificate11_root0011001.fastVerify [12,13,15,16,19] [11,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00110010_checked, certificate11_root00110011_checked⟩

def certificate11_root001100 : OrbitCertificate :=
  (.split certificate11_root0011000 certificate11_root0011001)

theorem certificate11_root001100_checked :
    certificate11_root001100.fastVerify [11,12,13,15,16,19] [7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0011000_checked, certificate11_root0011001_checked⟩

def certificate11_root00110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00110100_checked :
    certificate11_root00110100.fastVerify [13,15,16,19] [10,7,3] = true := rfl

def certificate11_root00110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00110101_checked :
    certificate11_root00110101.fastVerify [13,15,16,19] [12,10,7,3] = true := rfl

def certificate11_root0011010 : OrbitCertificate :=
  (.split certificate11_root00110100 certificate11_root00110101)

theorem certificate11_root0011010_checked :
    certificate11_root0011010.fastVerify [12,13,15,16,19] [10,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00110100_checked, certificate11_root00110101_checked⟩

def certificate11_root00110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 8) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root00110110_checked :
    certificate11_root00110110.fastVerify [13,15,16,19] [11,10,7,3] = true := rfl

def certificate11_root00110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 6) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root00110111_checked :
    certificate11_root00110111.fastVerify [13,15,16,19] [12,11,10,7,3] = true := rfl

def certificate11_root0011011 : OrbitCertificate :=
  (.split certificate11_root00110110 certificate11_root00110111)

theorem certificate11_root0011011_checked :
    certificate11_root0011011.fastVerify [12,13,15,16,19] [11,10,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00110110_checked, certificate11_root00110111_checked⟩

def certificate11_root001101 : OrbitCertificate :=
  (.split certificate11_root0011010 certificate11_root0011011)

theorem certificate11_root001101_checked :
    certificate11_root001101.fastVerify [11,12,13,15,16,19] [10,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0011010_checked, certificate11_root0011011_checked⟩

def certificate11_root00110 : OrbitCertificate :=
  (.split certificate11_root001100 certificate11_root001101)

theorem certificate11_root00110_checked :
    certificate11_root00110.fastVerify [10,11,12,13,15,16,19] [7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root001100_checked, certificate11_root001101_checked⟩

def certificate11_root00111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 17)) (.split (.leaf 2) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root00111000_checked :
    certificate11_root00111000.fastVerify [13,15,16,19] [9,7,3] = true := rfl

def certificate11_root00111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root00111001_checked :
    certificate11_root00111001.fastVerify [13,15,16,19] [12,9,7,3] = true := rfl

def certificate11_root0011100 : OrbitCertificate :=
  (.split certificate11_root00111000 certificate11_root00111001)

theorem certificate11_root0011100_checked :
    certificate11_root0011100.fastVerify [12,13,15,16,19] [9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00111000_checked, certificate11_root00111001_checked⟩

def certificate11_root00111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 23)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root00111010_checked :
    certificate11_root00111010.fastVerify [13,15,16,19] [11,9,7,3] = true := rfl

def certificate11_root00111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00111011_checked :
    certificate11_root00111011.fastVerify [13,15,16,19] [12,11,9,7,3] = true := rfl

def certificate11_root0011101 : OrbitCertificate :=
  (.split certificate11_root00111010 certificate11_root00111011)

theorem certificate11_root0011101_checked :
    certificate11_root0011101.fastVerify [12,13,15,16,19] [11,9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00111010_checked, certificate11_root00111011_checked⟩

def certificate11_root001110 : OrbitCertificate :=
  (.split certificate11_root0011100 certificate11_root0011101)

theorem certificate11_root001110_checked :
    certificate11_root001110.fastVerify [11,12,13,15,16,19] [9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0011100_checked, certificate11_root0011101_checked⟩

def certificate11_root00111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00111100_checked :
    certificate11_root00111100.fastVerify [13,15,16,19] [10,9,7,3] = true := rfl

def certificate11_root00111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00111101_checked :
    certificate11_root00111101.fastVerify [13,15,16,19] [12,10,9,7,3] = true := rfl

def certificate11_root0011110 : OrbitCertificate :=
  (.split certificate11_root00111100 certificate11_root00111101)

theorem certificate11_root0011110_checked :
    certificate11_root0011110.fastVerify [12,13,15,16,19] [10,9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00111100_checked, certificate11_root00111101_checked⟩

def certificate11_root00111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00111110_checked :
    certificate11_root00111110.fastVerify [13,15,16,19] [11,10,9,7,3] = true := rfl

def certificate11_root00111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root00111111_checked :
    certificate11_root00111111.fastVerify [13,15,16,19] [12,11,10,9,7,3] = true := rfl

def certificate11_root0011111 : OrbitCertificate :=
  (.split certificate11_root00111110 certificate11_root00111111)

theorem certificate11_root0011111_checked :
    certificate11_root0011111.fastVerify [12,13,15,16,19] [11,10,9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00111110_checked, certificate11_root00111111_checked⟩

def certificate11_root001111 : OrbitCertificate :=
  (.split certificate11_root0011110 certificate11_root0011111)

theorem certificate11_root001111_checked :
    certificate11_root001111.fastVerify [11,12,13,15,16,19] [10,9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0011110_checked, certificate11_root0011111_checked⟩

def certificate11_root00111 : OrbitCertificate :=
  (.split certificate11_root001110 certificate11_root001111)

theorem certificate11_root00111_checked :
    certificate11_root00111.fastVerify [10,11,12,13,15,16,19] [9,7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root001110_checked, certificate11_root001111_checked⟩

def certificate11_root0011 : OrbitCertificate :=
  (.split certificate11_root00110 certificate11_root00111)

theorem certificate11_root0011_checked :
    certificate11_root0011.fastVerify [9,10,11,12,13,15,16,19] [7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00110_checked, certificate11_root00111_checked⟩

def certificate11_root001 : OrbitCertificate :=
  (.split certificate11_root0010 certificate11_root0011)

theorem certificate11_root001_checked :
    certificate11_root001.fastVerify [7,9,10,11,12,13,15,16,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0010_checked, certificate11_root0011_checked⟩

def certificate11_root00 : OrbitCertificate :=
  (.split certificate11_root000 certificate11_root001)

theorem certificate11_root00_checked :
    certificate11_root00.fastVerify [3,7,9,10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root000_checked, certificate11_root001_checked⟩

def certificate11_root01000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01000000_checked :
    certificate11_root01000000.fastVerify [13,15,16,19] [2] = true := rfl

def certificate11_root01000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 20) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root01000001_checked :
    certificate11_root01000001.fastVerify [13,15,16,19] [12,2] = true := rfl

def certificate11_root0100000 : OrbitCertificate :=
  (.split certificate11_root01000000 certificate11_root01000001)

theorem certificate11_root0100000_checked :
    certificate11_root0100000.fastVerify [12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01000000_checked, certificate11_root01000001_checked⟩

def certificate11_root01000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01000010_checked :
    certificate11_root01000010.fastVerify [13,15,16,19] [11,2] = true := rfl

def certificate11_root01000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root01000011_checked :
    certificate11_root01000011.fastVerify [13,15,16,19] [12,11,2] = true := rfl

def certificate11_root0100001 : OrbitCertificate :=
  (.split certificate11_root01000010 certificate11_root01000011)

theorem certificate11_root0100001_checked :
    certificate11_root0100001.fastVerify [12,13,15,16,19] [11,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01000010_checked, certificate11_root01000011_checked⟩

def certificate11_root010000 : OrbitCertificate :=
  (.split certificate11_root0100000 certificate11_root0100001)

theorem certificate11_root010000_checked :
    certificate11_root010000.fastVerify [11,12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0100000_checked, certificate11_root0100001_checked⟩

def certificate11_root01000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate11_root01000100_checked :
    certificate11_root01000100.fastVerify [13,15,16,19] [10,2] = true := rfl

def certificate11_root01000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20)))) (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate11_root01000101_checked :
    certificate11_root01000101.fastVerify [13,15,16,19] [12,10,2] = true := rfl

def certificate11_root0100010 : OrbitCertificate :=
  (.split certificate11_root01000100 certificate11_root01000101)

theorem certificate11_root0100010_checked :
    certificate11_root0100010.fastVerify [12,13,15,16,19] [10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01000100_checked, certificate11_root01000101_checked⟩

def certificate11_root01000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root01000110_checked :
    certificate11_root01000110.fastVerify [13,15,16,19] [11,10,2] = true := rfl

def certificate11_root01000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20)))) (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate11_root01000111_checked :
    certificate11_root01000111.fastVerify [13,15,16,19] [12,11,10,2] = true := rfl

def certificate11_root0100011 : OrbitCertificate :=
  (.split certificate11_root01000110 certificate11_root01000111)

theorem certificate11_root0100011_checked :
    certificate11_root0100011.fastVerify [12,13,15,16,19] [11,10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01000110_checked, certificate11_root01000111_checked⟩

def certificate11_root010001 : OrbitCertificate :=
  (.split certificate11_root0100010 certificate11_root0100011)

theorem certificate11_root010001_checked :
    certificate11_root010001.fastVerify [11,12,13,15,16,19] [10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0100010_checked, certificate11_root0100011_checked⟩

def certificate11_root01000 : OrbitCertificate :=
  (.split certificate11_root010000 certificate11_root010001)

theorem certificate11_root01000_checked :
    certificate11_root01000.fastVerify [10,11,12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root010000_checked, certificate11_root010001_checked⟩

def certificate11_root01001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01001000_checked :
    certificate11_root01001000.fastVerify [13,15,16,19] [9,2] = true := rfl

def certificate11_root01001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 22) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01001001_checked :
    certificate11_root01001001.fastVerify [13,15,16,19] [12,9,2] = true := rfl

def certificate11_root0100100 : OrbitCertificate :=
  (.split certificate11_root01001000 certificate11_root01001001)

theorem certificate11_root0100100_checked :
    certificate11_root0100100.fastVerify [12,13,15,16,19] [9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01001000_checked, certificate11_root01001001_checked⟩

def certificate11_root01001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001010_checked :
    certificate11_root01001010.fastVerify [13,15,16,19] [11,9,2] = true := rfl

def certificate11_root01001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001011_checked :
    certificate11_root01001011.fastVerify [13,15,16,19] [12,11,9,2] = true := rfl

def certificate11_root0100101 : OrbitCertificate :=
  (.split certificate11_root01001010 certificate11_root01001011)

theorem certificate11_root0100101_checked :
    certificate11_root0100101.fastVerify [12,13,15,16,19] [11,9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01001010_checked, certificate11_root01001011_checked⟩

def certificate11_root010010 : OrbitCertificate :=
  (.split certificate11_root0100100 certificate11_root0100101)

theorem certificate11_root010010_checked :
    certificate11_root010010.fastVerify [11,12,13,15,16,19] [9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0100100_checked, certificate11_root0100101_checked⟩

def certificate11_root01001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001100_checked :
    certificate11_root01001100.fastVerify [13,15,16,19] [10,9,2] = true := rfl

def certificate11_root01001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001101_checked :
    certificate11_root01001101.fastVerify [13,15,16,19] [12,10,9,2] = true := rfl

def certificate11_root0100110 : OrbitCertificate :=
  (.split certificate11_root01001100 certificate11_root01001101)

theorem certificate11_root0100110_checked :
    certificate11_root0100110.fastVerify [12,13,15,16,19] [10,9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01001100_checked, certificate11_root01001101_checked⟩

def certificate11_root01001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001110_checked :
    certificate11_root01001110.fastVerify [13,15,16,19] [11,10,9,2] = true := rfl

def certificate11_root01001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01001111_checked :
    certificate11_root01001111.fastVerify [13,15,16,19] [12,11,10,9,2] = true := rfl

def certificate11_root0100111 : OrbitCertificate :=
  (.split certificate11_root01001110 certificate11_root01001111)

theorem certificate11_root0100111_checked :
    certificate11_root0100111.fastVerify [12,13,15,16,19] [11,10,9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01001110_checked, certificate11_root01001111_checked⟩

def certificate11_root010011 : OrbitCertificate :=
  (.split certificate11_root0100110 certificate11_root0100111)

theorem certificate11_root010011_checked :
    certificate11_root010011.fastVerify [11,12,13,15,16,19] [10,9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0100110_checked, certificate11_root0100111_checked⟩

def certificate11_root01001 : OrbitCertificate :=
  (.split certificate11_root010010 certificate11_root010011)

theorem certificate11_root01001_checked :
    certificate11_root01001.fastVerify [10,11,12,13,15,16,19] [9,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root010010_checked, certificate11_root010011_checked⟩

def certificate11_root0100 : OrbitCertificate :=
  (.split certificate11_root01000 certificate11_root01001)

theorem certificate11_root0100_checked :
    certificate11_root0100.fastVerify [9,10,11,12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01000_checked, certificate11_root01001_checked⟩

def certificate11_root01010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01010000_checked :
    certificate11_root01010000.fastVerify [13,15,16,19] [7,2] = true := rfl

def certificate11_root01010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 20) (.leaf 17)))) (.split (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate11_root01010001_checked :
    certificate11_root01010001.fastVerify [13,15,16,19] [12,7,2] = true := rfl

def certificate11_root0101000 : OrbitCertificate :=
  (.split certificate11_root01010000 certificate11_root01010001)

theorem certificate11_root0101000_checked :
    certificate11_root0101000.fastVerify [12,13,15,16,19] [7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01010000_checked, certificate11_root01010001_checked⟩

def certificate11_root01010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01010010_checked :
    certificate11_root01010010.fastVerify [13,15,16,19] [11,7,2] = true := rfl

def certificate11_root01010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate11_root01010011_checked :
    certificate11_root01010011.fastVerify [13,15,16,19] [12,11,7,2] = true := rfl

def certificate11_root0101001 : OrbitCertificate :=
  (.split certificate11_root01010010 certificate11_root01010011)

theorem certificate11_root0101001_checked :
    certificate11_root0101001.fastVerify [12,13,15,16,19] [11,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01010010_checked, certificate11_root01010011_checked⟩

def certificate11_root010100 : OrbitCertificate :=
  (.split certificate11_root0101000 certificate11_root0101001)

theorem certificate11_root010100_checked :
    certificate11_root010100.fastVerify [11,12,13,15,16,19] [7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0101000_checked, certificate11_root0101001_checked⟩

def certificate11_root01010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate11_root01010100_checked :
    certificate11_root01010100.fastVerify [13,15,16,19] [10,7,2] = true := rfl

def certificate11_root01010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 20)))) (.split (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate11_root01010101_checked :
    certificate11_root01010101.fastVerify [13,15,16,19] [12,10,7,2] = true := rfl

def certificate11_root0101010 : OrbitCertificate :=
  (.split certificate11_root01010100 certificate11_root01010101)

theorem certificate11_root0101010_checked :
    certificate11_root0101010.fastVerify [12,13,15,16,19] [10,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01010100_checked, certificate11_root01010101_checked⟩

def certificate11_root01010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 0) (.leaf 20))) (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate11_root01010110_checked :
    certificate11_root01010110.fastVerify [13,15,16,19] [11,10,7,2] = true := rfl

def certificate11_root01010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20)))) (.split (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate11_root01010111_checked :
    certificate11_root01010111.fastVerify [13,15,16,19] [12,11,10,7,2] = true := rfl

def certificate11_root0101011 : OrbitCertificate :=
  (.split certificate11_root01010110 certificate11_root01010111)

theorem certificate11_root0101011_checked :
    certificate11_root0101011.fastVerify [12,13,15,16,19] [11,10,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01010110_checked, certificate11_root01010111_checked⟩

def certificate11_root010101 : OrbitCertificate :=
  (.split certificate11_root0101010 certificate11_root0101011)

theorem certificate11_root010101_checked :
    certificate11_root010101.fastVerify [11,12,13,15,16,19] [10,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0101010_checked, certificate11_root0101011_checked⟩

def certificate11_root01010 : OrbitCertificate :=
  (.split certificate11_root010100 certificate11_root010101)

theorem certificate11_root01010_checked :
    certificate11_root01010.fastVerify [10,11,12,13,15,16,19] [7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root010100_checked, certificate11_root010101_checked⟩

def certificate11_root01011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01011000_checked :
    certificate11_root01011000.fastVerify [13,15,16,19] [9,7,2] = true := rfl

def certificate11_root01011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 22) (.leaf 17)))))

theorem certificate11_root01011001_checked :
    certificate11_root01011001.fastVerify [13,15,16,19] [12,9,7,2] = true := rfl

def certificate11_root0101100 : OrbitCertificate :=
  (.split certificate11_root01011000 certificate11_root01011001)

theorem certificate11_root0101100_checked :
    certificate11_root0101100.fastVerify [12,13,15,16,19] [9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01011000_checked, certificate11_root01011001_checked⟩

def certificate11_root01011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01011010_checked :
    certificate11_root01011010.fastVerify [13,15,16,19] [11,9,7,2] = true := rfl

def certificate11_root01011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01011011_checked :
    certificate11_root01011011.fastVerify [13,15,16,19] [12,11,9,7,2] = true := rfl

def certificate11_root0101101 : OrbitCertificate :=
  (.split certificate11_root01011010 certificate11_root01011011)

theorem certificate11_root0101101_checked :
    certificate11_root0101101.fastVerify [12,13,15,16,19] [11,9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01011010_checked, certificate11_root01011011_checked⟩

def certificate11_root010110 : OrbitCertificate :=
  (.split certificate11_root0101100 certificate11_root0101101)

theorem certificate11_root010110_checked :
    certificate11_root010110.fastVerify [11,12,13,15,16,19] [9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0101100_checked, certificate11_root0101101_checked⟩

def certificate11_root01011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01011100_checked :
    certificate11_root01011100.fastVerify [13,15,16,19] [10,9,7,2] = true := rfl

def certificate11_root01011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01011101_checked :
    certificate11_root01011101.fastVerify [13,15,16,19] [12,10,9,7,2] = true := rfl

def certificate11_root0101110 : OrbitCertificate :=
  (.split certificate11_root01011100 certificate11_root01011101)

theorem certificate11_root0101110_checked :
    certificate11_root0101110.fastVerify [12,13,15,16,19] [10,9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01011100_checked, certificate11_root01011101_checked⟩

def certificate11_root01011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01011110_checked :
    certificate11_root01011110.fastVerify [13,15,16,19] [11,10,9,7,2] = true := rfl

def certificate11_root01011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01011111_checked :
    certificate11_root01011111.fastVerify [13,15,16,19] [12,11,10,9,7,2] = true := rfl

def certificate11_root0101111 : OrbitCertificate :=
  (.split certificate11_root01011110 certificate11_root01011111)

theorem certificate11_root0101111_checked :
    certificate11_root0101111.fastVerify [12,13,15,16,19] [11,10,9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01011110_checked, certificate11_root01011111_checked⟩

def certificate11_root010111 : OrbitCertificate :=
  (.split certificate11_root0101110 certificate11_root0101111)

theorem certificate11_root010111_checked :
    certificate11_root010111.fastVerify [11,12,13,15,16,19] [10,9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0101110_checked, certificate11_root0101111_checked⟩

def certificate11_root01011 : OrbitCertificate :=
  (.split certificate11_root010110 certificate11_root010111)

theorem certificate11_root01011_checked :
    certificate11_root01011.fastVerify [10,11,12,13,15,16,19] [9,7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root010110_checked, certificate11_root010111_checked⟩

def certificate11_root0101 : OrbitCertificate :=
  (.split certificate11_root01010 certificate11_root01011)

theorem certificate11_root0101_checked :
    certificate11_root0101.fastVerify [9,10,11,12,13,15,16,19] [7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01010_checked, certificate11_root01011_checked⟩

def certificate11_root010 : OrbitCertificate :=
  (.split certificate11_root0100 certificate11_root0101)

theorem certificate11_root010_checked :
    certificate11_root010.fastVerify [7,9,10,11,12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0100_checked, certificate11_root0101_checked⟩

def certificate11_root01100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01100000_checked :
    certificate11_root01100000.fastVerify [13,15,16,19] [3,2] = true := rfl

def certificate11_root01100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01100001_checked :
    certificate11_root01100001.fastVerify [13,15,16,19] [12,3,2] = true := rfl

def certificate11_root0110000 : OrbitCertificate :=
  (.split certificate11_root01100000 certificate11_root01100001)

theorem certificate11_root0110000_checked :
    certificate11_root0110000.fastVerify [12,13,15,16,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01100000_checked, certificate11_root01100001_checked⟩

def certificate11_root01100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01100010_checked :
    certificate11_root01100010.fastVerify [13,15,16,19] [11,3,2] = true := rfl

def certificate11_root01100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 23)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01100011_checked :
    certificate11_root01100011.fastVerify [13,15,16,19] [12,11,3,2] = true := rfl

def certificate11_root0110001 : OrbitCertificate :=
  (.split certificate11_root01100010 certificate11_root01100011)

theorem certificate11_root0110001_checked :
    certificate11_root0110001.fastVerify [12,13,15,16,19] [11,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01100010_checked, certificate11_root01100011_checked⟩

def certificate11_root011000 : OrbitCertificate :=
  (.split certificate11_root0110000 certificate11_root0110001)

theorem certificate11_root011000_checked :
    certificate11_root011000.fastVerify [11,12,13,15,16,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0110000_checked, certificate11_root0110001_checked⟩

def certificate11_root01100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01100100_checked :
    certificate11_root01100100.fastVerify [13,15,16,19] [10,3,2] = true := rfl

def certificate11_root01100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root01100101_checked :
    certificate11_root01100101.fastVerify [13,15,16,19] [12,10,3,2] = true := rfl

def certificate11_root0110010 : OrbitCertificate :=
  (.split certificate11_root01100100 certificate11_root01100101)

theorem certificate11_root0110010_checked :
    certificate11_root0110010.fastVerify [12,13,15,16,19] [10,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01100100_checked, certificate11_root01100101_checked⟩

def certificate11_root01100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 8) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01100110_checked :
    certificate11_root01100110.fastVerify [13,15,16,19] [11,10,3,2] = true := rfl

def certificate11_root01100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01100111_checked :
    certificate11_root01100111.fastVerify [13,15,16,19] [12,11,10,3,2] = true := rfl

def certificate11_root0110011 : OrbitCertificate :=
  (.split certificate11_root01100110 certificate11_root01100111)

theorem certificate11_root0110011_checked :
    certificate11_root0110011.fastVerify [12,13,15,16,19] [11,10,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01100110_checked, certificate11_root01100111_checked⟩

def certificate11_root011001 : OrbitCertificate :=
  (.split certificate11_root0110010 certificate11_root0110011)

theorem certificate11_root011001_checked :
    certificate11_root011001.fastVerify [11,12,13,15,16,19] [10,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0110010_checked, certificate11_root0110011_checked⟩

def certificate11_root01100 : OrbitCertificate :=
  (.split certificate11_root011000 certificate11_root011001)

theorem certificate11_root01100_checked :
    certificate11_root01100.fastVerify [10,11,12,13,15,16,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root011000_checked, certificate11_root011001_checked⟩

def certificate11_root01101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01101000_checked :
    certificate11_root01101000.fastVerify [13,15,16,19] [9,3,2] = true := rfl

def certificate11_root01101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01101001_checked :
    certificate11_root01101001.fastVerify [13,15,16,19] [12,9,3,2] = true := rfl

def certificate11_root0110100 : OrbitCertificate :=
  (.split certificate11_root01101000 certificate11_root01101001)

theorem certificate11_root0110100_checked :
    certificate11_root0110100.fastVerify [12,13,15,16,19] [9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01101000_checked, certificate11_root01101001_checked⟩

def certificate11_root01101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01101010_checked :
    certificate11_root01101010.fastVerify [13,15,16,19] [11,9,3,2] = true := rfl

def certificate11_root01101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root01101011_checked :
    certificate11_root01101011.fastVerify [13,15,16,19] [12,11,9,3,2] = true := rfl

def certificate11_root0110101 : OrbitCertificate :=
  (.split certificate11_root01101010 certificate11_root01101011)

theorem certificate11_root0110101_checked :
    certificate11_root0110101.fastVerify [12,13,15,16,19] [11,9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01101010_checked, certificate11_root01101011_checked⟩

def certificate11_root011010 : OrbitCertificate :=
  (.split certificate11_root0110100 certificate11_root0110101)

theorem certificate11_root011010_checked :
    certificate11_root011010.fastVerify [11,12,13,15,16,19] [9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0110100_checked, certificate11_root0110101_checked⟩

def certificate11_root01101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root01101100_checked :
    certificate11_root01101100.fastVerify [13,15,16,19] [10,9,3,2] = true := rfl

def certificate11_root01101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root01101101_checked :
    certificate11_root01101101.fastVerify [13,15,16,19] [12,10,9,3,2] = true := rfl

def certificate11_root0110110 : OrbitCertificate :=
  (.split certificate11_root01101100 certificate11_root01101101)

theorem certificate11_root0110110_checked :
    certificate11_root0110110.fastVerify [12,13,15,16,19] [10,9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01101100_checked, certificate11_root01101101_checked⟩

def certificate11_root01101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01101110_checked :
    certificate11_root01101110.fastVerify [13,15,16,19] [11,10,9,3,2] = true := rfl

def certificate11_root01101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root01101111_checked :
    certificate11_root01101111.fastVerify [13,15,16,19] [12,11,10,9,3,2] = true := rfl

def certificate11_root0110111 : OrbitCertificate :=
  (.split certificate11_root01101110 certificate11_root01101111)

theorem certificate11_root0110111_checked :
    certificate11_root0110111.fastVerify [12,13,15,16,19] [11,10,9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01101110_checked, certificate11_root01101111_checked⟩

def certificate11_root011011 : OrbitCertificate :=
  (.split certificate11_root0110110 certificate11_root0110111)

theorem certificate11_root011011_checked :
    certificate11_root011011.fastVerify [11,12,13,15,16,19] [10,9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0110110_checked, certificate11_root0110111_checked⟩

def certificate11_root01101 : OrbitCertificate :=
  (.split certificate11_root011010 certificate11_root011011)

theorem certificate11_root01101_checked :
    certificate11_root01101.fastVerify [10,11,12,13,15,16,19] [9,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root011010_checked, certificate11_root011011_checked⟩

def certificate11_root0110 : OrbitCertificate :=
  (.split certificate11_root01100 certificate11_root01101)

theorem certificate11_root0110_checked :
    certificate11_root0110.fastVerify [9,10,11,12,13,15,16,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01100_checked, certificate11_root01101_checked⟩

def certificate11_root01110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01110000_checked :
    certificate11_root01110000.fastVerify [13,15,16,19] [7,3,2] = true := rfl

def certificate11_root01110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01110001_checked :
    certificate11_root01110001.fastVerify [13,15,16,19] [12,7,3,2] = true := rfl

def certificate11_root0111000 : OrbitCertificate :=
  (.split certificate11_root01110000 certificate11_root01110001)

theorem certificate11_root0111000_checked :
    certificate11_root0111000.fastVerify [12,13,15,16,19] [7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01110000_checked, certificate11_root01110001_checked⟩

def certificate11_root01110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01110010_checked :
    certificate11_root01110010.fastVerify [13,15,16,19] [11,7,3,2] = true := rfl

def certificate11_root01110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 22) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01110011_checked :
    certificate11_root01110011.fastVerify [13,15,16,19] [12,11,7,3,2] = true := rfl

def certificate11_root0111001 : OrbitCertificate :=
  (.split certificate11_root01110010 certificate11_root01110011)

theorem certificate11_root0111001_checked :
    certificate11_root0111001.fastVerify [12,13,15,16,19] [11,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01110010_checked, certificate11_root01110011_checked⟩

def certificate11_root011100 : OrbitCertificate :=
  (.split certificate11_root0111000 certificate11_root0111001)

theorem certificate11_root011100_checked :
    certificate11_root011100.fastVerify [11,12,13,15,16,19] [7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0111000_checked, certificate11_root0111001_checked⟩

def certificate11_root01110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01110100_checked :
    certificate11_root01110100.fastVerify [13,15,16,19] [10,7,3,2] = true := rfl

def certificate11_root01110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root01110101_checked :
    certificate11_root01110101.fastVerify [13,15,16,19] [12,10,7,3,2] = true := rfl

def certificate11_root0111010 : OrbitCertificate :=
  (.split certificate11_root01110100 certificate11_root01110101)

theorem certificate11_root0111010_checked :
    certificate11_root0111010.fastVerify [12,13,15,16,19] [10,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01110100_checked, certificate11_root01110101_checked⟩

def certificate11_root01110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 8) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01110110_checked :
    certificate11_root01110110.fastVerify [13,15,16,19] [11,10,7,3,2] = true := rfl

def certificate11_root01110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 6) (.leaf 22)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01110111_checked :
    certificate11_root01110111.fastVerify [13,15,16,19] [12,11,10,7,3,2] = true := rfl

def certificate11_root0111011 : OrbitCertificate :=
  (.split certificate11_root01110110 certificate11_root01110111)

theorem certificate11_root0111011_checked :
    certificate11_root0111011.fastVerify [12,13,15,16,19] [11,10,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01110110_checked, certificate11_root01110111_checked⟩

def certificate11_root011101 : OrbitCertificate :=
  (.split certificate11_root0111010 certificate11_root0111011)

theorem certificate11_root011101_checked :
    certificate11_root011101.fastVerify [11,12,13,15,16,19] [10,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0111010_checked, certificate11_root0111011_checked⟩

def certificate11_root01110 : OrbitCertificate :=
  (.split certificate11_root011100 certificate11_root011101)

theorem certificate11_root01110_checked :
    certificate11_root01110.fastVerify [10,11,12,13,15,16,19] [7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root011100_checked, certificate11_root011101_checked⟩

def certificate11_root01111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01111000_checked :
    certificate11_root01111000.fastVerify [13,15,16,19] [9,7,3,2] = true := rfl

def certificate11_root01111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root01111001_checked :
    certificate11_root01111001.fastVerify [13,15,16,19] [12,9,7,3,2] = true := rfl

def certificate11_root0111100 : OrbitCertificate :=
  (.split certificate11_root01111000 certificate11_root01111001)

theorem certificate11_root0111100_checked :
    certificate11_root0111100.fastVerify [12,13,15,16,19] [9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01111000_checked, certificate11_root01111001_checked⟩

def certificate11_root01111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01111010_checked :
    certificate11_root01111010.fastVerify [13,15,16,19] [11,9,7,3,2] = true := rfl

def certificate11_root01111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root01111011_checked :
    certificate11_root01111011.fastVerify [13,15,16,19] [12,11,9,7,3,2] = true := rfl

def certificate11_root0111101 : OrbitCertificate :=
  (.split certificate11_root01111010 certificate11_root01111011)

theorem certificate11_root0111101_checked :
    certificate11_root0111101.fastVerify [12,13,15,16,19] [11,9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01111010_checked, certificate11_root01111011_checked⟩

def certificate11_root011110 : OrbitCertificate :=
  (.split certificate11_root0111100 certificate11_root0111101)

theorem certificate11_root011110_checked :
    certificate11_root011110.fastVerify [11,12,13,15,16,19] [9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0111100_checked, certificate11_root0111101_checked⟩

def certificate11_root01111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 0) (.leaf 23)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01111100_checked :
    certificate11_root01111100.fastVerify [13,15,16,19] [10,9,7,3,2] = true := rfl

def certificate11_root01111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate11_root01111101_checked :
    certificate11_root01111101.fastVerify [13,15,16,19] [12,10,9,7,3,2] = true := rfl

def certificate11_root0111110 : OrbitCertificate :=
  (.split certificate11_root01111100 certificate11_root01111101)

theorem certificate11_root0111110_checked :
    certificate11_root0111110.fastVerify [12,13,15,16,19] [10,9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01111100_checked, certificate11_root01111101_checked⟩

def certificate11_root01111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 22))) (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate11_root01111110_checked :
    certificate11_root01111110.fastVerify [13,15,16,19] [11,10,9,7,3,2] = true := rfl

def certificate11_root01111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root01111111_checked :
    certificate11_root01111111.fastVerify [13,15,16,19] [12,11,10,9,7,3,2] = true := rfl

def certificate11_root0111111 : OrbitCertificate :=
  (.split certificate11_root01111110 certificate11_root01111111)

theorem certificate11_root0111111_checked :
    certificate11_root0111111.fastVerify [12,13,15,16,19] [11,10,9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01111110_checked, certificate11_root01111111_checked⟩

def certificate11_root011111 : OrbitCertificate :=
  (.split certificate11_root0111110 certificate11_root0111111)

theorem certificate11_root011111_checked :
    certificate11_root011111.fastVerify [11,12,13,15,16,19] [10,9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0111110_checked, certificate11_root0111111_checked⟩

def certificate11_root01111 : OrbitCertificate :=
  (.split certificate11_root011110 certificate11_root011111)

theorem certificate11_root01111_checked :
    certificate11_root01111.fastVerify [10,11,12,13,15,16,19] [9,7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root011110_checked, certificate11_root011111_checked⟩

def certificate11_root0111 : OrbitCertificate :=
  (.split certificate11_root01110 certificate11_root01111)

theorem certificate11_root0111_checked :
    certificate11_root0111.fastVerify [9,10,11,12,13,15,16,19] [7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root01110_checked, certificate11_root01111_checked⟩

def certificate11_root011 : OrbitCertificate :=
  (.split certificate11_root0110 certificate11_root0111)

theorem certificate11_root011_checked :
    certificate11_root011.fastVerify [7,9,10,11,12,13,15,16,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0110_checked, certificate11_root0111_checked⟩

def certificate11_root01 : OrbitCertificate :=
  (.split certificate11_root010 certificate11_root011)

theorem certificate11_root01_checked :
    certificate11_root01.fastVerify [3,7,9,10,11,12,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root010_checked, certificate11_root011_checked⟩

def certificate11_root0 : OrbitCertificate :=
  (.split certificate11_root00 certificate11_root01)

theorem certificate11_root0_checked :
    certificate11_root0.fastVerify [2,3,7,9,10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root00_checked, certificate11_root01_checked⟩

def certificate11_root10000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10000000_checked :
    certificate11_root10000000.fastVerify [13,15,16,19] [0] = true := rfl

def certificate11_root10000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 17)))))

theorem certificate11_root10000001_checked :
    certificate11_root10000001.fastVerify [13,15,16,19] [12,0] = true := rfl

def certificate11_root1000000 : OrbitCertificate :=
  (.split certificate11_root10000000 certificate11_root10000001)

theorem certificate11_root1000000_checked :
    certificate11_root1000000.fastVerify [12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10000000_checked, certificate11_root10000001_checked⟩

def certificate11_root10000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10000010_checked :
    certificate11_root10000010.fastVerify [13,15,16,19] [11,0] = true := rfl

def certificate11_root10000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10000011_checked :
    certificate11_root10000011.fastVerify [13,15,16,19] [12,11,0] = true := rfl

def certificate11_root1000001 : OrbitCertificate :=
  (.split certificate11_root10000010 certificate11_root10000011)

theorem certificate11_root1000001_checked :
    certificate11_root1000001.fastVerify [12,13,15,16,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10000010_checked, certificate11_root10000011_checked⟩

def certificate11_root100000 : OrbitCertificate :=
  (.split certificate11_root1000000 certificate11_root1000001)

theorem certificate11_root100000_checked :
    certificate11_root100000.fastVerify [11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1000000_checked, certificate11_root1000001_checked⟩

def certificate11_root10000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate11_root10000100_checked :
    certificate11_root10000100.fastVerify [13,15,16,19] [10,0] = true := rfl

def certificate11_root10000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 13))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 13)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 19)))))

theorem certificate11_root10000101_checked :
    certificate11_root10000101.fastVerify [13,15,16,19] [12,10,0] = true := rfl

def certificate11_root1000010 : OrbitCertificate :=
  (.split certificate11_root10000100 certificate11_root10000101)

theorem certificate11_root1000010_checked :
    certificate11_root1000010.fastVerify [12,13,15,16,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10000100_checked, certificate11_root10000101_checked⟩

def certificate11_root10000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 12))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 12))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate11_root10000110_checked :
    certificate11_root10000110.fastVerify [13,15,16,19] [11,10,0] = true := rfl

def certificate11_root10000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 19)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate11_root10000111_checked :
    certificate11_root10000111.fastVerify [13,15,16,19] [12,11,10,0] = true := rfl

def certificate11_root1000011 : OrbitCertificate :=
  (.split certificate11_root10000110 certificate11_root10000111)

theorem certificate11_root1000011_checked :
    certificate11_root1000011.fastVerify [12,13,15,16,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10000110_checked, certificate11_root10000111_checked⟩

def certificate11_root100001 : OrbitCertificate :=
  (.split certificate11_root1000010 certificate11_root1000011)

theorem certificate11_root100001_checked :
    certificate11_root100001.fastVerify [11,12,13,15,16,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1000010_checked, certificate11_root1000011_checked⟩

def certificate11_root10000 : OrbitCertificate :=
  (.split certificate11_root100000 certificate11_root100001)

theorem certificate11_root10000_checked :
    certificate11_root10000.fastVerify [10,11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root100000_checked, certificate11_root100001_checked⟩

def certificate11_root10001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10001000_checked :
    certificate11_root10001000.fastVerify [13,15,16,19] [9,0] = true := rfl

def certificate11_root10001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10001001_checked :
    certificate11_root10001001.fastVerify [13,15,16,19] [12,9,0] = true := rfl

def certificate11_root1000100 : OrbitCertificate :=
  (.split certificate11_root10001000 certificate11_root10001001)

theorem certificate11_root1000100_checked :
    certificate11_root1000100.fastVerify [12,13,15,16,19] [9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10001000_checked, certificate11_root10001001_checked⟩

def certificate11_root10001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10001010_checked :
    certificate11_root10001010.fastVerify [13,15,16,19] [11,9,0] = true := rfl

def certificate11_root10001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 13)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10001011_checked :
    certificate11_root10001011.fastVerify [13,15,16,19] [12,11,9,0] = true := rfl

def certificate11_root1000101 : OrbitCertificate :=
  (.split certificate11_root10001010 certificate11_root10001011)

theorem certificate11_root1000101_checked :
    certificate11_root1000101.fastVerify [12,13,15,16,19] [11,9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10001010_checked, certificate11_root10001011_checked⟩

def certificate11_root100010 : OrbitCertificate :=
  (.split certificate11_root1000100 certificate11_root1000101)

theorem certificate11_root100010_checked :
    certificate11_root100010.fastVerify [11,12,13,15,16,19] [9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1000100_checked, certificate11_root1000101_checked⟩

def certificate11_root10001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10001100_checked :
    certificate11_root10001100.fastVerify [13,15,16,19] [10,9,0] = true := rfl

def certificate11_root10001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 15)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10001101_checked :
    certificate11_root10001101.fastVerify [13,15,16,19] [12,10,9,0] = true := rfl

def certificate11_root1000110 : OrbitCertificate :=
  (.split certificate11_root10001100 certificate11_root10001101)

theorem certificate11_root1000110_checked :
    certificate11_root1000110.fastVerify [12,13,15,16,19] [10,9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10001100_checked, certificate11_root10001101_checked⟩

def certificate11_root10001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 0) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 13)))))

theorem certificate11_root10001110_checked :
    certificate11_root10001110.fastVerify [13,15,16,19] [11,10,9,0] = true := rfl

def certificate11_root10001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 13)) (.split (.leaf 0) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 13)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 13)))))

theorem certificate11_root10001111_checked :
    certificate11_root10001111.fastVerify [13,15,16,19] [12,11,10,9,0] = true := rfl

def certificate11_root1000111 : OrbitCertificate :=
  (.split certificate11_root10001110 certificate11_root10001111)

theorem certificate11_root1000111_checked :
    certificate11_root1000111.fastVerify [12,13,15,16,19] [11,10,9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10001110_checked, certificate11_root10001111_checked⟩

def certificate11_root100011 : OrbitCertificate :=
  (.split certificate11_root1000110 certificate11_root1000111)

theorem certificate11_root100011_checked :
    certificate11_root100011.fastVerify [11,12,13,15,16,19] [10,9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1000110_checked, certificate11_root1000111_checked⟩

def certificate11_root10001 : OrbitCertificate :=
  (.split certificate11_root100010 certificate11_root100011)

theorem certificate11_root10001_checked :
    certificate11_root10001.fastVerify [10,11,12,13,15,16,19] [9,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root100010_checked, certificate11_root100011_checked⟩

def certificate11_root1000 : OrbitCertificate :=
  (.split certificate11_root10000 certificate11_root10001)

theorem certificate11_root1000_checked :
    certificate11_root1000.fastVerify [9,10,11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10000_checked, certificate11_root10001_checked⟩

def certificate11_root10010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10010000_checked :
    certificate11_root10010000.fastVerify [13,15,16,19] [7,0] = true := rfl

def certificate11_root10010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 12) (.leaf 17)))))

theorem certificate11_root10010001_checked :
    certificate11_root10010001.fastVerify [13,15,16,19] [12,7,0] = true := rfl

def certificate11_root1001000 : OrbitCertificate :=
  (.split certificate11_root10010000 certificate11_root10010001)

theorem certificate11_root1001000_checked :
    certificate11_root1001000.fastVerify [12,13,15,16,19] [7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10010000_checked, certificate11_root10010001_checked⟩

def certificate11_root10010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10010010_checked :
    certificate11_root10010010.fastVerify [13,15,16,19] [11,7,0] = true := rfl

def certificate11_root10010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 12) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root10010011_checked :
    certificate11_root10010011.fastVerify [13,15,16,19] [12,11,7,0] = true := rfl

def certificate11_root1001001 : OrbitCertificate :=
  (.split certificate11_root10010010 certificate11_root10010011)

theorem certificate11_root1001001_checked :
    certificate11_root1001001.fastVerify [12,13,15,16,19] [11,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10010010_checked, certificate11_root10010011_checked⟩

def certificate11_root100100 : OrbitCertificate :=
  (.split certificate11_root1001000 certificate11_root1001001)

theorem certificate11_root100100_checked :
    certificate11_root100100.fastVerify [11,12,13,15,16,19] [7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1001000_checked, certificate11_root1001001_checked⟩

def certificate11_root10010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root10010100_checked :
    certificate11_root10010100.fastVerify [13,15,16,19] [10,7,0] = true := rfl

def certificate11_root10010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 12) (.leaf 12))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 12)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate11_root10010101_checked :
    certificate11_root10010101.fastVerify [13,15,16,19] [12,10,7,0] = true := rfl

def certificate11_root1001010 : OrbitCertificate :=
  (.split certificate11_root10010100 certificate11_root10010101)

theorem certificate11_root1001010_checked :
    certificate11_root1001010.fastVerify [12,13,15,16,19] [10,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10010100_checked, certificate11_root10010101_checked⟩

def certificate11_root10010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root10010110_checked :
    certificate11_root10010110.fastVerify [13,15,16,19] [11,10,7,0] = true := rfl

def certificate11_root10010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 12) (.leaf 12))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 12)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 12))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate11_root10010111_checked :
    certificate11_root10010111.fastVerify [13,15,16,19] [12,11,10,7,0] = true := rfl

def certificate11_root1001011 : OrbitCertificate :=
  (.split certificate11_root10010110 certificate11_root10010111)

theorem certificate11_root1001011_checked :
    certificate11_root1001011.fastVerify [12,13,15,16,19] [11,10,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10010110_checked, certificate11_root10010111_checked⟩

def certificate11_root100101 : OrbitCertificate :=
  (.split certificate11_root1001010 certificate11_root1001011)

theorem certificate11_root100101_checked :
    certificate11_root100101.fastVerify [11,12,13,15,16,19] [10,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1001010_checked, certificate11_root1001011_checked⟩

def certificate11_root10010 : OrbitCertificate :=
  (.split certificate11_root100100 certificate11_root100101)

theorem certificate11_root10010_checked :
    certificate11_root10010.fastVerify [10,11,12,13,15,16,19] [7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root100100_checked, certificate11_root100101_checked⟩

def certificate11_root10011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10011000_checked :
    certificate11_root10011000.fastVerify [13,15,16,19] [9,7,0] = true := rfl

def certificate11_root10011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10011001_checked :
    certificate11_root10011001.fastVerify [13,15,16,19] [12,9,7,0] = true := rfl

def certificate11_root1001100 : OrbitCertificate :=
  (.split certificate11_root10011000 certificate11_root10011001)

theorem certificate11_root1001100_checked :
    certificate11_root1001100.fastVerify [12,13,15,16,19] [9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10011000_checked, certificate11_root10011001_checked⟩

def certificate11_root10011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10011010_checked :
    certificate11_root10011010.fastVerify [13,15,16,19] [11,9,7,0] = true := rfl

def certificate11_root10011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10011011_checked :
    certificate11_root10011011.fastVerify [13,15,16,19] [12,11,9,7,0] = true := rfl

def certificate11_root1001101 : OrbitCertificate :=
  (.split certificate11_root10011010 certificate11_root10011011)

theorem certificate11_root1001101_checked :
    certificate11_root1001101.fastVerify [12,13,15,16,19] [11,9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10011010_checked, certificate11_root10011011_checked⟩

def certificate11_root100110 : OrbitCertificate :=
  (.split certificate11_root1001100 certificate11_root1001101)

theorem certificate11_root100110_checked :
    certificate11_root100110.fastVerify [11,12,13,15,16,19] [9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1001100_checked, certificate11_root1001101_checked⟩

def certificate11_root10011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root10011100_checked :
    certificate11_root10011100.fastVerify [13,15,16,19] [10,9,7,0] = true := rfl

def certificate11_root10011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10011101_checked :
    certificate11_root10011101.fastVerify [13,15,16,19] [12,10,9,7,0] = true := rfl

def certificate11_root1001110 : OrbitCertificate :=
  (.split certificate11_root10011100 certificate11_root10011101)

theorem certificate11_root1001110_checked :
    certificate11_root1001110.fastVerify [12,13,15,16,19] [10,9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10011100_checked, certificate11_root10011101_checked⟩

def certificate11_root10011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root10011110_checked :
    certificate11_root10011110.fastVerify [13,15,16,19] [11,10,9,7,0] = true := rfl

def certificate11_root10011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root10011111_checked :
    certificate11_root10011111.fastVerify [13,15,16,19] [12,11,10,9,7,0] = true := rfl

def certificate11_root1001111 : OrbitCertificate :=
  (.split certificate11_root10011110 certificate11_root10011111)

theorem certificate11_root1001111_checked :
    certificate11_root1001111.fastVerify [12,13,15,16,19] [11,10,9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10011110_checked, certificate11_root10011111_checked⟩

def certificate11_root100111 : OrbitCertificate :=
  (.split certificate11_root1001110 certificate11_root1001111)

theorem certificate11_root100111_checked :
    certificate11_root100111.fastVerify [11,12,13,15,16,19] [10,9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1001110_checked, certificate11_root1001111_checked⟩

def certificate11_root10011 : OrbitCertificate :=
  (.split certificate11_root100110 certificate11_root100111)

theorem certificate11_root10011_checked :
    certificate11_root10011.fastVerify [10,11,12,13,15,16,19] [9,7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root100110_checked, certificate11_root100111_checked⟩

def certificate11_root1001 : OrbitCertificate :=
  (.split certificate11_root10010 certificate11_root10011)

theorem certificate11_root1001_checked :
    certificate11_root1001.fastVerify [9,10,11,12,13,15,16,19] [7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10010_checked, certificate11_root10011_checked⟩

def certificate11_root100 : OrbitCertificate :=
  (.split certificate11_root1000 certificate11_root1001)

theorem certificate11_root100_checked :
    certificate11_root100.fastVerify [7,9,10,11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1000_checked, certificate11_root1001_checked⟩

def certificate11_root10100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10100000_checked :
    certificate11_root10100000.fastVerify [13,15,16,19] [3,0] = true := rfl

def certificate11_root10100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10100001_checked :
    certificate11_root10100001.fastVerify [13,15,16,19] [12,3,0] = true := rfl

def certificate11_root1010000 : OrbitCertificate :=
  (.split certificate11_root10100000 certificate11_root10100001)

theorem certificate11_root1010000_checked :
    certificate11_root1010000.fastVerify [12,13,15,16,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10100000_checked, certificate11_root10100001_checked⟩

def certificate11_root10100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root10100010_checked :
    certificate11_root10100010.fastVerify [13,15,16,19] [11,3,0] = true := rfl

def certificate11_root10100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10100011_checked :
    certificate11_root10100011.fastVerify [13,15,16,19] [12,11,3,0] = true := rfl

def certificate11_root1010001 : OrbitCertificate :=
  (.split certificate11_root10100010 certificate11_root10100011)

theorem certificate11_root1010001_checked :
    certificate11_root1010001.fastVerify [12,13,15,16,19] [11,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10100010_checked, certificate11_root10100011_checked⟩

def certificate11_root101000 : OrbitCertificate :=
  (.split certificate11_root1010000 certificate11_root1010001)

theorem certificate11_root101000_checked :
    certificate11_root101000.fastVerify [11,12,13,15,16,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1010000_checked, certificate11_root1010001_checked⟩

def certificate11_root10100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 9)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10100100_checked :
    certificate11_root10100100.fastVerify [13,15,16,19] [10,3,0] = true := rfl

def certificate11_root10100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 15)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root10100101_checked :
    certificate11_root10100101.fastVerify [13,15,16,19] [12,10,3,0] = true := rfl

def certificate11_root1010010 : OrbitCertificate :=
  (.split certificate11_root10100100 certificate11_root10100101)

theorem certificate11_root1010010_checked :
    certificate11_root1010010.fastVerify [12,13,15,16,19] [10,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10100100_checked, certificate11_root10100101_checked⟩

def certificate11_root10100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root10100110_checked :
    certificate11_root10100110.fastVerify [13,15,16,19] [11,10,3,0] = true := rfl

def certificate11_root10100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root10100111_checked :
    certificate11_root10100111.fastVerify [13,15,16,19] [12,11,10,3,0] = true := rfl

def certificate11_root1010011 : OrbitCertificate :=
  (.split certificate11_root10100110 certificate11_root10100111)

theorem certificate11_root1010011_checked :
    certificate11_root1010011.fastVerify [12,13,15,16,19] [11,10,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10100110_checked, certificate11_root10100111_checked⟩

def certificate11_root101001 : OrbitCertificate :=
  (.split certificate11_root1010010 certificate11_root1010011)

theorem certificate11_root101001_checked :
    certificate11_root101001.fastVerify [11,12,13,15,16,19] [10,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1010010_checked, certificate11_root1010011_checked⟩

def certificate11_root10100 : OrbitCertificate :=
  (.split certificate11_root101000 certificate11_root101001)

theorem certificate11_root10100_checked :
    certificate11_root10100.fastVerify [10,11,12,13,15,16,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root101000_checked, certificate11_root101001_checked⟩

def certificate11_root10101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10101000_checked :
    certificate11_root10101000.fastVerify [13,15,16,19] [9,3,0] = true := rfl

def certificate11_root10101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10101001_checked :
    certificate11_root10101001.fastVerify [13,15,16,19] [12,9,3,0] = true := rfl

def certificate11_root1010100 : OrbitCertificate :=
  (.split certificate11_root10101000 certificate11_root10101001)

theorem certificate11_root1010100_checked :
    certificate11_root1010100.fastVerify [12,13,15,16,19] [9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10101000_checked, certificate11_root10101001_checked⟩

def certificate11_root10101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10101010_checked :
    certificate11_root10101010.fastVerify [13,15,16,19] [11,9,3,0] = true := rfl

def certificate11_root10101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10101011_checked :
    certificate11_root10101011.fastVerify [13,15,16,19] [12,11,9,3,0] = true := rfl

def certificate11_root1010101 : OrbitCertificate :=
  (.split certificate11_root10101010 certificate11_root10101011)

theorem certificate11_root1010101_checked :
    certificate11_root1010101.fastVerify [12,13,15,16,19] [11,9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10101010_checked, certificate11_root10101011_checked⟩

def certificate11_root101010 : OrbitCertificate :=
  (.split certificate11_root1010100 certificate11_root1010101)

theorem certificate11_root101010_checked :
    certificate11_root101010.fastVerify [11,12,13,15,16,19] [9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1010100_checked, certificate11_root1010101_checked⟩

def certificate11_root10101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10101100_checked :
    certificate11_root10101100.fastVerify [13,15,16,19] [10,9,3,0] = true := rfl

def certificate11_root10101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 9)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10101101_checked :
    certificate11_root10101101.fastVerify [13,15,16,19] [12,10,9,3,0] = true := rfl

def certificate11_root1010110 : OrbitCertificate :=
  (.split certificate11_root10101100 certificate11_root10101101)

theorem certificate11_root1010110_checked :
    certificate11_root1010110.fastVerify [12,13,15,16,19] [10,9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10101100_checked, certificate11_root10101101_checked⟩

def certificate11_root10101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 0) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 21)))))

theorem certificate11_root10101110_checked :
    certificate11_root10101110.fastVerify [13,15,16,19] [11,10,9,3,0] = true := rfl

def certificate11_root10101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 0) (.leaf 21))) (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 6) (.leaf 21)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 0) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 6) (.leaf 13)))))

theorem certificate11_root10101111_checked :
    certificate11_root10101111.fastVerify [13,15,16,19] [12,11,10,9,3,0] = true := rfl

def certificate11_root1010111 : OrbitCertificate :=
  (.split certificate11_root10101110 certificate11_root10101111)

theorem certificate11_root1010111_checked :
    certificate11_root1010111.fastVerify [12,13,15,16,19] [11,10,9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10101110_checked, certificate11_root10101111_checked⟩

def certificate11_root101011 : OrbitCertificate :=
  (.split certificate11_root1010110 certificate11_root1010111)

theorem certificate11_root101011_checked :
    certificate11_root101011.fastVerify [11,12,13,15,16,19] [10,9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1010110_checked, certificate11_root1010111_checked⟩

def certificate11_root10101 : OrbitCertificate :=
  (.split certificate11_root101010 certificate11_root101011)

theorem certificate11_root10101_checked :
    certificate11_root10101.fastVerify [10,11,12,13,15,16,19] [9,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root101010_checked, certificate11_root101011_checked⟩

def certificate11_root1010 : OrbitCertificate :=
  (.split certificate11_root10100 certificate11_root10101)

theorem certificate11_root1010_checked :
    certificate11_root1010.fastVerify [9,10,11,12,13,15,16,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10100_checked, certificate11_root10101_checked⟩

def certificate11_root10110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10110000_checked :
    certificate11_root10110000.fastVerify [13,15,16,19] [7,3,0] = true := rfl

def certificate11_root10110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10110001_checked :
    certificate11_root10110001.fastVerify [13,15,16,19] [12,7,3,0] = true := rfl

def certificate11_root1011000 : OrbitCertificate :=
  (.split certificate11_root10110000 certificate11_root10110001)

theorem certificate11_root1011000_checked :
    certificate11_root1011000.fastVerify [12,13,15,16,19] [7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10110000_checked, certificate11_root10110001_checked⟩

def certificate11_root10110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10110010_checked :
    certificate11_root10110010.fastVerify [13,15,16,19] [11,7,3,0] = true := rfl

def certificate11_root10110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10110011_checked :
    certificate11_root10110011.fastVerify [13,15,16,19] [12,11,7,3,0] = true := rfl

def certificate11_root1011001 : OrbitCertificate :=
  (.split certificate11_root10110010 certificate11_root10110011)

theorem certificate11_root1011001_checked :
    certificate11_root1011001.fastVerify [12,13,15,16,19] [11,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10110010_checked, certificate11_root10110011_checked⟩

def certificate11_root101100 : OrbitCertificate :=
  (.split certificate11_root1011000 certificate11_root1011001)

theorem certificate11_root101100_checked :
    certificate11_root101100.fastVerify [11,12,13,15,16,19] [7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1011000_checked, certificate11_root1011001_checked⟩

def certificate11_root10110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root10110100_checked :
    certificate11_root10110100.fastVerify [13,15,16,19] [10,7,3,0] = true := rfl

def certificate11_root10110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10110101_checked :
    certificate11_root10110101.fastVerify [13,15,16,19] [12,10,7,3,0] = true := rfl

def certificate11_root1011010 : OrbitCertificate :=
  (.split certificate11_root10110100 certificate11_root10110101)

theorem certificate11_root1011010_checked :
    certificate11_root1011010.fastVerify [12,13,15,16,19] [10,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10110100_checked, certificate11_root10110101_checked⟩

def certificate11_root10110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root10110110_checked :
    certificate11_root10110110.fastVerify [13,15,16,19] [11,10,7,3,0] = true := rfl

def certificate11_root10110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root10110111_checked :
    certificate11_root10110111.fastVerify [13,15,16,19] [12,11,10,7,3,0] = true := rfl

def certificate11_root1011011 : OrbitCertificate :=
  (.split certificate11_root10110110 certificate11_root10110111)

theorem certificate11_root1011011_checked :
    certificate11_root1011011.fastVerify [12,13,15,16,19] [11,10,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10110110_checked, certificate11_root10110111_checked⟩

def certificate11_root101101 : OrbitCertificate :=
  (.split certificate11_root1011010 certificate11_root1011011)

theorem certificate11_root101101_checked :
    certificate11_root101101.fastVerify [11,12,13,15,16,19] [10,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1011010_checked, certificate11_root1011011_checked⟩

def certificate11_root10110 : OrbitCertificate :=
  (.split certificate11_root101100 certificate11_root101101)

theorem certificate11_root10110_checked :
    certificate11_root10110.fastVerify [10,11,12,13,15,16,19] [7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root101100_checked, certificate11_root101101_checked⟩

def certificate11_root10111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10111000_checked :
    certificate11_root10111000.fastVerify [13,15,16,19] [9,7,3,0] = true := rfl

def certificate11_root10111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10111001_checked :
    certificate11_root10111001.fastVerify [13,15,16,19] [12,9,7,3,0] = true := rfl

def certificate11_root1011100 : OrbitCertificate :=
  (.split certificate11_root10111000 certificate11_root10111001)

theorem certificate11_root1011100_checked :
    certificate11_root1011100.fastVerify [12,13,15,16,19] [9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10111000_checked, certificate11_root10111001_checked⟩

def certificate11_root10111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root10111010_checked :
    certificate11_root10111010.fastVerify [13,15,16,19] [11,9,7,3,0] = true := rfl

def certificate11_root10111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root10111011_checked :
    certificate11_root10111011.fastVerify [13,15,16,19] [12,11,9,7,3,0] = true := rfl

def certificate11_root1011101 : OrbitCertificate :=
  (.split certificate11_root10111010 certificate11_root10111011)

theorem certificate11_root1011101_checked :
    certificate11_root1011101.fastVerify [12,13,15,16,19] [11,9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10111010_checked, certificate11_root10111011_checked⟩

def certificate11_root101110 : OrbitCertificate :=
  (.split certificate11_root1011100 certificate11_root1011101)

theorem certificate11_root101110_checked :
    certificate11_root101110.fastVerify [11,12,13,15,16,19] [9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1011100_checked, certificate11_root1011101_checked⟩

def certificate11_root10111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 5))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17)))))

theorem certificate11_root10111100_checked :
    certificate11_root10111100.fastVerify [13,15,16,19] [10,9,7,3,0] = true := rfl

def certificate11_root10111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17)))))

theorem certificate11_root10111101_checked :
    certificate11_root10111101.fastVerify [13,15,16,19] [12,10,9,7,3,0] = true := rfl

def certificate11_root1011110 : OrbitCertificate :=
  (.split certificate11_root10111100 certificate11_root10111101)

theorem certificate11_root1011110_checked :
    certificate11_root1011110.fastVerify [12,13,15,16,19] [10,9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10111100_checked, certificate11_root10111101_checked⟩

def certificate11_root10111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root10111110_checked :
    certificate11_root10111110.fastVerify [13,15,16,19] [11,10,9,7,3,0] = true := rfl

def certificate11_root10111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 23)))))

theorem certificate11_root10111111_checked :
    certificate11_root10111111.fastVerify [13,15,16,19] [12,11,10,9,7,3,0] = true := rfl

def certificate11_root1011111 : OrbitCertificate :=
  (.split certificate11_root10111110 certificate11_root10111111)

theorem certificate11_root1011111_checked :
    certificate11_root1011111.fastVerify [12,13,15,16,19] [11,10,9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10111110_checked, certificate11_root10111111_checked⟩

def certificate11_root101111 : OrbitCertificate :=
  (.split certificate11_root1011110 certificate11_root1011111)

theorem certificate11_root101111_checked :
    certificate11_root101111.fastVerify [11,12,13,15,16,19] [10,9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1011110_checked, certificate11_root1011111_checked⟩

def certificate11_root10111 : OrbitCertificate :=
  (.split certificate11_root101110 certificate11_root101111)

theorem certificate11_root10111_checked :
    certificate11_root10111.fastVerify [10,11,12,13,15,16,19] [9,7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root101110_checked, certificate11_root101111_checked⟩

def certificate11_root1011 : OrbitCertificate :=
  (.split certificate11_root10110 certificate11_root10111)

theorem certificate11_root1011_checked :
    certificate11_root1011.fastVerify [9,10,11,12,13,15,16,19] [7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10110_checked, certificate11_root10111_checked⟩

def certificate11_root101 : OrbitCertificate :=
  (.split certificate11_root1010 certificate11_root1011)

theorem certificate11_root101_checked :
    certificate11_root101.fastVerify [7,9,10,11,12,13,15,16,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1010_checked, certificate11_root1011_checked⟩

def certificate11_root10 : OrbitCertificate :=
  (.split certificate11_root100 certificate11_root101)

theorem certificate11_root10_checked :
    certificate11_root10.fastVerify [3,7,9,10,11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root100_checked, certificate11_root101_checked⟩

def certificate11_root11000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11000000_checked :
    certificate11_root11000000.fastVerify [13,15,16,19] [2,0] = true := rfl

def certificate11_root11000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 6) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11000001_checked :
    certificate11_root11000001.fastVerify [13,15,16,19] [12,2,0] = true := rfl

def certificate11_root1100000 : OrbitCertificate :=
  (.split certificate11_root11000000 certificate11_root11000001)

theorem certificate11_root1100000_checked :
    certificate11_root1100000.fastVerify [12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11000000_checked, certificate11_root11000001_checked⟩

def certificate11_root11000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11000010_checked :
    certificate11_root11000010.fastVerify [13,15,16,19] [11,2,0] = true := rfl

def certificate11_root11000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11000011_checked :
    certificate11_root11000011.fastVerify [13,15,16,19] [12,11,2,0] = true := rfl

def certificate11_root1100001 : OrbitCertificate :=
  (.split certificate11_root11000010 certificate11_root11000011)

theorem certificate11_root1100001_checked :
    certificate11_root1100001.fastVerify [12,13,15,16,19] [11,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11000010_checked, certificate11_root11000011_checked⟩

def certificate11_root110000 : OrbitCertificate :=
  (.split certificate11_root1100000 certificate11_root1100001)

theorem certificate11_root110000_checked :
    certificate11_root110000.fastVerify [11,12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1100000_checked, certificate11_root1100001_checked⟩

def certificate11_root11000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 2))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 6) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root11000100_checked :
    certificate11_root11000100.fastVerify [13,15,16,19] [10,2,0] = true := rfl

def certificate11_root11000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 1))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11000101_checked :
    certificate11_root11000101.fastVerify [13,15,16,19] [12,10,2,0] = true := rfl

def certificate11_root1100010 : OrbitCertificate :=
  (.split certificate11_root11000100 certificate11_root11000101)

theorem certificate11_root1100010_checked :
    certificate11_root1100010.fastVerify [12,13,15,16,19] [10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11000100_checked, certificate11_root11000101_checked⟩

def certificate11_root11000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11000110_checked :
    certificate11_root11000110.fastVerify [13,15,16,19] [11,10,2,0] = true := rfl

def certificate11_root11000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11000111_checked :
    certificate11_root11000111.fastVerify [13,15,16,19] [12,11,10,2,0] = true := rfl

def certificate11_root1100011 : OrbitCertificate :=
  (.split certificate11_root11000110 certificate11_root11000111)

theorem certificate11_root1100011_checked :
    certificate11_root1100011.fastVerify [12,13,15,16,19] [11,10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11000110_checked, certificate11_root11000111_checked⟩

def certificate11_root110001 : OrbitCertificate :=
  (.split certificate11_root1100010 certificate11_root1100011)

theorem certificate11_root110001_checked :
    certificate11_root110001.fastVerify [11,12,13,15,16,19] [10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1100010_checked, certificate11_root1100011_checked⟩

def certificate11_root11000 : OrbitCertificate :=
  (.split certificate11_root110000 certificate11_root110001)

theorem certificate11_root11000_checked :
    certificate11_root11000.fastVerify [10,11,12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root110000_checked, certificate11_root110001_checked⟩

def certificate11_root11001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11001000_checked :
    certificate11_root11001000.fastVerify [13,15,16,19] [9,2,0] = true := rfl

def certificate11_root11001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root11001001_checked :
    certificate11_root11001001.fastVerify [13,15,16,19] [12,9,2,0] = true := rfl

def certificate11_root1100100 : OrbitCertificate :=
  (.split certificate11_root11001000 certificate11_root11001001)

theorem certificate11_root1100100_checked :
    certificate11_root1100100.fastVerify [12,13,15,16,19] [9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11001000_checked, certificate11_root11001001_checked⟩

def certificate11_root11001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11001010_checked :
    certificate11_root11001010.fastVerify [13,15,16,19] [11,9,2,0] = true := rfl

def certificate11_root11001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11001011_checked :
    certificate11_root11001011.fastVerify [13,15,16,19] [12,11,9,2,0] = true := rfl

def certificate11_root1100101 : OrbitCertificate :=
  (.split certificate11_root11001010 certificate11_root11001011)

theorem certificate11_root1100101_checked :
    certificate11_root1100101.fastVerify [12,13,15,16,19] [11,9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11001010_checked, certificate11_root11001011_checked⟩

def certificate11_root110010 : OrbitCertificate :=
  (.split certificate11_root1100100 certificate11_root1100101)

theorem certificate11_root110010_checked :
    certificate11_root110010.fastVerify [11,12,13,15,16,19] [9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1100100_checked, certificate11_root1100101_checked⟩

def certificate11_root11001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 5))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11001100_checked :
    certificate11_root11001100.fastVerify [13,15,16,19] [10,9,2,0] = true := rfl

def certificate11_root11001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11001101_checked :
    certificate11_root11001101.fastVerify [13,15,16,19] [12,10,9,2,0] = true := rfl

def certificate11_root1100110 : OrbitCertificate :=
  (.split certificate11_root11001100 certificate11_root11001101)

theorem certificate11_root1100110_checked :
    certificate11_root1100110.fastVerify [12,13,15,16,19] [10,9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11001100_checked, certificate11_root11001101_checked⟩

def certificate11_root11001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root11001110_checked :
    certificate11_root11001110.fastVerify [13,15,16,19] [11,10,9,2,0] = true := rfl

def certificate11_root11001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))) (.split (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 0) (.leaf 7))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root11001111_checked :
    certificate11_root11001111.fastVerify [13,15,16,19] [12,11,10,9,2,0] = true := rfl

def certificate11_root1100111 : OrbitCertificate :=
  (.split certificate11_root11001110 certificate11_root11001111)

theorem certificate11_root1100111_checked :
    certificate11_root1100111.fastVerify [12,13,15,16,19] [11,10,9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11001110_checked, certificate11_root11001111_checked⟩

def certificate11_root110011 : OrbitCertificate :=
  (.split certificate11_root1100110 certificate11_root1100111)

theorem certificate11_root110011_checked :
    certificate11_root110011.fastVerify [11,12,13,15,16,19] [10,9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1100110_checked, certificate11_root1100111_checked⟩

def certificate11_root11001 : OrbitCertificate :=
  (.split certificate11_root110010 certificate11_root110011)

theorem certificate11_root11001_checked :
    certificate11_root11001.fastVerify [10,11,12,13,15,16,19] [9,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root110010_checked, certificate11_root110011_checked⟩

def certificate11_root1100 : OrbitCertificate :=
  (.split certificate11_root11000 certificate11_root11001)

theorem certificate11_root1100_checked :
    certificate11_root1100.fastVerify [9,10,11,12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11000_checked, certificate11_root11001_checked⟩

def certificate11_root11010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11010000_checked :
    certificate11_root11010000.fastVerify [13,15,16,19] [7,2,0] = true := rfl

def certificate11_root11010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 14) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 12) (.leaf 17)))))

theorem certificate11_root11010001_checked :
    certificate11_root11010001.fastVerify [13,15,16,19] [12,7,2,0] = true := rfl

def certificate11_root1101000 : OrbitCertificate :=
  (.split certificate11_root11010000 certificate11_root11010001)

theorem certificate11_root1101000_checked :
    certificate11_root1101000.fastVerify [12,13,15,16,19] [7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11010000_checked, certificate11_root11010001_checked⟩

def certificate11_root11010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11010010_checked :
    certificate11_root11010010.fastVerify [13,15,16,19] [11,7,2,0] = true := rfl

def certificate11_root11010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 16)))) (.split (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate11_root11010011_checked :
    certificate11_root11010011.fastVerify [13,15,16,19] [12,11,7,2,0] = true := rfl

def certificate11_root1101001 : OrbitCertificate :=
  (.split certificate11_root11010010 certificate11_root11010011)

theorem certificate11_root1101001_checked :
    certificate11_root1101001.fastVerify [12,13,15,16,19] [11,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11010010_checked, certificate11_root11010011_checked⟩

def certificate11_root110100 : OrbitCertificate :=
  (.split certificate11_root1101000 certificate11_root1101001)

theorem certificate11_root110100_checked :
    certificate11_root110100.fastVerify [11,12,13,15,16,19] [7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1101000_checked, certificate11_root1101001_checked⟩

def certificate11_root11010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root11010100_checked :
    certificate11_root11010100.fastVerify [13,15,16,19] [10,7,2,0] = true := rfl

def certificate11_root11010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 1)))) (.split (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate11_root11010101_checked :
    certificate11_root11010101.fastVerify [13,15,16,19] [12,10,7,2,0] = true := rfl

def certificate11_root1101010 : OrbitCertificate :=
  (.split certificate11_root11010100 certificate11_root11010101)

theorem certificate11_root1101010_checked :
    certificate11_root1101010.fastVerify [12,13,15,16,19] [10,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11010100_checked, certificate11_root11010101_checked⟩

def certificate11_root11010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 22)))))

theorem certificate11_root11010110_checked :
    certificate11_root11010110.fastVerify [13,15,16,19] [11,10,7,2,0] = true := rfl

def certificate11_root11010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 12) (.leaf 12)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 12)))))

theorem certificate11_root11010111_checked :
    certificate11_root11010111.fastVerify [13,15,16,19] [12,11,10,7,2,0] = true := rfl

def certificate11_root1101011 : OrbitCertificate :=
  (.split certificate11_root11010110 certificate11_root11010111)

theorem certificate11_root1101011_checked :
    certificate11_root1101011.fastVerify [12,13,15,16,19] [11,10,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11010110_checked, certificate11_root11010111_checked⟩

def certificate11_root110101 : OrbitCertificate :=
  (.split certificate11_root1101010 certificate11_root1101011)

theorem certificate11_root110101_checked :
    certificate11_root110101.fastVerify [11,12,13,15,16,19] [10,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1101010_checked, certificate11_root1101011_checked⟩

def certificate11_root11010 : OrbitCertificate :=
  (.split certificate11_root110100 certificate11_root110101)

theorem certificate11_root11010_checked :
    certificate11_root11010.fastVerify [10,11,12,13,15,16,19] [7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root110100_checked, certificate11_root110101_checked⟩

def certificate11_root11011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 2) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11011000_checked :
    certificate11_root11011000.fastVerify [13,15,16,19] [9,7,2,0] = true := rfl

def certificate11_root11011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root11011001_checked :
    certificate11_root11011001.fastVerify [13,15,16,19] [12,9,7,2,0] = true := rfl

def certificate11_root1101100 : OrbitCertificate :=
  (.split certificate11_root11011000 certificate11_root11011001)

theorem certificate11_root1101100_checked :
    certificate11_root1101100.fastVerify [12,13,15,16,19] [9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11011000_checked, certificate11_root11011001_checked⟩

def certificate11_root11011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11011010_checked :
    certificate11_root11011010.fastVerify [13,15,16,19] [11,9,7,2,0] = true := rfl

def certificate11_root11011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11011011_checked :
    certificate11_root11011011.fastVerify [13,15,16,19] [12,11,9,7,2,0] = true := rfl

def certificate11_root1101101 : OrbitCertificate :=
  (.split certificate11_root11011010 certificate11_root11011011)

theorem certificate11_root1101101_checked :
    certificate11_root1101101.fastVerify [12,13,15,16,19] [11,9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11011010_checked, certificate11_root11011011_checked⟩

def certificate11_root110110 : OrbitCertificate :=
  (.split certificate11_root1101100 certificate11_root1101101)

theorem certificate11_root110110_checked :
    certificate11_root110110.fastVerify [11,12,13,15,16,19] [9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1101100_checked, certificate11_root1101101_checked⟩

def certificate11_root11011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root11011100_checked :
    certificate11_root11011100.fastVerify [13,15,16,19] [10,9,7,2,0] = true := rfl

def certificate11_root11011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11011101_checked :
    certificate11_root11011101.fastVerify [13,15,16,19] [12,10,9,7,2,0] = true := rfl

def certificate11_root1101110 : OrbitCertificate :=
  (.split certificate11_root11011100 certificate11_root11011101)

theorem certificate11_root1101110_checked :
    certificate11_root1101110.fastVerify [12,13,15,16,19] [10,9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11011100_checked, certificate11_root11011101_checked⟩

def certificate11_root11011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root11011110_checked :
    certificate11_root11011110.fastVerify [13,15,16,19] [11,10,9,7,2,0] = true := rfl

def certificate11_root11011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 22)))))

theorem certificate11_root11011111_checked :
    certificate11_root11011111.fastVerify [13,15,16,19] [12,11,10,9,7,2,0] = true := rfl

def certificate11_root1101111 : OrbitCertificate :=
  (.split certificate11_root11011110 certificate11_root11011111)

theorem certificate11_root1101111_checked :
    certificate11_root1101111.fastVerify [12,13,15,16,19] [11,10,9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11011110_checked, certificate11_root11011111_checked⟩

def certificate11_root110111 : OrbitCertificate :=
  (.split certificate11_root1101110 certificate11_root1101111)

theorem certificate11_root110111_checked :
    certificate11_root110111.fastVerify [11,12,13,15,16,19] [10,9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1101110_checked, certificate11_root1101111_checked⟩

def certificate11_root11011 : OrbitCertificate :=
  (.split certificate11_root110110 certificate11_root110111)

theorem certificate11_root11011_checked :
    certificate11_root11011.fastVerify [10,11,12,13,15,16,19] [9,7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root110110_checked, certificate11_root110111_checked⟩

def certificate11_root1101 : OrbitCertificate :=
  (.split certificate11_root11010 certificate11_root11011)

theorem certificate11_root1101_checked :
    certificate11_root1101.fastVerify [9,10,11,12,13,15,16,19] [7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11010_checked, certificate11_root11011_checked⟩

def certificate11_root110 : OrbitCertificate :=
  (.split certificate11_root1100 certificate11_root1101)

theorem certificate11_root110_checked :
    certificate11_root110.fastVerify [7,9,10,11,12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1100_checked, certificate11_root1101_checked⟩

def certificate11_root11100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11100000_checked :
    certificate11_root11100000.fastVerify [13,15,16,19] [3,2,0] = true := rfl

def certificate11_root11100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11100001_checked :
    certificate11_root11100001.fastVerify [13,15,16,19] [12,3,2,0] = true := rfl

def certificate11_root1110000 : OrbitCertificate :=
  (.split certificate11_root11100000 certificate11_root11100001)

theorem certificate11_root1110000_checked :
    certificate11_root1110000.fastVerify [12,13,15,16,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11100000_checked, certificate11_root11100001_checked⟩

def certificate11_root11100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11100010_checked :
    certificate11_root11100010.fastVerify [13,15,16,19] [11,3,2,0] = true := rfl

def certificate11_root11100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11100011_checked :
    certificate11_root11100011.fastVerify [13,15,16,19] [12,11,3,2,0] = true := rfl

def certificate11_root1110001 : OrbitCertificate :=
  (.split certificate11_root11100010 certificate11_root11100011)

theorem certificate11_root1110001_checked :
    certificate11_root1110001.fastVerify [12,13,15,16,19] [11,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11100010_checked, certificate11_root11100011_checked⟩

def certificate11_root111000 : OrbitCertificate :=
  (.split certificate11_root1110000 certificate11_root1110001)

theorem certificate11_root111000_checked :
    certificate11_root111000.fastVerify [11,12,13,15,16,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1110000_checked, certificate11_root1110001_checked⟩

def certificate11_root11100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 6) (.leaf 3)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11100100_checked :
    certificate11_root11100100.fastVerify [13,15,16,19] [10,3,2,0] = true := rfl

def certificate11_root11100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root11100101_checked :
    certificate11_root11100101.fastVerify [13,15,16,19] [12,10,3,2,0] = true := rfl

def certificate11_root1110010 : OrbitCertificate :=
  (.split certificate11_root11100100 certificate11_root11100101)

theorem certificate11_root1110010_checked :
    certificate11_root1110010.fastVerify [12,13,15,16,19] [10,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11100100_checked, certificate11_root11100101_checked⟩

def certificate11_root11100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11100110_checked :
    certificate11_root11100110.fastVerify [13,15,16,19] [11,10,3,2,0] = true := rfl

def certificate11_root11100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11100111_checked :
    certificate11_root11100111.fastVerify [13,15,16,19] [12,11,10,3,2,0] = true := rfl

def certificate11_root1110011 : OrbitCertificate :=
  (.split certificate11_root11100110 certificate11_root11100111)

theorem certificate11_root1110011_checked :
    certificate11_root1110011.fastVerify [12,13,15,16,19] [11,10,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11100110_checked, certificate11_root11100111_checked⟩

def certificate11_root111001 : OrbitCertificate :=
  (.split certificate11_root1110010 certificate11_root1110011)

theorem certificate11_root111001_checked :
    certificate11_root111001.fastVerify [11,12,13,15,16,19] [10,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1110010_checked, certificate11_root1110011_checked⟩

def certificate11_root11100 : OrbitCertificate :=
  (.split certificate11_root111000 certificate11_root111001)

theorem certificate11_root11100_checked :
    certificate11_root11100.fastVerify [10,11,12,13,15,16,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root111000_checked, certificate11_root111001_checked⟩

def certificate11_root11101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root11101000_checked :
    certificate11_root11101000.fastVerify [13,15,16,19] [9,3,2,0] = true := rfl

def certificate11_root11101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 7) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root11101001_checked :
    certificate11_root11101001.fastVerify [13,15,16,19] [12,9,3,2,0] = true := rfl

def certificate11_root1110100 : OrbitCertificate :=
  (.split certificate11_root11101000 certificate11_root11101001)

theorem certificate11_root1110100_checked :
    certificate11_root1110100.fastVerify [12,13,15,16,19] [9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11101000_checked, certificate11_root11101001_checked⟩

def certificate11_root11101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11101010_checked :
    certificate11_root11101010.fastVerify [13,15,16,19] [11,9,3,2,0] = true := rfl

def certificate11_root11101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11101011_checked :
    certificate11_root11101011.fastVerify [13,15,16,19] [12,11,9,3,2,0] = true := rfl

def certificate11_root1110101 : OrbitCertificate :=
  (.split certificate11_root11101010 certificate11_root11101011)

theorem certificate11_root1110101_checked :
    certificate11_root1110101.fastVerify [12,13,15,16,19] [11,9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11101010_checked, certificate11_root11101011_checked⟩

def certificate11_root111010 : OrbitCertificate :=
  (.split certificate11_root1110100 certificate11_root1110101)

theorem certificate11_root111010_checked :
    certificate11_root111010.fastVerify [11,12,13,15,16,19] [9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1110100_checked, certificate11_root1110101_checked⟩

def certificate11_root11101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 2) (.leaf 5))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11101100_checked :
    certificate11_root11101100.fastVerify [13,15,16,19] [10,9,3,2,0] = true := rfl

def certificate11_root11101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11101101_checked :
    certificate11_root11101101.fastVerify [13,15,16,19] [12,10,9,3,2,0] = true := rfl

def certificate11_root1110110 : OrbitCertificate :=
  (.split certificate11_root11101100 certificate11_root11101101)

theorem certificate11_root1110110_checked :
    certificate11_root1110110.fastVerify [12,13,15,16,19] [10,9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11101100_checked, certificate11_root11101101_checked⟩

def certificate11_root11101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root11101110_checked :
    certificate11_root11101110.fastVerify [13,15,16,19] [11,10,9,3,2,0] = true := rfl

def certificate11_root11101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 7) (.leaf 7)) (.split (.leaf 6) (.leaf 7)))))

theorem certificate11_root11101111_checked :
    certificate11_root11101111.fastVerify [13,15,16,19] [12,11,10,9,3,2,0] = true := rfl

def certificate11_root1110111 : OrbitCertificate :=
  (.split certificate11_root11101110 certificate11_root11101111)

theorem certificate11_root1110111_checked :
    certificate11_root1110111.fastVerify [12,13,15,16,19] [11,10,9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11101110_checked, certificate11_root11101111_checked⟩

def certificate11_root111011 : OrbitCertificate :=
  (.split certificate11_root1110110 certificate11_root1110111)

theorem certificate11_root111011_checked :
    certificate11_root111011.fastVerify [11,12,13,15,16,19] [10,9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1110110_checked, certificate11_root1110111_checked⟩

def certificate11_root11101 : OrbitCertificate :=
  (.split certificate11_root111010 certificate11_root111011)

theorem certificate11_root11101_checked :
    certificate11_root11101.fastVerify [10,11,12,13,15,16,19] [9,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root111010_checked, certificate11_root111011_checked⟩

def certificate11_root1110 : OrbitCertificate :=
  (.split certificate11_root11100 certificate11_root11101)

theorem certificate11_root1110_checked :
    certificate11_root1110.fastVerify [9,10,11,12,13,15,16,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11100_checked, certificate11_root11101_checked⟩

def certificate11_root11110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11110000_checked :
    certificate11_root11110000.fastVerify [13,15,16,19] [7,3,2,0] = true := rfl

def certificate11_root11110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 6) (.leaf 17)) (.split (.leaf 6) (.leaf 17)))))

theorem certificate11_root11110001_checked :
    certificate11_root11110001.fastVerify [13,15,16,19] [12,7,3,2,0] = true := rfl

def certificate11_root1111000 : OrbitCertificate :=
  (.split certificate11_root11110000 certificate11_root11110001)

theorem certificate11_root1111000_checked :
    certificate11_root1111000.fastVerify [12,13,15,16,19] [7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11110000_checked, certificate11_root11110001_checked⟩

def certificate11_root11110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 10) (.leaf 10)) (.split (.leaf 10) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11110010_checked :
    certificate11_root11110010.fastVerify [13,15,16,19] [11,7,3,2,0] = true := rfl

def certificate11_root11110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11110011_checked :
    certificate11_root11110011.fastVerify [13,15,16,19] [12,11,7,3,2,0] = true := rfl

def certificate11_root1111001 : OrbitCertificate :=
  (.split certificate11_root11110010 certificate11_root11110011)

theorem certificate11_root1111001_checked :
    certificate11_root1111001.fastVerify [12,13,15,16,19] [11,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11110010_checked, certificate11_root11110011_checked⟩

def certificate11_root111100 : OrbitCertificate :=
  (.split certificate11_root1111000 certificate11_root1111001)

theorem certificate11_root111100_checked :
    certificate11_root111100.fastVerify [11,12,13,15,16,19] [7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1111000_checked, certificate11_root1111001_checked⟩

def certificate11_root11110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11110100_checked :
    certificate11_root11110100.fastVerify [13,15,16,19] [10,7,3,2,0] = true := rfl

def certificate11_root11110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 6) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11110101_checked :
    certificate11_root11110101.fastVerify [13,15,16,19] [12,10,7,3,2,0] = true := rfl

def certificate11_root1111010 : OrbitCertificate :=
  (.split certificate11_root11110100 certificate11_root11110101)

theorem certificate11_root1111010_checked :
    certificate11_root1111010.fastVerify [12,13,15,16,19] [10,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11110100_checked, certificate11_root11110101_checked⟩

def certificate11_root11110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate11_root11110110_checked :
    certificate11_root11110110.fastVerify [13,15,16,19] [11,10,7,3,2,0] = true := rfl

def certificate11_root11110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 6) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 6)))))

theorem certificate11_root11110111_checked :
    certificate11_root11110111.fastVerify [13,15,16,19] [12,11,10,7,3,2,0] = true := rfl

def certificate11_root1111011 : OrbitCertificate :=
  (.split certificate11_root11110110 certificate11_root11110111)

theorem certificate11_root1111011_checked :
    certificate11_root1111011.fastVerify [12,13,15,16,19] [11,10,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11110110_checked, certificate11_root11110111_checked⟩

def certificate11_root111101 : OrbitCertificate :=
  (.split certificate11_root1111010 certificate11_root1111011)

theorem certificate11_root111101_checked :
    certificate11_root111101.fastVerify [11,12,13,15,16,19] [10,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1111010_checked, certificate11_root1111011_checked⟩

def certificate11_root11110 : OrbitCertificate :=
  (.split certificate11_root111100 certificate11_root111101)

theorem certificate11_root11110_checked :
    certificate11_root11110.fastVerify [10,11,12,13,15,16,19] [7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root111100_checked, certificate11_root111101_checked⟩

def certificate11_root11111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11111000_checked :
    certificate11_root11111000.fastVerify [13,15,16,19] [9,7,3,2,0] = true := rfl

def certificate11_root11111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 11))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 17)) (.split (.leaf 0) (.leaf 17))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate11_root11111001_checked :
    certificate11_root11111001.fastVerify [13,15,16,19] [12,9,7,3,2,0] = true := rfl

def certificate11_root1111100 : OrbitCertificate :=
  (.split certificate11_root11111000 certificate11_root11111001)

theorem certificate11_root1111100_checked :
    certificate11_root1111100.fastVerify [12,13,15,16,19] [9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11111000_checked, certificate11_root11111001_checked⟩

def certificate11_root11111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 2) (.leaf 10)) (.split (.leaf 2) (.leaf 10))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate11_root11111010_checked :
    certificate11_root11111010.fastVerify [13,15,16,19] [11,9,7,3,2,0] = true := rfl

def certificate11_root11111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root11111011_checked :
    certificate11_root11111011.fastVerify [13,15,16,19] [12,11,9,7,3,2,0] = true := rfl

def certificate11_root1111101 : OrbitCertificate :=
  (.split certificate11_root11111010 certificate11_root11111011)

theorem certificate11_root1111101_checked :
    certificate11_root1111101.fastVerify [12,13,15,16,19] [11,9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11111010_checked, certificate11_root11111011_checked⟩

def certificate11_root111110 : OrbitCertificate :=
  (.split certificate11_root1111100 certificate11_root1111101)

theorem certificate11_root111110_checked :
    certificate11_root111110.fastVerify [11,12,13,15,16,19] [9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1111100_checked, certificate11_root1111101_checked⟩

def certificate11_root11111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 2) (.leaf 4))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root11111100_checked :
    certificate11_root11111100.fastVerify [13,15,16,19] [10,9,7,3,2,0] = true := rfl

def certificate11_root11111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1))) (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 0) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 17)))))

theorem certificate11_root11111101_checked :
    certificate11_root11111101.fastVerify [13,15,16,19] [12,10,9,7,3,2,0] = true := rfl

def certificate11_root1111110 : OrbitCertificate :=
  (.split certificate11_root11111100 certificate11_root11111101)

theorem certificate11_root1111110_checked :
    certificate11_root1111110.fastVerify [12,13,15,16,19] [10,9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11111100_checked, certificate11_root11111101_checked⟩

def certificate11_root11111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 16)))))

theorem certificate11_root11111110_checked :
    certificate11_root11111110.fastVerify [13,15,16,19] [11,10,9,7,3,2,0] = true := rfl

def certificate11_root11111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 0) (.leaf 1)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate11_root11111111_checked :
    certificate11_root11111111.fastVerify [13,15,16,19] [12,11,10,9,7,3,2,0] = true := rfl

def certificate11_root1111111 : OrbitCertificate :=
  (.split certificate11_root11111110 certificate11_root11111111)

theorem certificate11_root1111111_checked :
    certificate11_root1111111.fastVerify [12,13,15,16,19] [11,10,9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11111110_checked, certificate11_root11111111_checked⟩

def certificate11_root111111 : OrbitCertificate :=
  (.split certificate11_root1111110 certificate11_root1111111)

theorem certificate11_root111111_checked :
    certificate11_root111111.fastVerify [11,12,13,15,16,19] [10,9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1111110_checked, certificate11_root1111111_checked⟩

def certificate11_root11111 : OrbitCertificate :=
  (.split certificate11_root111110 certificate11_root111111)

theorem certificate11_root11111_checked :
    certificate11_root11111.fastVerify [10,11,12,13,15,16,19] [9,7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root111110_checked, certificate11_root111111_checked⟩

def certificate11_root1111 : OrbitCertificate :=
  (.split certificate11_root11110 certificate11_root11111)

theorem certificate11_root1111_checked :
    certificate11_root1111.fastVerify [9,10,11,12,13,15,16,19] [7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root11110_checked, certificate11_root11111_checked⟩

def certificate11_root111 : OrbitCertificate :=
  (.split certificate11_root1110 certificate11_root1111)

theorem certificate11_root111_checked :
    certificate11_root111.fastVerify [7,9,10,11,12,13,15,16,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root1110_checked, certificate11_root1111_checked⟩

def certificate11_root11 : OrbitCertificate :=
  (.split certificate11_root110 certificate11_root111)

theorem certificate11_root11_checked :
    certificate11_root11.fastVerify [3,7,9,10,11,12,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root110_checked, certificate11_root111_checked⟩

def certificate11_root1 : OrbitCertificate :=
  (.split certificate11_root10 certificate11_root11)

theorem certificate11_root1_checked :
    certificate11_root1.fastVerify [2,3,7,9,10,11,12,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root10_checked, certificate11_root11_checked⟩

def certificate11_root : OrbitCertificate :=
  (.split certificate11_root0 certificate11_root1)

theorem certificate11_root_checked :
    certificate11_root.fastVerify [0,2,3,7,9,10,11,12,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate11_root0_checked, certificate11_root1_checked⟩

theorem covered_11 : ∀ C ∈ (box 11).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,2,3,7,9,10,11,12,13,15,16,19] [] certificate11_root
    certificate11_root_checked C
  have hs : C ⊆ ([0,2,3,7,9,10,11,12,13,15,16,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_11
