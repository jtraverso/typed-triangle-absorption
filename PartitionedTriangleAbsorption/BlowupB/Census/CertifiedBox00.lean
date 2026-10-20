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

def certificate00_root0000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000000_checked :
    certificate00_root0000000.fastVerify [16,17,18,19] [] = true := rfl

def certificate00_root0000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000001_checked :
    certificate00_root0000001.fastVerify [16,17,18,19] [15] = true := rfl

def certificate00_root000000 : OrbitCertificate :=
  (.split certificate00_root0000000 certificate00_root0000001)

theorem certificate00_root000000_checked :
    certificate00_root000000.fastVerify [15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0000000_checked, certificate00_root0000001_checked⟩

def certificate00_root0000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000010_checked :
    certificate00_root0000010.fastVerify [16,17,18,19] [14] = true := rfl

def certificate00_root0000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000011_checked :
    certificate00_root0000011.fastVerify [16,17,18,19] [15,14] = true := rfl

def certificate00_root000001 : OrbitCertificate :=
  (.split certificate00_root0000010 certificate00_root0000011)

theorem certificate00_root000001_checked :
    certificate00_root000001.fastVerify [15,16,17,18,19] [14] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0000010_checked, certificate00_root0000011_checked⟩

def certificate00_root00000 : OrbitCertificate :=
  (.split certificate00_root000000 certificate00_root000001)

theorem certificate00_root00000_checked :
    certificate00_root00000.fastVerify [14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root000000_checked, certificate00_root000001_checked⟩

def certificate00_root0000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000100_checked :
    certificate00_root0000100.fastVerify [16,17,18,19] [13] = true := rfl

def certificate00_root0000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000101_checked :
    certificate00_root0000101.fastVerify [16,17,18,19] [15,13] = true := rfl

def certificate00_root000010 : OrbitCertificate :=
  (.split certificate00_root0000100 certificate00_root0000101)

theorem certificate00_root000010_checked :
    certificate00_root000010.fastVerify [15,16,17,18,19] [13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0000100_checked, certificate00_root0000101_checked⟩

def certificate00_root0000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000110_checked :
    certificate00_root0000110.fastVerify [16,17,18,19] [14,13] = true := rfl

def certificate00_root0000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0000111_checked :
    certificate00_root0000111.fastVerify [16,17,18,19] [15,14,13] = true := rfl

def certificate00_root000011 : OrbitCertificate :=
  (.split certificate00_root0000110 certificate00_root0000111)

theorem certificate00_root000011_checked :
    certificate00_root000011.fastVerify [15,16,17,18,19] [14,13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0000110_checked, certificate00_root0000111_checked⟩

def certificate00_root00001 : OrbitCertificate :=
  (.split certificate00_root000010 certificate00_root000011)

theorem certificate00_root00001_checked :
    certificate00_root00001.fastVerify [14,15,16,17,18,19] [13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root000010_checked, certificate00_root000011_checked⟩

def certificate00_root0000 : OrbitCertificate :=
  (.split certificate00_root00000 certificate00_root00001)

theorem certificate00_root0000_checked :
    certificate00_root0000.fastVerify [13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root00000_checked, certificate00_root00001_checked⟩

def certificate00_root0001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001000_checked :
    certificate00_root0001000.fastVerify [16,17,18,19] [12] = true := rfl

def certificate00_root0001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001001_checked :
    certificate00_root0001001.fastVerify [16,17,18,19] [15,12] = true := rfl

def certificate00_root000100 : OrbitCertificate :=
  (.split certificate00_root0001000 certificate00_root0001001)

theorem certificate00_root000100_checked :
    certificate00_root000100.fastVerify [15,16,17,18,19] [12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0001000_checked, certificate00_root0001001_checked⟩

def certificate00_root0001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001010_checked :
    certificate00_root0001010.fastVerify [16,17,18,19] [14,12] = true := rfl

def certificate00_root0001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001011_checked :
    certificate00_root0001011.fastVerify [16,17,18,19] [15,14,12] = true := rfl

def certificate00_root000101 : OrbitCertificate :=
  (.split certificate00_root0001010 certificate00_root0001011)

theorem certificate00_root000101_checked :
    certificate00_root000101.fastVerify [15,16,17,18,19] [14,12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0001010_checked, certificate00_root0001011_checked⟩

def certificate00_root00010 : OrbitCertificate :=
  (.split certificate00_root000100 certificate00_root000101)

theorem certificate00_root00010_checked :
    certificate00_root00010.fastVerify [14,15,16,17,18,19] [12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root000100_checked, certificate00_root000101_checked⟩

def certificate00_root0001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001100_checked :
    certificate00_root0001100.fastVerify [16,17,18,19] [13,12] = true := rfl

def certificate00_root0001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001101_checked :
    certificate00_root0001101.fastVerify [16,17,18,19] [15,13,12] = true := rfl

def certificate00_root000110 : OrbitCertificate :=
  (.split certificate00_root0001100 certificate00_root0001101)

theorem certificate00_root000110_checked :
    certificate00_root000110.fastVerify [15,16,17,18,19] [13,12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0001100_checked, certificate00_root0001101_checked⟩

def certificate00_root0001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001110_checked :
    certificate00_root0001110.fastVerify [16,17,18,19] [14,13,12] = true := rfl

def certificate00_root0001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0001111_checked :
    certificate00_root0001111.fastVerify [16,17,18,19] [15,14,13,12] = true := rfl

def certificate00_root000111 : OrbitCertificate :=
  (.split certificate00_root0001110 certificate00_root0001111)

theorem certificate00_root000111_checked :
    certificate00_root000111.fastVerify [15,16,17,18,19] [14,13,12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0001110_checked, certificate00_root0001111_checked⟩

def certificate00_root00011 : OrbitCertificate :=
  (.split certificate00_root000110 certificate00_root000111)

theorem certificate00_root00011_checked :
    certificate00_root00011.fastVerify [14,15,16,17,18,19] [13,12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root000110_checked, certificate00_root000111_checked⟩

def certificate00_root0001 : OrbitCertificate :=
  (.split certificate00_root00010 certificate00_root00011)

theorem certificate00_root0001_checked :
    certificate00_root0001.fastVerify [13,14,15,16,17,18,19] [12] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root00010_checked, certificate00_root00011_checked⟩

def certificate00_root000 : OrbitCertificate :=
  (.split certificate00_root0000 certificate00_root0001)

theorem certificate00_root000_checked :
    certificate00_root000.fastVerify [12,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0000_checked, certificate00_root0001_checked⟩

def certificate00_root0010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010000_checked :
    certificate00_root0010000.fastVerify [16,17,18,19] [11] = true := rfl

def certificate00_root0010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010001_checked :
    certificate00_root0010001.fastVerify [16,17,18,19] [15,11] = true := rfl

def certificate00_root001000 : OrbitCertificate :=
  (.split certificate00_root0010000 certificate00_root0010001)

theorem certificate00_root001000_checked :
    certificate00_root001000.fastVerify [15,16,17,18,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0010000_checked, certificate00_root0010001_checked⟩

def certificate00_root0010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010010_checked :
    certificate00_root0010010.fastVerify [16,17,18,19] [14,11] = true := rfl

def certificate00_root0010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010011_checked :
    certificate00_root0010011.fastVerify [16,17,18,19] [15,14,11] = true := rfl

def certificate00_root001001 : OrbitCertificate :=
  (.split certificate00_root0010010 certificate00_root0010011)

theorem certificate00_root001001_checked :
    certificate00_root001001.fastVerify [15,16,17,18,19] [14,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0010010_checked, certificate00_root0010011_checked⟩

def certificate00_root00100 : OrbitCertificate :=
  (.split certificate00_root001000 certificate00_root001001)

theorem certificate00_root00100_checked :
    certificate00_root00100.fastVerify [14,15,16,17,18,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root001000_checked, certificate00_root001001_checked⟩

def certificate00_root0010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010100_checked :
    certificate00_root0010100.fastVerify [16,17,18,19] [13,11] = true := rfl

def certificate00_root0010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010101_checked :
    certificate00_root0010101.fastVerify [16,17,18,19] [15,13,11] = true := rfl

def certificate00_root001010 : OrbitCertificate :=
  (.split certificate00_root0010100 certificate00_root0010101)

theorem certificate00_root001010_checked :
    certificate00_root001010.fastVerify [15,16,17,18,19] [13,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0010100_checked, certificate00_root0010101_checked⟩

def certificate00_root0010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010110_checked :
    certificate00_root0010110.fastVerify [16,17,18,19] [14,13,11] = true := rfl

def certificate00_root0010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0010111_checked :
    certificate00_root0010111.fastVerify [16,17,18,19] [15,14,13,11] = true := rfl

def certificate00_root001011 : OrbitCertificate :=
  (.split certificate00_root0010110 certificate00_root0010111)

theorem certificate00_root001011_checked :
    certificate00_root001011.fastVerify [15,16,17,18,19] [14,13,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0010110_checked, certificate00_root0010111_checked⟩

def certificate00_root00101 : OrbitCertificate :=
  (.split certificate00_root001010 certificate00_root001011)

theorem certificate00_root00101_checked :
    certificate00_root00101.fastVerify [14,15,16,17,18,19] [13,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root001010_checked, certificate00_root001011_checked⟩

def certificate00_root0010 : OrbitCertificate :=
  (.split certificate00_root00100 certificate00_root00101)

theorem certificate00_root0010_checked :
    certificate00_root0010.fastVerify [13,14,15,16,17,18,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root00100_checked, certificate00_root00101_checked⟩

def certificate00_root0011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011000_checked :
    certificate00_root0011000.fastVerify [16,17,18,19] [12,11] = true := rfl

def certificate00_root0011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011001_checked :
    certificate00_root0011001.fastVerify [16,17,18,19] [15,12,11] = true := rfl

def certificate00_root001100 : OrbitCertificate :=
  (.split certificate00_root0011000 certificate00_root0011001)

theorem certificate00_root001100_checked :
    certificate00_root001100.fastVerify [15,16,17,18,19] [12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0011000_checked, certificate00_root0011001_checked⟩

def certificate00_root0011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011010_checked :
    certificate00_root0011010.fastVerify [16,17,18,19] [14,12,11] = true := rfl

def certificate00_root0011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011011_checked :
    certificate00_root0011011.fastVerify [16,17,18,19] [15,14,12,11] = true := rfl

def certificate00_root001101 : OrbitCertificate :=
  (.split certificate00_root0011010 certificate00_root0011011)

theorem certificate00_root001101_checked :
    certificate00_root001101.fastVerify [15,16,17,18,19] [14,12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0011010_checked, certificate00_root0011011_checked⟩

def certificate00_root00110 : OrbitCertificate :=
  (.split certificate00_root001100 certificate00_root001101)

theorem certificate00_root00110_checked :
    certificate00_root00110.fastVerify [14,15,16,17,18,19] [12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root001100_checked, certificate00_root001101_checked⟩

def certificate00_root0011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011100_checked :
    certificate00_root0011100.fastVerify [16,17,18,19] [13,12,11] = true := rfl

def certificate00_root0011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011101_checked :
    certificate00_root0011101.fastVerify [16,17,18,19] [15,13,12,11] = true := rfl

def certificate00_root001110 : OrbitCertificate :=
  (.split certificate00_root0011100 certificate00_root0011101)

theorem certificate00_root001110_checked :
    certificate00_root001110.fastVerify [15,16,17,18,19] [13,12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0011100_checked, certificate00_root0011101_checked⟩

def certificate00_root0011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011110_checked :
    certificate00_root0011110.fastVerify [16,17,18,19] [14,13,12,11] = true := rfl

def certificate00_root0011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0011111_checked :
    certificate00_root0011111.fastVerify [16,17,18,19] [15,14,13,12,11] = true := rfl

def certificate00_root001111 : OrbitCertificate :=
  (.split certificate00_root0011110 certificate00_root0011111)

theorem certificate00_root001111_checked :
    certificate00_root001111.fastVerify [15,16,17,18,19] [14,13,12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0011110_checked, certificate00_root0011111_checked⟩

def certificate00_root00111 : OrbitCertificate :=
  (.split certificate00_root001110 certificate00_root001111)

theorem certificate00_root00111_checked :
    certificate00_root00111.fastVerify [14,15,16,17,18,19] [13,12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root001110_checked, certificate00_root001111_checked⟩

def certificate00_root0011 : OrbitCertificate :=
  (.split certificate00_root00110 certificate00_root00111)

theorem certificate00_root0011_checked :
    certificate00_root0011.fastVerify [13,14,15,16,17,18,19] [12,11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root00110_checked, certificate00_root00111_checked⟩

def certificate00_root001 : OrbitCertificate :=
  (.split certificate00_root0010 certificate00_root0011)

theorem certificate00_root001_checked :
    certificate00_root001.fastVerify [12,13,14,15,16,17,18,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0010_checked, certificate00_root0011_checked⟩

def certificate00_root00 : OrbitCertificate :=
  (.split certificate00_root000 certificate00_root001)

theorem certificate00_root00_checked :
    certificate00_root00.fastVerify [11,12,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root000_checked, certificate00_root001_checked⟩

def certificate00_root0100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100000_checked :
    certificate00_root0100000.fastVerify [16,17,18,19] [10] = true := rfl

def certificate00_root0100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100001_checked :
    certificate00_root0100001.fastVerify [16,17,18,19] [15,10] = true := rfl

def certificate00_root010000 : OrbitCertificate :=
  (.split certificate00_root0100000 certificate00_root0100001)

theorem certificate00_root010000_checked :
    certificate00_root010000.fastVerify [15,16,17,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0100000_checked, certificate00_root0100001_checked⟩

def certificate00_root0100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100010_checked :
    certificate00_root0100010.fastVerify [16,17,18,19] [14,10] = true := rfl

def certificate00_root0100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100011_checked :
    certificate00_root0100011.fastVerify [16,17,18,19] [15,14,10] = true := rfl

def certificate00_root010001 : OrbitCertificate :=
  (.split certificate00_root0100010 certificate00_root0100011)

theorem certificate00_root010001_checked :
    certificate00_root010001.fastVerify [15,16,17,18,19] [14,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0100010_checked, certificate00_root0100011_checked⟩

def certificate00_root01000 : OrbitCertificate :=
  (.split certificate00_root010000 certificate00_root010001)

theorem certificate00_root01000_checked :
    certificate00_root01000.fastVerify [14,15,16,17,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root010000_checked, certificate00_root010001_checked⟩

def certificate00_root0100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100100_checked :
    certificate00_root0100100.fastVerify [16,17,18,19] [13,10] = true := rfl

def certificate00_root0100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100101_checked :
    certificate00_root0100101.fastVerify [16,17,18,19] [15,13,10] = true := rfl

def certificate00_root010010 : OrbitCertificate :=
  (.split certificate00_root0100100 certificate00_root0100101)

theorem certificate00_root010010_checked :
    certificate00_root010010.fastVerify [15,16,17,18,19] [13,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0100100_checked, certificate00_root0100101_checked⟩

def certificate00_root0100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100110_checked :
    certificate00_root0100110.fastVerify [16,17,18,19] [14,13,10] = true := rfl

def certificate00_root0100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0100111_checked :
    certificate00_root0100111.fastVerify [16,17,18,19] [15,14,13,10] = true := rfl

def certificate00_root010011 : OrbitCertificate :=
  (.split certificate00_root0100110 certificate00_root0100111)

theorem certificate00_root010011_checked :
    certificate00_root010011.fastVerify [15,16,17,18,19] [14,13,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0100110_checked, certificate00_root0100111_checked⟩

def certificate00_root01001 : OrbitCertificate :=
  (.split certificate00_root010010 certificate00_root010011)

theorem certificate00_root01001_checked :
    certificate00_root01001.fastVerify [14,15,16,17,18,19] [13,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root010010_checked, certificate00_root010011_checked⟩

def certificate00_root0100 : OrbitCertificate :=
  (.split certificate00_root01000 certificate00_root01001)

theorem certificate00_root0100_checked :
    certificate00_root0100.fastVerify [13,14,15,16,17,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root01000_checked, certificate00_root01001_checked⟩

def certificate00_root0101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101000_checked :
    certificate00_root0101000.fastVerify [16,17,18,19] [12,10] = true := rfl

def certificate00_root0101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101001_checked :
    certificate00_root0101001.fastVerify [16,17,18,19] [15,12,10] = true := rfl

def certificate00_root010100 : OrbitCertificate :=
  (.split certificate00_root0101000 certificate00_root0101001)

theorem certificate00_root010100_checked :
    certificate00_root010100.fastVerify [15,16,17,18,19] [12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0101000_checked, certificate00_root0101001_checked⟩

def certificate00_root0101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101010_checked :
    certificate00_root0101010.fastVerify [16,17,18,19] [14,12,10] = true := rfl

def certificate00_root0101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101011_checked :
    certificate00_root0101011.fastVerify [16,17,18,19] [15,14,12,10] = true := rfl

def certificate00_root010101 : OrbitCertificate :=
  (.split certificate00_root0101010 certificate00_root0101011)

theorem certificate00_root010101_checked :
    certificate00_root010101.fastVerify [15,16,17,18,19] [14,12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0101010_checked, certificate00_root0101011_checked⟩

def certificate00_root01010 : OrbitCertificate :=
  (.split certificate00_root010100 certificate00_root010101)

theorem certificate00_root01010_checked :
    certificate00_root01010.fastVerify [14,15,16,17,18,19] [12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root010100_checked, certificate00_root010101_checked⟩

def certificate00_root0101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101100_checked :
    certificate00_root0101100.fastVerify [16,17,18,19] [13,12,10] = true := rfl

def certificate00_root0101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101101_checked :
    certificate00_root0101101.fastVerify [16,17,18,19] [15,13,12,10] = true := rfl

def certificate00_root010110 : OrbitCertificate :=
  (.split certificate00_root0101100 certificate00_root0101101)

theorem certificate00_root010110_checked :
    certificate00_root010110.fastVerify [15,16,17,18,19] [13,12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0101100_checked, certificate00_root0101101_checked⟩

def certificate00_root0101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101110_checked :
    certificate00_root0101110.fastVerify [16,17,18,19] [14,13,12,10] = true := rfl

def certificate00_root0101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0101111_checked :
    certificate00_root0101111.fastVerify [16,17,18,19] [15,14,13,12,10] = true := rfl

def certificate00_root010111 : OrbitCertificate :=
  (.split certificate00_root0101110 certificate00_root0101111)

theorem certificate00_root010111_checked :
    certificate00_root010111.fastVerify [15,16,17,18,19] [14,13,12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0101110_checked, certificate00_root0101111_checked⟩

def certificate00_root01011 : OrbitCertificate :=
  (.split certificate00_root010110 certificate00_root010111)

theorem certificate00_root01011_checked :
    certificate00_root01011.fastVerify [14,15,16,17,18,19] [13,12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root010110_checked, certificate00_root010111_checked⟩

def certificate00_root0101 : OrbitCertificate :=
  (.split certificate00_root01010 certificate00_root01011)

theorem certificate00_root0101_checked :
    certificate00_root0101.fastVerify [13,14,15,16,17,18,19] [12,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root01010_checked, certificate00_root01011_checked⟩

def certificate00_root010 : OrbitCertificate :=
  (.split certificate00_root0100 certificate00_root0101)

theorem certificate00_root010_checked :
    certificate00_root010.fastVerify [12,13,14,15,16,17,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0100_checked, certificate00_root0101_checked⟩

def certificate00_root0110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110000_checked :
    certificate00_root0110000.fastVerify [16,17,18,19] [11,10] = true := rfl

def certificate00_root0110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110001_checked :
    certificate00_root0110001.fastVerify [16,17,18,19] [15,11,10] = true := rfl

def certificate00_root011000 : OrbitCertificate :=
  (.split certificate00_root0110000 certificate00_root0110001)

theorem certificate00_root011000_checked :
    certificate00_root011000.fastVerify [15,16,17,18,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0110000_checked, certificate00_root0110001_checked⟩

def certificate00_root0110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110010_checked :
    certificate00_root0110010.fastVerify [16,17,18,19] [14,11,10] = true := rfl

def certificate00_root0110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110011_checked :
    certificate00_root0110011.fastVerify [16,17,18,19] [15,14,11,10] = true := rfl

def certificate00_root011001 : OrbitCertificate :=
  (.split certificate00_root0110010 certificate00_root0110011)

theorem certificate00_root011001_checked :
    certificate00_root011001.fastVerify [15,16,17,18,19] [14,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0110010_checked, certificate00_root0110011_checked⟩

def certificate00_root01100 : OrbitCertificate :=
  (.split certificate00_root011000 certificate00_root011001)

theorem certificate00_root01100_checked :
    certificate00_root01100.fastVerify [14,15,16,17,18,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root011000_checked, certificate00_root011001_checked⟩

def certificate00_root0110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110100_checked :
    certificate00_root0110100.fastVerify [16,17,18,19] [13,11,10] = true := rfl

def certificate00_root0110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110101_checked :
    certificate00_root0110101.fastVerify [16,17,18,19] [15,13,11,10] = true := rfl

def certificate00_root011010 : OrbitCertificate :=
  (.split certificate00_root0110100 certificate00_root0110101)

theorem certificate00_root011010_checked :
    certificate00_root011010.fastVerify [15,16,17,18,19] [13,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0110100_checked, certificate00_root0110101_checked⟩

def certificate00_root0110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110110_checked :
    certificate00_root0110110.fastVerify [16,17,18,19] [14,13,11,10] = true := rfl

def certificate00_root0110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0110111_checked :
    certificate00_root0110111.fastVerify [16,17,18,19] [15,14,13,11,10] = true := rfl

def certificate00_root011011 : OrbitCertificate :=
  (.split certificate00_root0110110 certificate00_root0110111)

theorem certificate00_root011011_checked :
    certificate00_root011011.fastVerify [15,16,17,18,19] [14,13,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0110110_checked, certificate00_root0110111_checked⟩

def certificate00_root01101 : OrbitCertificate :=
  (.split certificate00_root011010 certificate00_root011011)

theorem certificate00_root01101_checked :
    certificate00_root01101.fastVerify [14,15,16,17,18,19] [13,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root011010_checked, certificate00_root011011_checked⟩

def certificate00_root0110 : OrbitCertificate :=
  (.split certificate00_root01100 certificate00_root01101)

theorem certificate00_root0110_checked :
    certificate00_root0110.fastVerify [13,14,15,16,17,18,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root01100_checked, certificate00_root01101_checked⟩

def certificate00_root0111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111000_checked :
    certificate00_root0111000.fastVerify [16,17,18,19] [12,11,10] = true := rfl

def certificate00_root0111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111001_checked :
    certificate00_root0111001.fastVerify [16,17,18,19] [15,12,11,10] = true := rfl

def certificate00_root011100 : OrbitCertificate :=
  (.split certificate00_root0111000 certificate00_root0111001)

theorem certificate00_root011100_checked :
    certificate00_root011100.fastVerify [15,16,17,18,19] [12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0111000_checked, certificate00_root0111001_checked⟩

def certificate00_root0111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111010_checked :
    certificate00_root0111010.fastVerify [16,17,18,19] [14,12,11,10] = true := rfl

def certificate00_root0111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111011_checked :
    certificate00_root0111011.fastVerify [16,17,18,19] [15,14,12,11,10] = true := rfl

def certificate00_root011101 : OrbitCertificate :=
  (.split certificate00_root0111010 certificate00_root0111011)

theorem certificate00_root011101_checked :
    certificate00_root011101.fastVerify [15,16,17,18,19] [14,12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0111010_checked, certificate00_root0111011_checked⟩

def certificate00_root01110 : OrbitCertificate :=
  (.split certificate00_root011100 certificate00_root011101)

theorem certificate00_root01110_checked :
    certificate00_root01110.fastVerify [14,15,16,17,18,19] [12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root011100_checked, certificate00_root011101_checked⟩

def certificate00_root0111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111100_checked :
    certificate00_root0111100.fastVerify [16,17,18,19] [13,12,11,10] = true := rfl

def certificate00_root0111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111101_checked :
    certificate00_root0111101.fastVerify [16,17,18,19] [15,13,12,11,10] = true := rfl

def certificate00_root011110 : OrbitCertificate :=
  (.split certificate00_root0111100 certificate00_root0111101)

theorem certificate00_root011110_checked :
    certificate00_root011110.fastVerify [15,16,17,18,19] [13,12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0111100_checked, certificate00_root0111101_checked⟩

def certificate00_root0111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111110_checked :
    certificate00_root0111110.fastVerify [16,17,18,19] [14,13,12,11,10] = true := rfl

def certificate00_root0111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root0111111_checked :
    certificate00_root0111111.fastVerify [16,17,18,19] [15,14,13,12,11,10] = true := rfl

def certificate00_root011111 : OrbitCertificate :=
  (.split certificate00_root0111110 certificate00_root0111111)

theorem certificate00_root011111_checked :
    certificate00_root011111.fastVerify [15,16,17,18,19] [14,13,12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0111110_checked, certificate00_root0111111_checked⟩

def certificate00_root01111 : OrbitCertificate :=
  (.split certificate00_root011110 certificate00_root011111)

theorem certificate00_root01111_checked :
    certificate00_root01111.fastVerify [14,15,16,17,18,19] [13,12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root011110_checked, certificate00_root011111_checked⟩

def certificate00_root0111 : OrbitCertificate :=
  (.split certificate00_root01110 certificate00_root01111)

theorem certificate00_root0111_checked :
    certificate00_root0111.fastVerify [13,14,15,16,17,18,19] [12,11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root01110_checked, certificate00_root01111_checked⟩

def certificate00_root011 : OrbitCertificate :=
  (.split certificate00_root0110 certificate00_root0111)

theorem certificate00_root011_checked :
    certificate00_root011.fastVerify [12,13,14,15,16,17,18,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0110_checked, certificate00_root0111_checked⟩

def certificate00_root01 : OrbitCertificate :=
  (.split certificate00_root010 certificate00_root011)

theorem certificate00_root01_checked :
    certificate00_root01.fastVerify [11,12,13,14,15,16,17,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root010_checked, certificate00_root011_checked⟩

def certificate00_root0 : OrbitCertificate :=
  (.split certificate00_root00 certificate00_root01)

theorem certificate00_root0_checked :
    certificate00_root0.fastVerify [10,11,12,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root00_checked, certificate00_root01_checked⟩

def certificate00_root1000000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate00_root1000000_checked :
    certificate00_root1000000.fastVerify [16,17,18,19] [0] = true := rfl

def certificate00_root1000001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1000001_checked :
    certificate00_root1000001.fastVerify [16,17,18,19] [15,0] = true := rfl

def certificate00_root100000 : OrbitCertificate :=
  (.split certificate00_root1000000 certificate00_root1000001)

theorem certificate00_root100000_checked :
    certificate00_root100000.fastVerify [15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1000000_checked, certificate00_root1000001_checked⟩

def certificate00_root1000010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 10) (.leaf 11)) (.split (.leaf 10) (.leaf 11)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 17))) (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate00_root1000010_checked :
    certificate00_root1000010.fastVerify [16,17,18,19] [14,0] = true := rfl

def certificate00_root1000011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1000011_checked :
    certificate00_root1000011.fastVerify [16,17,18,19] [15,14,0] = true := rfl

def certificate00_root100001 : OrbitCertificate :=
  (.split certificate00_root1000010 certificate00_root1000011)

theorem certificate00_root100001_checked :
    certificate00_root100001.fastVerify [15,16,17,18,19] [14,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1000010_checked, certificate00_root1000011_checked⟩

def certificate00_root10000 : OrbitCertificate :=
  (.split certificate00_root100000 certificate00_root100001)

theorem certificate00_root10000_checked :
    certificate00_root10000.fastVerify [14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root100000_checked, certificate00_root100001_checked⟩

def certificate00_root1000100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate00_root1000100_checked :
    certificate00_root1000100.fastVerify [16,17,18,19] [13,0] = true := rfl

def certificate00_root1000101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1000101_checked :
    certificate00_root1000101.fastVerify [16,17,18,19] [15,13,0] = true := rfl

def certificate00_root100010 : OrbitCertificate :=
  (.split certificate00_root1000100 certificate00_root1000101)

theorem certificate00_root100010_checked :
    certificate00_root100010.fastVerify [15,16,17,18,19] [13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1000100_checked, certificate00_root1000101_checked⟩

def certificate00_root1000110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate00_root1000110_checked :
    certificate00_root1000110.fastVerify [16,17,18,19] [14,13,0] = true := rfl

def certificate00_root1000111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1000111_checked :
    certificate00_root1000111.fastVerify [16,17,18,19] [15,14,13,0] = true := rfl

def certificate00_root100011 : OrbitCertificate :=
  (.split certificate00_root1000110 certificate00_root1000111)

theorem certificate00_root100011_checked :
    certificate00_root100011.fastVerify [15,16,17,18,19] [14,13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1000110_checked, certificate00_root1000111_checked⟩

def certificate00_root10001 : OrbitCertificate :=
  (.split certificate00_root100010 certificate00_root100011)

theorem certificate00_root10001_checked :
    certificate00_root10001.fastVerify [14,15,16,17,18,19] [13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root100010_checked, certificate00_root100011_checked⟩

def certificate00_root1000 : OrbitCertificate :=
  (.split certificate00_root10000 certificate00_root10001)

theorem certificate00_root1000_checked :
    certificate00_root1000.fastVerify [13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root10000_checked, certificate00_root10001_checked⟩

def certificate00_root1001000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001000_checked :
    certificate00_root1001000.fastVerify [16,17,18,19] [12,0] = true := rfl

def certificate00_root1001001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001001_checked :
    certificate00_root1001001.fastVerify [16,17,18,19] [15,12,0] = true := rfl

def certificate00_root100100 : OrbitCertificate :=
  (.split certificate00_root1001000 certificate00_root1001001)

theorem certificate00_root100100_checked :
    certificate00_root100100.fastVerify [15,16,17,18,19] [12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1001000_checked, certificate00_root1001001_checked⟩

def certificate00_root1001010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001010_checked :
    certificate00_root1001010.fastVerify [16,17,18,19] [14,12,0] = true := rfl

def certificate00_root1001011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001011_checked :
    certificate00_root1001011.fastVerify [16,17,18,19] [15,14,12,0] = true := rfl

def certificate00_root100101 : OrbitCertificate :=
  (.split certificate00_root1001010 certificate00_root1001011)

theorem certificate00_root100101_checked :
    certificate00_root100101.fastVerify [15,16,17,18,19] [14,12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1001010_checked, certificate00_root1001011_checked⟩

def certificate00_root10010 : OrbitCertificate :=
  (.split certificate00_root100100 certificate00_root100101)

theorem certificate00_root10010_checked :
    certificate00_root10010.fastVerify [14,15,16,17,18,19] [12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root100100_checked, certificate00_root100101_checked⟩

def certificate00_root1001100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 17)) (.split (.leaf 14) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 14) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 17)) (.split (.leaf 14) (.leaf 17)))))

theorem certificate00_root1001100_checked :
    certificate00_root1001100.fastVerify [16,17,18,19] [13,12,0] = true := rfl

def certificate00_root1001101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001101_checked :
    certificate00_root1001101.fastVerify [16,17,18,19] [15,13,12,0] = true := rfl

def certificate00_root100110 : OrbitCertificate :=
  (.split certificate00_root1001100 certificate00_root1001101)

theorem certificate00_root100110_checked :
    certificate00_root100110.fastVerify [15,16,17,18,19] [13,12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1001100_checked, certificate00_root1001101_checked⟩

def certificate00_root1001110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 17)) (.split (.leaf 14) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 14) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 17)) (.split (.leaf 14) (.leaf 17)))))

theorem certificate00_root1001110_checked :
    certificate00_root1001110.fastVerify [16,17,18,19] [14,13,12,0] = true := rfl

def certificate00_root1001111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1001111_checked :
    certificate00_root1001111.fastVerify [16,17,18,19] [15,14,13,12,0] = true := rfl

def certificate00_root100111 : OrbitCertificate :=
  (.split certificate00_root1001110 certificate00_root1001111)

theorem certificate00_root100111_checked :
    certificate00_root100111.fastVerify [15,16,17,18,19] [14,13,12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1001110_checked, certificate00_root1001111_checked⟩

def certificate00_root10011 : OrbitCertificate :=
  (.split certificate00_root100110 certificate00_root100111)

theorem certificate00_root10011_checked :
    certificate00_root10011.fastVerify [14,15,16,17,18,19] [13,12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root100110_checked, certificate00_root100111_checked⟩

def certificate00_root1001 : OrbitCertificate :=
  (.split certificate00_root10010 certificate00_root10011)

theorem certificate00_root1001_checked :
    certificate00_root1001.fastVerify [13,14,15,16,17,18,19] [12,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root10010_checked, certificate00_root10011_checked⟩

def certificate00_root100 : OrbitCertificate :=
  (.split certificate00_root1000 certificate00_root1001)

theorem certificate00_root100_checked :
    certificate00_root100.fastVerify [12,13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1000_checked, certificate00_root1001_checked⟩

def certificate00_root1010000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate00_root1010000_checked :
    certificate00_root1010000.fastVerify [16,17,18,19] [11,0] = true := rfl

def certificate00_root1010001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1010001_checked :
    certificate00_root1010001.fastVerify [16,17,18,19] [15,11,0] = true := rfl

def certificate00_root101000 : OrbitCertificate :=
  (.split certificate00_root1010000 certificate00_root1010001)

theorem certificate00_root101000_checked :
    certificate00_root101000.fastVerify [15,16,17,18,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1010000_checked, certificate00_root1010001_checked⟩

def certificate00_root1010010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate00_root1010010_checked :
    certificate00_root1010010.fastVerify [16,17,18,19] [14,11,0] = true := rfl

def certificate00_root1010011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1010011_checked :
    certificate00_root1010011.fastVerify [16,17,18,19] [15,14,11,0] = true := rfl

def certificate00_root101001 : OrbitCertificate :=
  (.split certificate00_root1010010 certificate00_root1010011)

theorem certificate00_root101001_checked :
    certificate00_root101001.fastVerify [15,16,17,18,19] [14,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1010010_checked, certificate00_root1010011_checked⟩

def certificate00_root10100 : OrbitCertificate :=
  (.split certificate00_root101000 certificate00_root101001)

theorem certificate00_root10100_checked :
    certificate00_root10100.fastVerify [14,15,16,17,18,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root101000_checked, certificate00_root101001_checked⟩

def certificate00_root1010100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))))

theorem certificate00_root1010100_checked :
    certificate00_root1010100.fastVerify [16,17,18,19] [13,11,0] = true := rfl

def certificate00_root1010101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1010101_checked :
    certificate00_root1010101.fastVerify [16,17,18,19] [15,13,11,0] = true := rfl

def certificate00_root101010 : OrbitCertificate :=
  (.split certificate00_root1010100 certificate00_root1010101)

theorem certificate00_root101010_checked :
    certificate00_root101010.fastVerify [15,16,17,18,19] [13,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1010100_checked, certificate00_root1010101_checked⟩

def certificate00_root1010110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))))

theorem certificate00_root1010110_checked :
    certificate00_root1010110.fastVerify [16,17,18,19] [14,13,11,0] = true := rfl

def certificate00_root1010111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate00_root1010111_checked :
    certificate00_root1010111.fastVerify [16,17,18,19] [15,14,13,11,0] = true := rfl

def certificate00_root101011 : OrbitCertificate :=
  (.split certificate00_root1010110 certificate00_root1010111)

theorem certificate00_root101011_checked :
    certificate00_root101011.fastVerify [15,16,17,18,19] [14,13,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1010110_checked, certificate00_root1010111_checked⟩

def certificate00_root10101 : OrbitCertificate :=
  (.split certificate00_root101010 certificate00_root101011)

theorem certificate00_root10101_checked :
    certificate00_root10101.fastVerify [14,15,16,17,18,19] [13,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root101010_checked, certificate00_root101011_checked⟩

def certificate00_root1010 : OrbitCertificate :=
  (.split certificate00_root10100 certificate00_root10101)

theorem certificate00_root1010_checked :
    certificate00_root1010.fastVerify [13,14,15,16,17,18,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root10100_checked, certificate00_root10101_checked⟩

def certificate00_root1011000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011000_checked :
    certificate00_root1011000.fastVerify [16,17,18,19] [12,11,0] = true := rfl

def certificate00_root1011001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1011001_checked :
    certificate00_root1011001.fastVerify [16,17,18,19] [15,12,11,0] = true := rfl

def certificate00_root101100 : OrbitCertificate :=
  (.split certificate00_root1011000 certificate00_root1011001)

theorem certificate00_root101100_checked :
    certificate00_root101100.fastVerify [15,16,17,18,19] [12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1011000_checked, certificate00_root1011001_checked⟩

def certificate00_root1011010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 17))) (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011010_checked :
    certificate00_root1011010.fastVerify [16,17,18,19] [14,12,11,0] = true := rfl

def certificate00_root1011011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate00_root1011011_checked :
    certificate00_root1011011.fastVerify [16,17,18,19] [15,14,12,11,0] = true := rfl

def certificate00_root101101 : OrbitCertificate :=
  (.split certificate00_root1011010 certificate00_root1011011)

theorem certificate00_root101101_checked :
    certificate00_root101101.fastVerify [15,16,17,18,19] [14,12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1011010_checked, certificate00_root1011011_checked⟩

def certificate00_root10110 : OrbitCertificate :=
  (.split certificate00_root101100 certificate00_root101101)

theorem certificate00_root10110_checked :
    certificate00_root10110.fastVerify [14,15,16,17,18,19] [12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root101100_checked, certificate00_root101101_checked⟩

def certificate00_root1011100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 16)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011100_checked :
    certificate00_root1011100.fastVerify [16,17,18,19] [13,12,11,0] = true := rfl

def certificate00_root1011101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011101_checked :
    certificate00_root1011101.fastVerify [16,17,18,19] [15,13,12,11,0] = true := rfl

def certificate00_root101110 : OrbitCertificate :=
  (.split certificate00_root1011100 certificate00_root1011101)

theorem certificate00_root101110_checked :
    certificate00_root101110.fastVerify [15,16,17,18,19] [13,12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1011100_checked, certificate00_root1011101_checked⟩

def certificate00_root1011110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 16)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011110_checked :
    certificate00_root1011110.fastVerify [16,17,18,19] [14,13,12,11,0] = true := rfl

def certificate00_root1011111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate00_root1011111_checked :
    certificate00_root1011111.fastVerify [16,17,18,19] [15,14,13,12,11,0] = true := rfl

def certificate00_root101111 : OrbitCertificate :=
  (.split certificate00_root1011110 certificate00_root1011111)

theorem certificate00_root101111_checked :
    certificate00_root101111.fastVerify [15,16,17,18,19] [14,13,12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1011110_checked, certificate00_root1011111_checked⟩

def certificate00_root10111 : OrbitCertificate :=
  (.split certificate00_root101110 certificate00_root101111)

theorem certificate00_root10111_checked :
    certificate00_root10111.fastVerify [14,15,16,17,18,19] [13,12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root101110_checked, certificate00_root101111_checked⟩

def certificate00_root1011 : OrbitCertificate :=
  (.split certificate00_root10110 certificate00_root10111)

theorem certificate00_root1011_checked :
    certificate00_root1011.fastVerify [13,14,15,16,17,18,19] [12,11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root10110_checked, certificate00_root10111_checked⟩

def certificate00_root101 : OrbitCertificate :=
  (.split certificate00_root1010 certificate00_root1011)

theorem certificate00_root101_checked :
    certificate00_root101.fastVerify [12,13,14,15,16,17,18,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1010_checked, certificate00_root1011_checked⟩

def certificate00_root10 : OrbitCertificate :=
  (.split certificate00_root100 certificate00_root101)

theorem certificate00_root10_checked :
    certificate00_root10.fastVerify [11,12,13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root100_checked, certificate00_root101_checked⟩

def certificate00_root1100000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 8) (.leaf 9)) (.split (.leaf 8) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 8) (.leaf 17))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))))

theorem certificate00_root1100000_checked :
    certificate00_root1100000.fastVerify [16,17,18,19] [10,0] = true := rfl

def certificate00_root1100001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 15)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 23)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1100001_checked :
    certificate00_root1100001.fastVerify [16,17,18,19] [15,10,0] = true := rfl

def certificate00_root110000 : OrbitCertificate :=
  (.split certificate00_root1100000 certificate00_root1100001)

theorem certificate00_root110000_checked :
    certificate00_root110000.fastVerify [15,16,17,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1100000_checked, certificate00_root1100001_checked⟩

def certificate00_root1100010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 23))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1100010_checked :
    certificate00_root1100010.fastVerify [16,17,18,19] [14,10,0] = true := rfl

def certificate00_root1100011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 21)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 23)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1100011_checked :
    certificate00_root1100011.fastVerify [16,17,18,19] [15,14,10,0] = true := rfl

def certificate00_root110001 : OrbitCertificate :=
  (.split certificate00_root1100010 certificate00_root1100011)

theorem certificate00_root110001_checked :
    certificate00_root110001.fastVerify [15,16,17,18,19] [14,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1100010_checked, certificate00_root1100011_checked⟩

def certificate00_root11000 : OrbitCertificate :=
  (.split certificate00_root110000 certificate00_root110001)

theorem certificate00_root11000_checked :
    certificate00_root11000.fastVerify [14,15,16,17,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root110000_checked, certificate00_root110001_checked⟩

def certificate00_root1100100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1100100_checked :
    certificate00_root1100100.fastVerify [16,17,18,19] [13,10,0] = true := rfl

def certificate00_root1100101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 23))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1100101_checked :
    certificate00_root1100101.fastVerify [16,17,18,19] [15,13,10,0] = true := rfl

def certificate00_root110010 : OrbitCertificate :=
  (.split certificate00_root1100100 certificate00_root1100101)

theorem certificate00_root110010_checked :
    certificate00_root110010.fastVerify [15,16,17,18,19] [13,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1100100_checked, certificate00_root1100101_checked⟩

def certificate00_root1100110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1100110_checked :
    certificate00_root1100110.fastVerify [16,17,18,19] [14,13,10,0] = true := rfl

def certificate00_root1100111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 23))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1100111_checked :
    certificate00_root1100111.fastVerify [16,17,18,19] [15,14,13,10,0] = true := rfl

def certificate00_root110011 : OrbitCertificate :=
  (.split certificate00_root1100110 certificate00_root1100111)

theorem certificate00_root110011_checked :
    certificate00_root110011.fastVerify [15,16,17,18,19] [14,13,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1100110_checked, certificate00_root1100111_checked⟩

def certificate00_root11001 : OrbitCertificate :=
  (.split certificate00_root110010 certificate00_root110011)

theorem certificate00_root11001_checked :
    certificate00_root11001.fastVerify [14,15,16,17,18,19] [13,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root110010_checked, certificate00_root110011_checked⟩

def certificate00_root1100 : OrbitCertificate :=
  (.split certificate00_root11000 certificate00_root11001)

theorem certificate00_root1100_checked :
    certificate00_root1100.fastVerify [13,14,15,16,17,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root11000_checked, certificate00_root11001_checked⟩

def certificate00_root1101000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 14) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 21)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1101000_checked :
    certificate00_root1101000.fastVerify [16,17,18,19] [12,10,0] = true := rfl

def certificate00_root1101001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 21)) (.split (.leaf 12) (.leaf 21)))))

theorem certificate00_root1101001_checked :
    certificate00_root1101001.fastVerify [16,17,18,19] [15,12,10,0] = true := rfl

def certificate00_root110100 : OrbitCertificate :=
  (.split certificate00_root1101000 certificate00_root1101001)

theorem certificate00_root110100_checked :
    certificate00_root110100.fastVerify [15,16,17,18,19] [12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1101000_checked, certificate00_root1101001_checked⟩

def certificate00_root1101010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 14) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 21)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1101010_checked :
    certificate00_root1101010.fastVerify [16,17,18,19] [14,12,10,0] = true := rfl

def certificate00_root1101011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 21)) (.split (.leaf 12) (.leaf 21)))))

theorem certificate00_root1101011_checked :
    certificate00_root1101011.fastVerify [16,17,18,19] [15,14,12,10,0] = true := rfl

def certificate00_root110101 : OrbitCertificate :=
  (.split certificate00_root1101010 certificate00_root1101011)

theorem certificate00_root110101_checked :
    certificate00_root110101.fastVerify [15,16,17,18,19] [14,12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1101010_checked, certificate00_root1101011_checked⟩

def certificate00_root11010 : OrbitCertificate :=
  (.split certificate00_root110100 certificate00_root110101)

theorem certificate00_root11010_checked :
    certificate00_root11010.fastVerify [14,15,16,17,18,19] [12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root110100_checked, certificate00_root110101_checked⟩

def certificate00_root1101100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1101100_checked :
    certificate00_root1101100.fastVerify [16,17,18,19] [13,12,10,0] = true := rfl

def certificate00_root1101101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 23))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1101101_checked :
    certificate00_root1101101.fastVerify [16,17,18,19] [15,13,12,10,0] = true := rfl

def certificate00_root110110 : OrbitCertificate :=
  (.split certificate00_root1101100 certificate00_root1101101)

theorem certificate00_root110110_checked :
    certificate00_root110110.fastVerify [15,16,17,18,19] [13,12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1101100_checked, certificate00_root1101101_checked⟩

def certificate00_root1101110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1101110_checked :
    certificate00_root1101110.fastVerify [16,17,18,19] [14,13,12,10,0] = true := rfl

def certificate00_root1101111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 23))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 23)))))

theorem certificate00_root1101111_checked :
    certificate00_root1101111.fastVerify [16,17,18,19] [15,14,13,12,10,0] = true := rfl

def certificate00_root110111 : OrbitCertificate :=
  (.split certificate00_root1101110 certificate00_root1101111)

theorem certificate00_root110111_checked :
    certificate00_root110111.fastVerify [15,16,17,18,19] [14,13,12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1101110_checked, certificate00_root1101111_checked⟩

def certificate00_root11011 : OrbitCertificate :=
  (.split certificate00_root110110 certificate00_root110111)

theorem certificate00_root11011_checked :
    certificate00_root11011.fastVerify [14,15,16,17,18,19] [13,12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root110110_checked, certificate00_root110111_checked⟩

def certificate00_root1101 : OrbitCertificate :=
  (.split certificate00_root11010 certificate00_root11011)

theorem certificate00_root1101_checked :
    certificate00_root1101.fastVerify [13,14,15,16,17,18,19] [12,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root11010_checked, certificate00_root11011_checked⟩

def certificate00_root110 : OrbitCertificate :=
  (.split certificate00_root1100 certificate00_root1101)

theorem certificate00_root110_checked :
    certificate00_root110.fastVerify [12,13,14,15,16,17,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1100_checked, certificate00_root1101_checked⟩

def certificate00_root1110000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 12)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1110000_checked :
    certificate00_root1110000.fastVerify [16,17,18,19] [11,10,0] = true := rfl

def certificate00_root1110001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 21)))))

theorem certificate00_root1110001_checked :
    certificate00_root1110001.fastVerify [16,17,18,19] [15,11,10,0] = true := rfl

def certificate00_root111000 : OrbitCertificate :=
  (.split certificate00_root1110000 certificate00_root1110001)

theorem certificate00_root111000_checked :
    certificate00_root111000.fastVerify [15,16,17,18,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1110000_checked, certificate00_root1110001_checked⟩

def certificate00_root1110010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1110010_checked :
    certificate00_root1110010.fastVerify [16,17,18,19] [14,11,10,0] = true := rfl

def certificate00_root1110011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 21))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 21)))))

theorem certificate00_root1110011_checked :
    certificate00_root1110011.fastVerify [16,17,18,19] [15,14,11,10,0] = true := rfl

def certificate00_root111001 : OrbitCertificate :=
  (.split certificate00_root1110010 certificate00_root1110011)

theorem certificate00_root111001_checked :
    certificate00_root111001.fastVerify [15,16,17,18,19] [14,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1110010_checked, certificate00_root1110011_checked⟩

def certificate00_root11100 : OrbitCertificate :=
  (.split certificate00_root111000 certificate00_root111001)

theorem certificate00_root11100_checked :
    certificate00_root11100.fastVerify [14,15,16,17,18,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root111000_checked, certificate00_root111001_checked⟩

def certificate00_root1110100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 13)) (.split (.leaf 14) (.leaf 13)))) (.split (.split (.split (.leaf 0) (.leaf 12)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1110100_checked :
    certificate00_root1110100.fastVerify [16,17,18,19] [13,11,10,0] = true := rfl

def certificate00_root1110101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1110101_checked :
    certificate00_root1110101.fastVerify [16,17,18,19] [15,13,11,10,0] = true := rfl

def certificate00_root111010 : OrbitCertificate :=
  (.split certificate00_root1110100 certificate00_root1110101)

theorem certificate00_root111010_checked :
    certificate00_root111010.fastVerify [15,16,17,18,19] [13,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1110100_checked, certificate00_root1110101_checked⟩

def certificate00_root1110110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 14) (.leaf 13)) (.split (.leaf 14) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1110110_checked :
    certificate00_root1110110.fastVerify [16,17,18,19] [14,13,11,10,0] = true := rfl

def certificate00_root1110111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate00_root1110111_checked :
    certificate00_root1110111.fastVerify [16,17,18,19] [15,14,13,11,10,0] = true := rfl

def certificate00_root111011 : OrbitCertificate :=
  (.split certificate00_root1110110 certificate00_root1110111)

theorem certificate00_root111011_checked :
    certificate00_root111011.fastVerify [15,16,17,18,19] [14,13,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1110110_checked, certificate00_root1110111_checked⟩

def certificate00_root11101 : OrbitCertificate :=
  (.split certificate00_root111010 certificate00_root111011)

theorem certificate00_root11101_checked :
    certificate00_root11101.fastVerify [14,15,16,17,18,19] [13,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root111010_checked, certificate00_root111011_checked⟩

def certificate00_root1110 : OrbitCertificate :=
  (.split certificate00_root11100 certificate00_root11101)

theorem certificate00_root1110_checked :
    certificate00_root1110.fastVerify [13,14,15,16,17,18,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root11100_checked, certificate00_root11101_checked⟩

def certificate00_root1111000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1111000_checked :
    certificate00_root1111000.fastVerify [16,17,18,19] [12,11,10,0] = true := rfl

def certificate00_root1111001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 21)))))

theorem certificate00_root1111001_checked :
    certificate00_root1111001.fastVerify [16,17,18,19] [15,12,11,10,0] = true := rfl

def certificate00_root111100 : OrbitCertificate :=
  (.split certificate00_root1111000 certificate00_root1111001)

theorem certificate00_root111100_checked :
    certificate00_root111100.fastVerify [15,16,17,18,19] [12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1111000_checked, certificate00_root1111001_checked⟩

def certificate00_root1111010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1111010_checked :
    certificate00_root1111010.fastVerify [16,17,18,19] [14,12,11,10,0] = true := rfl

def certificate00_root1111011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 21)))))

theorem certificate00_root1111011_checked :
    certificate00_root1111011.fastVerify [16,17,18,19] [15,14,12,11,10,0] = true := rfl

def certificate00_root111101 : OrbitCertificate :=
  (.split certificate00_root1111010 certificate00_root1111011)

theorem certificate00_root111101_checked :
    certificate00_root111101.fastVerify [15,16,17,18,19] [14,12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1111010_checked, certificate00_root1111011_checked⟩

def certificate00_root11110 : OrbitCertificate :=
  (.split certificate00_root111100 certificate00_root111101)

theorem certificate00_root11110_checked :
    certificate00_root11110.fastVerify [14,15,16,17,18,19] [12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root111100_checked, certificate00_root111101_checked⟩

def certificate00_root1111100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1111100_checked :
    certificate00_root1111100.fastVerify [16,17,18,19] [13,12,11,10,0] = true := rfl

def certificate00_root1111101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate00_root1111101_checked :
    certificate00_root1111101.fastVerify [16,17,18,19] [15,13,12,11,10,0] = true := rfl

def certificate00_root111110 : OrbitCertificate :=
  (.split certificate00_root1111100 certificate00_root1111101)

theorem certificate00_root111110_checked :
    certificate00_root111110.fastVerify [15,16,17,18,19] [13,12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1111100_checked, certificate00_root1111101_checked⟩

def certificate00_root1111110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 14) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate00_root1111110_checked :
    certificate00_root1111110.fastVerify [16,17,18,19] [14,13,12,11,10,0] = true := rfl

def certificate00_root1111111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 19))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate00_root1111111_checked :
    certificate00_root1111111.fastVerify [16,17,18,19] [15,14,13,12,11,10,0] = true := rfl

def certificate00_root111111 : OrbitCertificate :=
  (.split certificate00_root1111110 certificate00_root1111111)

theorem certificate00_root111111_checked :
    certificate00_root111111.fastVerify [15,16,17,18,19] [14,13,12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1111110_checked, certificate00_root1111111_checked⟩

def certificate00_root11111 : OrbitCertificate :=
  (.split certificate00_root111110 certificate00_root111111)

theorem certificate00_root11111_checked :
    certificate00_root11111.fastVerify [14,15,16,17,18,19] [13,12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root111110_checked, certificate00_root111111_checked⟩

def certificate00_root1111 : OrbitCertificate :=
  (.split certificate00_root11110 certificate00_root11111)

theorem certificate00_root1111_checked :
    certificate00_root1111.fastVerify [13,14,15,16,17,18,19] [12,11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root11110_checked, certificate00_root11111_checked⟩

def certificate00_root111 : OrbitCertificate :=
  (.split certificate00_root1110 certificate00_root1111)

theorem certificate00_root111_checked :
    certificate00_root111.fastVerify [12,13,14,15,16,17,18,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root1110_checked, certificate00_root1111_checked⟩

def certificate00_root11 : OrbitCertificate :=
  (.split certificate00_root110 certificate00_root111)

theorem certificate00_root11_checked :
    certificate00_root11.fastVerify [11,12,13,14,15,16,17,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root110_checked, certificate00_root111_checked⟩

def certificate00_root1 : OrbitCertificate :=
  (.split certificate00_root10 certificate00_root11)

theorem certificate00_root1_checked :
    certificate00_root1.fastVerify [10,11,12,13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root10_checked, certificate00_root11_checked⟩

def certificate00_root : OrbitCertificate :=
  (.split certificate00_root0 certificate00_root1)

theorem certificate00_root_checked :
    certificate00_root.fastVerify [0,10,11,12,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate00_root0_checked, certificate00_root1_checked⟩

theorem covered_00 : ∀ C ∈ (box 0).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,10,11,12,13,14,15,16,17,18,19] [] certificate00_root
    certificate00_root_checked C
  have hs : C ⊆ ([0,10,11,12,13,14,15,16,17,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_00
