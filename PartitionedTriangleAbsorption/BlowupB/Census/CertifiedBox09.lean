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

def certificate09_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate09_root00000_checked :
    certificate09_root00000.fastVerify [10,11,18,19] [] = true := rfl

def certificate09_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 13) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00001_checked :
    certificate09_root00001.fastVerify [10,11,18,19] [9] = true := rfl

def certificate09_root0000 : OrbitCertificate :=
  (.split certificate09_root00000 certificate09_root00001)

theorem certificate09_root0000_checked :
    certificate09_root0000.fastVerify [9,10,11,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root00000_checked, certificate09_root00001_checked⟩

def certificate09_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 8) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 14) (.leaf 21)) (.split (.leaf 20) (.leaf 21)))))

theorem certificate09_root00010_checked :
    certificate09_root00010.fastVerify [10,11,18,19] [8] = true := rfl

def certificate09_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00011_checked :
    certificate09_root00011.fastVerify [10,11,18,19] [9,8] = true := rfl

def certificate09_root0001 : OrbitCertificate :=
  (.split certificate09_root00010 certificate09_root00011)

theorem certificate09_root0001_checked :
    certificate09_root0001.fastVerify [9,10,11,18,19] [8] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root00010_checked, certificate09_root00011_checked⟩

def certificate09_root000 : OrbitCertificate :=
  (.split certificate09_root0000 certificate09_root0001)

theorem certificate09_root000_checked :
    certificate09_root000.fastVerify [8,9,10,11,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root0000_checked, certificate09_root0001_checked⟩

def certificate09_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00100_checked :
    certificate09_root00100.fastVerify [10,11,18,19] [3] = true := rfl

def certificate09_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00101_checked :
    certificate09_root00101.fastVerify [10,11,18,19] [9,3] = true := rfl

def certificate09_root0010 : OrbitCertificate :=
  (.split certificate09_root00100 certificate09_root00101)

theorem certificate09_root0010_checked :
    certificate09_root0010.fastVerify [9,10,11,18,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root00100_checked, certificate09_root00101_checked⟩

def certificate09_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 10) (.leaf 21)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00110_checked :
    certificate09_root00110.fastVerify [10,11,18,19] [8,3] = true := rfl

def certificate09_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate09_root00111_checked :
    certificate09_root00111.fastVerify [10,11,18,19] [9,8,3] = true := rfl

def certificate09_root0011 : OrbitCertificate :=
  (.split certificate09_root00110 certificate09_root00111)

theorem certificate09_root0011_checked :
    certificate09_root0011.fastVerify [9,10,11,18,19] [8,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root00110_checked, certificate09_root00111_checked⟩

def certificate09_root001 : OrbitCertificate :=
  (.split certificate09_root0010 certificate09_root0011)

theorem certificate09_root001_checked :
    certificate09_root001.fastVerify [8,9,10,11,18,19] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root0010_checked, certificate09_root0011_checked⟩

def certificate09_root00 : OrbitCertificate :=
  (.split certificate09_root000 certificate09_root001)

theorem certificate09_root00_checked :
    certificate09_root00.fastVerify [3,8,9,10,11,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root000_checked, certificate09_root001_checked⟩

def certificate09_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 8) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 14) (.leaf 22))) (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate09_root01000_checked :
    certificate09_root01000.fastVerify [10,11,18,19] [2] = true := rfl

def certificate09_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate09_root01001_checked :
    certificate09_root01001.fastVerify [10,11,18,19] [9,2] = true := rfl

def certificate09_root0100 : OrbitCertificate :=
  (.split certificate09_root01000 certificate09_root01001)

theorem certificate09_root0100_checked :
    certificate09_root0100.fastVerify [9,10,11,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root01000_checked, certificate09_root01001_checked⟩

def certificate09_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 14) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 14) (.leaf 22)))))

theorem certificate09_root01010_checked :
    certificate09_root01010.fastVerify [10,11,18,19] [8,2] = true := rfl

def certificate09_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate09_root01011_checked :
    certificate09_root01011.fastVerify [10,11,18,19] [9,8,2] = true := rfl

def certificate09_root0101 : OrbitCertificate :=
  (.split certificate09_root01010 certificate09_root01011)

theorem certificate09_root0101_checked :
    certificate09_root0101.fastVerify [9,10,11,18,19] [8,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root01010_checked, certificate09_root01011_checked⟩

def certificate09_root010 : OrbitCertificate :=
  (.split certificate09_root0100 certificate09_root0101)

theorem certificate09_root010_checked :
    certificate09_root010.fastVerify [8,9,10,11,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root0100_checked, certificate09_root0101_checked⟩

def certificate09_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 22)))))

theorem certificate09_root01100_checked :
    certificate09_root01100.fastVerify [10,11,18,19] [3,2] = true := rfl

def certificate09_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 22)))))

theorem certificate09_root01101_checked :
    certificate09_root01101.fastVerify [10,11,18,19] [9,3,2] = true := rfl

def certificate09_root0110 : OrbitCertificate :=
  (.split certificate09_root01100 certificate09_root01101)

theorem certificate09_root0110_checked :
    certificate09_root0110.fastVerify [9,10,11,18,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root01100_checked, certificate09_root01101_checked⟩

def certificate09_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 22)))))

theorem certificate09_root01110_checked :
    certificate09_root01110.fastVerify [10,11,18,19] [8,3,2] = true := rfl

def certificate09_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 22)))))

theorem certificate09_root01111_checked :
    certificate09_root01111.fastVerify [10,11,18,19] [9,8,3,2] = true := rfl

def certificate09_root0111 : OrbitCertificate :=
  (.split certificate09_root01110 certificate09_root01111)

theorem certificate09_root0111_checked :
    certificate09_root0111.fastVerify [9,10,11,18,19] [8,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root01110_checked, certificate09_root01111_checked⟩

def certificate09_root011 : OrbitCertificate :=
  (.split certificate09_root0110 certificate09_root0111)

theorem certificate09_root011_checked :
    certificate09_root011.fastVerify [8,9,10,11,18,19] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root0110_checked, certificate09_root0111_checked⟩

def certificate09_root01 : OrbitCertificate :=
  (.split certificate09_root010 certificate09_root011)

theorem certificate09_root01_checked :
    certificate09_root01.fastVerify [3,8,9,10,11,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root010_checked, certificate09_root011_checked⟩

def certificate09_root0 : OrbitCertificate :=
  (.split certificate09_root00 certificate09_root01)

theorem certificate09_root0_checked :
    certificate09_root0.fastVerify [2,3,8,9,10,11,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root00_checked, certificate09_root01_checked⟩

def certificate09_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 14) (.leaf 13)))))

theorem certificate09_root10000_checked :
    certificate09_root10000.fastVerify [10,11,18,19] [0] = true := rfl

def certificate09_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10001_checked :
    certificate09_root10001.fastVerify [10,11,18,19] [9,0] = true := rfl

def certificate09_root1000 : OrbitCertificate :=
  (.split certificate09_root10000 certificate09_root10001)

theorem certificate09_root1000_checked :
    certificate09_root1000.fastVerify [9,10,11,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root10000_checked, certificate09_root10001_checked⟩

def certificate09_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 15)))))

theorem certificate09_root10010_checked :
    certificate09_root10010.fastVerify [10,11,18,19] [8,0] = true := rfl

def certificate09_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10011_checked :
    certificate09_root10011.fastVerify [10,11,18,19] [9,8,0] = true := rfl

def certificate09_root1001 : OrbitCertificate :=
  (.split certificate09_root10010 certificate09_root10011)

theorem certificate09_root1001_checked :
    certificate09_root1001.fastVerify [9,10,11,18,19] [8,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root10010_checked, certificate09_root10011_checked⟩

def certificate09_root100 : OrbitCertificate :=
  (.split certificate09_root1000 certificate09_root1001)

theorem certificate09_root100_checked :
    certificate09_root100.fastVerify [8,9,10,11,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root1000_checked, certificate09_root1001_checked⟩

def certificate09_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10100_checked :
    certificate09_root10100.fastVerify [10,11,18,19] [3,0] = true := rfl

def certificate09_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 10) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10101_checked :
    certificate09_root10101.fastVerify [10,11,18,19] [9,3,0] = true := rfl

def certificate09_root1010 : OrbitCertificate :=
  (.split certificate09_root10100 certificate09_root10101)

theorem certificate09_root1010_checked :
    certificate09_root1010.fastVerify [9,10,11,18,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root10100_checked, certificate09_root10101_checked⟩

def certificate09_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10110_checked :
    certificate09_root10110.fastVerify [10,11,18,19] [8,3,0] = true := rfl

def certificate09_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 10) (.leaf 15)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate09_root10111_checked :
    certificate09_root10111.fastVerify [10,11,18,19] [9,8,3,0] = true := rfl

def certificate09_root1011 : OrbitCertificate :=
  (.split certificate09_root10110 certificate09_root10111)

theorem certificate09_root1011_checked :
    certificate09_root1011.fastVerify [9,10,11,18,19] [8,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root10110_checked, certificate09_root10111_checked⟩

def certificate09_root101 : OrbitCertificate :=
  (.split certificate09_root1010 certificate09_root1011)

theorem certificate09_root101_checked :
    certificate09_root101.fastVerify [8,9,10,11,18,19] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root1010_checked, certificate09_root1011_checked⟩

def certificate09_root10 : OrbitCertificate :=
  (.split certificate09_root100 certificate09_root101)

theorem certificate09_root10_checked :
    certificate09_root10.fastVerify [3,8,9,10,11,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root100_checked, certificate09_root101_checked⟩

def certificate09_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 1)))))

theorem certificate09_root11000_checked :
    certificate09_root11000.fastVerify [10,11,18,19] [2,0] = true := rfl

def certificate09_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 9)))))

theorem certificate09_root11001_checked :
    certificate09_root11001.fastVerify [10,11,18,19] [9,2,0] = true := rfl

def certificate09_root1100 : OrbitCertificate :=
  (.split certificate09_root11000 certificate09_root11001)

theorem certificate09_root1100_checked :
    certificate09_root1100.fastVerify [9,10,11,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root11000_checked, certificate09_root11001_checked⟩

def certificate09_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 8) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3)))))

theorem certificate09_root11010_checked :
    certificate09_root11010.fastVerify [10,11,18,19] [8,2,0] = true := rfl

def certificate09_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 9)))))

theorem certificate09_root11011_checked :
    certificate09_root11011.fastVerify [10,11,18,19] [9,8,2,0] = true := rfl

def certificate09_root1101 : OrbitCertificate :=
  (.split certificate09_root11010 certificate09_root11011)

theorem certificate09_root1101_checked :
    certificate09_root1101.fastVerify [9,10,11,18,19] [8,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root11010_checked, certificate09_root11011_checked⟩

def certificate09_root110 : OrbitCertificate :=
  (.split certificate09_root1100 certificate09_root1101)

theorem certificate09_root110_checked :
    certificate09_root110.fastVerify [8,9,10,11,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root1100_checked, certificate09_root1101_checked⟩

def certificate09_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3)))))

theorem certificate09_root11100_checked :
    certificate09_root11100.fastVerify [10,11,18,19] [3,2,0] = true := rfl

def certificate09_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3)))))

theorem certificate09_root11101_checked :
    certificate09_root11101.fastVerify [10,11,18,19] [9,3,2,0] = true := rfl

def certificate09_root1110 : OrbitCertificate :=
  (.split certificate09_root11100 certificate09_root11101)

theorem certificate09_root1110_checked :
    certificate09_root1110.fastVerify [9,10,11,18,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root11100_checked, certificate09_root11101_checked⟩

def certificate09_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3)))))

theorem certificate09_root11110_checked :
    certificate09_root11110.fastVerify [10,11,18,19] [8,3,2,0] = true := rfl

def certificate09_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 10) (.leaf 10)))) (.split (.split (.split (.leaf 1) (.leaf 3)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3)))))

theorem certificate09_root11111_checked :
    certificate09_root11111.fastVerify [10,11,18,19] [9,8,3,2,0] = true := rfl

def certificate09_root1111 : OrbitCertificate :=
  (.split certificate09_root11110 certificate09_root11111)

theorem certificate09_root1111_checked :
    certificate09_root1111.fastVerify [9,10,11,18,19] [8,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root11110_checked, certificate09_root11111_checked⟩

def certificate09_root111 : OrbitCertificate :=
  (.split certificate09_root1110 certificate09_root1111)

theorem certificate09_root111_checked :
    certificate09_root111.fastVerify [8,9,10,11,18,19] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root1110_checked, certificate09_root1111_checked⟩

def certificate09_root11 : OrbitCertificate :=
  (.split certificate09_root110 certificate09_root111)

theorem certificate09_root11_checked :
    certificate09_root11.fastVerify [3,8,9,10,11,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root110_checked, certificate09_root111_checked⟩

def certificate09_root1 : OrbitCertificate :=
  (.split certificate09_root10 certificate09_root11)

theorem certificate09_root1_checked :
    certificate09_root1.fastVerify [2,3,8,9,10,11,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root10_checked, certificate09_root11_checked⟩

def certificate09_root : OrbitCertificate :=
  (.split certificate09_root0 certificate09_root1)

theorem certificate09_root_checked :
    certificate09_root.fastVerify [0,2,3,8,9,10,11,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate09_root0_checked, certificate09_root1_checked⟩

theorem covered_09 : ∀ C ∈ (box 9).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,2,3,8,9,10,11,18,19] [] certificate09_root
    certificate09_root_checked C
  have hs : C ⊆ ([0,2,3,8,9,10,11,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_09
