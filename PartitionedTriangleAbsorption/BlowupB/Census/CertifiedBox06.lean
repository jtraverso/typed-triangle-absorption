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

def certificate06_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00000_checked :
    certificate06_root00000.fastVerify [14,15,18,19] [] = true := rfl

def certificate06_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00001_checked :
    certificate06_root00001.fastVerify [14,15,18,19] [12] = true := rfl

def certificate06_root0000 : OrbitCertificate :=
  (.split certificate06_root00000 certificate06_root00001)

theorem certificate06_root0000_checked :
    certificate06_root0000.fastVerify [12,14,15,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root00000_checked, certificate06_root00001_checked⟩

def certificate06_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00010_checked :
    certificate06_root00010.fastVerify [14,15,18,19] [11] = true := rfl

def certificate06_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00011_checked :
    certificate06_root00011.fastVerify [14,15,18,19] [12,11] = true := rfl

def certificate06_root0001 : OrbitCertificate :=
  (.split certificate06_root00010 certificate06_root00011)

theorem certificate06_root0001_checked :
    certificate06_root0001.fastVerify [12,14,15,18,19] [11] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root00010_checked, certificate06_root00011_checked⟩

def certificate06_root000 : OrbitCertificate :=
  (.split certificate06_root0000 certificate06_root0001)

theorem certificate06_root000_checked :
    certificate06_root000.fastVerify [11,12,14,15,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root0000_checked, certificate06_root0001_checked⟩

def certificate06_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00100_checked :
    certificate06_root00100.fastVerify [14,15,18,19] [10] = true := rfl

def certificate06_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00101_checked :
    certificate06_root00101.fastVerify [14,15,18,19] [12,10] = true := rfl

def certificate06_root0010 : OrbitCertificate :=
  (.split certificate06_root00100 certificate06_root00101)

theorem certificate06_root0010_checked :
    certificate06_root0010.fastVerify [12,14,15,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root00100_checked, certificate06_root00101_checked⟩

def certificate06_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00110_checked :
    certificate06_root00110.fastVerify [14,15,18,19] [11,10] = true := rfl

def certificate06_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate06_root00111_checked :
    certificate06_root00111.fastVerify [14,15,18,19] [12,11,10] = true := rfl

def certificate06_root0011 : OrbitCertificate :=
  (.split certificate06_root00110 certificate06_root00111)

theorem certificate06_root0011_checked :
    certificate06_root0011.fastVerify [12,14,15,18,19] [11,10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root00110_checked, certificate06_root00111_checked⟩

def certificate06_root001 : OrbitCertificate :=
  (.split certificate06_root0010 certificate06_root0011)

theorem certificate06_root001_checked :
    certificate06_root001.fastVerify [11,12,14,15,18,19] [10] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root0010_checked, certificate06_root0011_checked⟩

def certificate06_root00 : OrbitCertificate :=
  (.split certificate06_root000 certificate06_root001)

theorem certificate06_root00_checked :
    certificate06_root00.fastVerify [10,11,12,14,15,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root000_checked, certificate06_root001_checked⟩

def certificate06_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 14) (.leaf 16)) (.split (.leaf 16) (.leaf 16))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate06_root01000_checked :
    certificate06_root01000.fastVerify [14,15,18,19] [2] = true := rfl

def certificate06_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 20) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate06_root01001_checked :
    certificate06_root01001.fastVerify [14,15,18,19] [12,2] = true := rfl

def certificate06_root0100 : OrbitCertificate :=
  (.split certificate06_root01000 certificate06_root01001)

theorem certificate06_root0100_checked :
    certificate06_root0100.fastVerify [12,14,15,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root01000_checked, certificate06_root01001_checked⟩

def certificate06_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate06_root01010_checked :
    certificate06_root01010.fastVerify [14,15,18,19] [11,2] = true := rfl

def certificate06_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate06_root01011_checked :
    certificate06_root01011.fastVerify [14,15,18,19] [12,11,2] = true := rfl

def certificate06_root0101 : OrbitCertificate :=
  (.split certificate06_root01010 certificate06_root01011)

theorem certificate06_root0101_checked :
    certificate06_root0101.fastVerify [12,14,15,18,19] [11,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root01010_checked, certificate06_root01011_checked⟩

def certificate06_root010 : OrbitCertificate :=
  (.split certificate06_root0100 certificate06_root0101)

theorem certificate06_root010_checked :
    certificate06_root010.fastVerify [11,12,14,15,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root0100_checked, certificate06_root0101_checked⟩

def certificate06_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 14) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate06_root01100_checked :
    certificate06_root01100.fastVerify [14,15,18,19] [10,2] = true := rfl

def certificate06_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 1)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 20) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 20) (.leaf 9)))))

theorem certificate06_root01101_checked :
    certificate06_root01101.fastVerify [14,15,18,19] [12,10,2] = true := rfl

def certificate06_root0110 : OrbitCertificate :=
  (.split certificate06_root01100 certificate06_root01101)

theorem certificate06_root0110_checked :
    certificate06_root0110.fastVerify [12,14,15,18,19] [10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root01100_checked, certificate06_root01101_checked⟩

def certificate06_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate06_root01110_checked :
    certificate06_root01110.fastVerify [14,15,18,19] [11,10,2] = true := rfl

def certificate06_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate06_root01111_checked :
    certificate06_root01111.fastVerify [14,15,18,19] [12,11,10,2] = true := rfl

def certificate06_root0111 : OrbitCertificate :=
  (.split certificate06_root01110 certificate06_root01111)

theorem certificate06_root0111_checked :
    certificate06_root0111.fastVerify [12,14,15,18,19] [11,10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root01110_checked, certificate06_root01111_checked⟩

def certificate06_root011 : OrbitCertificate :=
  (.split certificate06_root0110 certificate06_root0111)

theorem certificate06_root011_checked :
    certificate06_root011.fastVerify [11,12,14,15,18,19] [10,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root0110_checked, certificate06_root0111_checked⟩

def certificate06_root01 : OrbitCertificate :=
  (.split certificate06_root010 certificate06_root011)

theorem certificate06_root01_checked :
    certificate06_root01.fastVerify [10,11,12,14,15,18,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root010_checked, certificate06_root011_checked⟩

def certificate06_root0 : OrbitCertificate :=
  (.split certificate06_root00 certificate06_root01)

theorem certificate06_root0_checked :
    certificate06_root0.fastVerify [2,10,11,12,14,15,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root00_checked, certificate06_root01_checked⟩

def certificate06_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate06_root10000_checked :
    certificate06_root10000.fastVerify [14,15,18,19] [0] = true := rfl

def certificate06_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate06_root10001_checked :
    certificate06_root10001.fastVerify [14,15,18,19] [12,0] = true := rfl

def certificate06_root1000 : OrbitCertificate :=
  (.split certificate06_root10000 certificate06_root10001)

theorem certificate06_root1000_checked :
    certificate06_root1000.fastVerify [12,14,15,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root10000_checked, certificate06_root10001_checked⟩

def certificate06_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate06_root10010_checked :
    certificate06_root10010.fastVerify [14,15,18,19] [11,0] = true := rfl

def certificate06_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))))

theorem certificate06_root10011_checked :
    certificate06_root10011.fastVerify [14,15,18,19] [12,11,0] = true := rfl

def certificate06_root1001 : OrbitCertificate :=
  (.split certificate06_root10010 certificate06_root10011)

theorem certificate06_root1001_checked :
    certificate06_root1001.fastVerify [12,14,15,18,19] [11,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root10010_checked, certificate06_root10011_checked⟩

def certificate06_root100 : OrbitCertificate :=
  (.split certificate06_root1000 certificate06_root1001)

theorem certificate06_root100_checked :
    certificate06_root100.fastVerify [11,12,14,15,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root1000_checked, certificate06_root1001_checked⟩

def certificate06_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate06_root10100_checked :
    certificate06_root10100.fastVerify [14,15,18,19] [10,0] = true := rfl

def certificate06_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 15) (.leaf 15)))))

theorem certificate06_root10101_checked :
    certificate06_root10101.fastVerify [14,15,18,19] [12,10,0] = true := rfl

def certificate06_root1010 : OrbitCertificate :=
  (.split certificate06_root10100 certificate06_root10101)

theorem certificate06_root1010_checked :
    certificate06_root1010.fastVerify [12,14,15,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root10100_checked, certificate06_root10101_checked⟩

def certificate06_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 15)))))

theorem certificate06_root10110_checked :
    certificate06_root10110.fastVerify [14,15,18,19] [11,10,0] = true := rfl

def certificate06_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))) (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 13) (.leaf 13)))))

theorem certificate06_root10111_checked :
    certificate06_root10111.fastVerify [14,15,18,19] [12,11,10,0] = true := rfl

def certificate06_root1011 : OrbitCertificate :=
  (.split certificate06_root10110 certificate06_root10111)

theorem certificate06_root1011_checked :
    certificate06_root1011.fastVerify [12,14,15,18,19] [11,10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root10110_checked, certificate06_root10111_checked⟩

def certificate06_root101 : OrbitCertificate :=
  (.split certificate06_root1010 certificate06_root1011)

theorem certificate06_root101_checked :
    certificate06_root101.fastVerify [11,12,14,15,18,19] [10,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root1010_checked, certificate06_root1011_checked⟩

def certificate06_root10 : OrbitCertificate :=
  (.split certificate06_root100 certificate06_root101)

theorem certificate06_root10_checked :
    certificate06_root10.fastVerify [10,11,12,14,15,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root100_checked, certificate06_root101_checked⟩

def certificate06_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 8) (.leaf 11)) (.split (.leaf 10) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate06_root11000_checked :
    certificate06_root11000.fastVerify [14,15,18,19] [2,0] = true := rfl

def certificate06_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 6) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate06_root11001_checked :
    certificate06_root11001.fastVerify [14,15,18,19] [12,2,0] = true := rfl

def certificate06_root1100 : OrbitCertificate :=
  (.split certificate06_root11000 certificate06_root11001)

theorem certificate06_root1100_checked :
    certificate06_root1100.fastVerify [12,14,15,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root11000_checked, certificate06_root11001_checked⟩

def certificate06_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 16) (.leaf 16)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 8) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate06_root11010_checked :
    certificate06_root11010.fastVerify [14,15,18,19] [11,2,0] = true := rfl

def certificate06_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 16)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 16)))))

theorem certificate06_root11011_checked :
    certificate06_root11011.fastVerify [14,15,18,19] [12,11,2,0] = true := rfl

def certificate06_root1101 : OrbitCertificate :=
  (.split certificate06_root11010 certificate06_root11011)

theorem certificate06_root1101_checked :
    certificate06_root1101.fastVerify [12,14,15,18,19] [11,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root11010_checked, certificate06_root11011_checked⟩

def certificate06_root110 : OrbitCertificate :=
  (.split certificate06_root1100 certificate06_root1101)

theorem certificate06_root110_checked :
    certificate06_root110.fastVerify [11,12,14,15,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root1100_checked, certificate06_root1101_checked⟩

def certificate06_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 3))) (.split (.split (.leaf 6) (.leaf 3)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 9))) (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate06_root11100_checked :
    certificate06_root11100.fastVerify [14,15,18,19] [10,2,0] = true := rfl

def certificate06_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 1)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 9) (.leaf 9)))))

theorem certificate06_root11101_checked :
    certificate06_root11101.fastVerify [14,15,18,19] [12,10,2,0] = true := rfl

def certificate06_root1110 : OrbitCertificate :=
  (.split certificate06_root11100 certificate06_root11101)

theorem certificate06_root1110_checked :
    certificate06_root1110.fastVerify [12,14,15,18,19] [10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root11100_checked, certificate06_root11101_checked⟩

def certificate06_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 8) (.leaf 1))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 15)))))

theorem certificate06_root11110_checked :
    certificate06_root11110.fastVerify [14,15,18,19] [11,10,2,0] = true := rfl

def certificate06_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 13)))) (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 13))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 14) (.leaf 13)))))

theorem certificate06_root11111_checked :
    certificate06_root11111.fastVerify [14,15,18,19] [12,11,10,2,0] = true := rfl

def certificate06_root1111 : OrbitCertificate :=
  (.split certificate06_root11110 certificate06_root11111)

theorem certificate06_root1111_checked :
    certificate06_root1111.fastVerify [12,14,15,18,19] [11,10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root11110_checked, certificate06_root11111_checked⟩

def certificate06_root111 : OrbitCertificate :=
  (.split certificate06_root1110 certificate06_root1111)

theorem certificate06_root111_checked :
    certificate06_root111.fastVerify [11,12,14,15,18,19] [10,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root1110_checked, certificate06_root1111_checked⟩

def certificate06_root11 : OrbitCertificate :=
  (.split certificate06_root110 certificate06_root111)

theorem certificate06_root11_checked :
    certificate06_root11.fastVerify [10,11,12,14,15,18,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root110_checked, certificate06_root111_checked⟩

def certificate06_root1 : OrbitCertificate :=
  (.split certificate06_root10 certificate06_root11)

theorem certificate06_root1_checked :
    certificate06_root1.fastVerify [2,10,11,12,14,15,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root10_checked, certificate06_root11_checked⟩

def certificate06_root : OrbitCertificate :=
  (.split certificate06_root0 certificate06_root1)

theorem certificate06_root_checked :
    certificate06_root.fastVerify [0,2,10,11,12,14,15,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate06_root0_checked, certificate06_root1_checked⟩

theorem covered_06 : ∀ C ∈ (box 6).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,2,10,11,12,14,15,18,19] [] certificate06_root
    certificate06_root_checked C
  have hs : C ⊆ ([0,2,10,11,12,14,15,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_06
