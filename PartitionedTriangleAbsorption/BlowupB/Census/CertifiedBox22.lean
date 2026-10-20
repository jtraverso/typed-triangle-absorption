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

def certificate22_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate22_root00000_checked :
    certificate22_root00000.fastVerify [10,12,16,17] [] = true := rfl

def certificate22_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 15) (.leaf 21)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root00001_checked :
    certificate22_root00001.fastVerify [10,12,16,17] [8] = true := rfl

def certificate22_root0000 : OrbitCertificate :=
  (.split certificate22_root00000 certificate22_root00001)

theorem certificate22_root0000_checked :
    certificate22_root0000.fastVerify [8,10,12,16,17] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root00000_checked, certificate22_root00001_checked⟩

def certificate22_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 12) (.leaf 20)) (.split (.leaf 12) (.leaf 20)))))

theorem certificate22_root00010_checked :
    certificate22_root00010.fastVerify [10,12,16,17] [7] = true := rfl

def certificate22_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 14) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 20) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root00011_checked :
    certificate22_root00011.fastVerify [10,12,16,17] [8,7] = true := rfl

def certificate22_root0001 : OrbitCertificate :=
  (.split certificate22_root00010 certificate22_root00011)

theorem certificate22_root0001_checked :
    certificate22_root0001.fastVerify [8,10,12,16,17] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root00010_checked, certificate22_root00011_checked⟩

def certificate22_root000 : OrbitCertificate :=
  (.split certificate22_root0000 certificate22_root0001)

theorem certificate22_root000_checked :
    certificate22_root000.fastVerify [7,8,10,12,16,17] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root0000_checked, certificate22_root0001_checked⟩

def certificate22_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 0) (.leaf 23))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate22_root00100_checked :
    certificate22_root00100.fastVerify [10,12,16,17] [3] = true := rfl

def certificate22_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate22_root00101_checked :
    certificate22_root00101.fastVerify [10,12,16,17] [8,3] = true := rfl

def certificate22_root0010 : OrbitCertificate :=
  (.split certificate22_root00100 certificate22_root00101)

theorem certificate22_root0010_checked :
    certificate22_root0010.fastVerify [8,10,12,16,17] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root00100_checked, certificate22_root00101_checked⟩

def certificate22_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root00110_checked :
    certificate22_root00110.fastVerify [10,12,16,17] [7,3] = true := rfl

def certificate22_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 23)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root00111_checked :
    certificate22_root00111.fastVerify [10,12,16,17] [8,7,3] = true := rfl

def certificate22_root0011 : OrbitCertificate :=
  (.split certificate22_root00110 certificate22_root00111)

theorem certificate22_root0011_checked :
    certificate22_root0011.fastVerify [8,10,12,16,17] [7,3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root00110_checked, certificate22_root00111_checked⟩

def certificate22_root001 : OrbitCertificate :=
  (.split certificate22_root0010 certificate22_root0011)

theorem certificate22_root001_checked :
    certificate22_root001.fastVerify [7,8,10,12,16,17] [3] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root0010_checked, certificate22_root0011_checked⟩

def certificate22_root00 : OrbitCertificate :=
  (.split certificate22_root000 certificate22_root001)

theorem certificate22_root00_checked :
    certificate22_root00.fastVerify [3,7,8,10,12,16,17] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root000_checked, certificate22_root001_checked⟩

def certificate22_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 6) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root01000_checked :
    certificate22_root01000.fastVerify [10,12,16,17] [2] = true := rfl

def certificate22_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root01001_checked :
    certificate22_root01001.fastVerify [10,12,16,17] [8,2] = true := rfl

def certificate22_root0100 : OrbitCertificate :=
  (.split certificate22_root01000 certificate22_root01001)

theorem certificate22_root0100_checked :
    certificate22_root0100.fastVerify [8,10,12,16,17] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root01000_checked, certificate22_root01001_checked⟩

def certificate22_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 0) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root01010_checked :
    certificate22_root01010.fastVerify [10,12,16,17] [7,2] = true := rfl

def certificate22_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 14)) (.split (.leaf 14) (.leaf 14))) (.split (.split (.leaf 1) (.leaf 20)) (.split (.leaf 20) (.leaf 20)))))

theorem certificate22_root01011_checked :
    certificate22_root01011.fastVerify [10,12,16,17] [8,7,2] = true := rfl

def certificate22_root0101 : OrbitCertificate :=
  (.split certificate22_root01010 certificate22_root01011)

theorem certificate22_root0101_checked :
    certificate22_root0101.fastVerify [8,10,12,16,17] [7,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root01010_checked, certificate22_root01011_checked⟩

def certificate22_root010 : OrbitCertificate :=
  (.split certificate22_root0100 certificate22_root0101)

theorem certificate22_root010_checked :
    certificate22_root010.fastVerify [7,8,10,12,16,17] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root0100_checked, certificate22_root0101_checked⟩

def certificate22_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root01100_checked :
    certificate22_root01100.fastVerify [10,12,16,17] [3,2] = true := rfl

def certificate22_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root01101_checked :
    certificate22_root01101.fastVerify [10,12,16,17] [8,3,2] = true := rfl

def certificate22_root0110 : OrbitCertificate :=
  (.split certificate22_root01100 certificate22_root01101)

theorem certificate22_root0110_checked :
    certificate22_root0110.fastVerify [8,10,12,16,17] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root01100_checked, certificate22_root01101_checked⟩

def certificate22_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root01110_checked :
    certificate22_root01110.fastVerify [10,12,16,17] [7,3,2] = true := rfl

def certificate22_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 23)))))

theorem certificate22_root01111_checked :
    certificate22_root01111.fastVerify [10,12,16,17] [8,7,3,2] = true := rfl

def certificate22_root0111 : OrbitCertificate :=
  (.split certificate22_root01110 certificate22_root01111)

theorem certificate22_root0111_checked :
    certificate22_root0111.fastVerify [8,10,12,16,17] [7,3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root01110_checked, certificate22_root01111_checked⟩

def certificate22_root011 : OrbitCertificate :=
  (.split certificate22_root0110 certificate22_root0111)

theorem certificate22_root011_checked :
    certificate22_root011.fastVerify [7,8,10,12,16,17] [3,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root0110_checked, certificate22_root0111_checked⟩

def certificate22_root01 : OrbitCertificate :=
  (.split certificate22_root010 certificate22_root011)

theorem certificate22_root01_checked :
    certificate22_root01.fastVerify [3,7,8,10,12,16,17] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root010_checked, certificate22_root011_checked⟩

def certificate22_root0 : OrbitCertificate :=
  (.split certificate22_root00 certificate22_root01)

theorem certificate22_root0_checked :
    certificate22_root0.fastVerify [2,3,7,8,10,12,16,17] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root00_checked, certificate22_root01_checked⟩

def certificate22_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 6) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 6) (.leaf 12)))))

theorem certificate22_root10000_checked :
    certificate22_root10000.fastVerify [10,12,16,17] [0] = true := rfl

def certificate22_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 11)) (.split (.leaf 11) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 14)))))

theorem certificate22_root10001_checked :
    certificate22_root10001.fastVerify [10,12,16,17] [8,0] = true := rfl

def certificate22_root1000 : OrbitCertificate :=
  (.split certificate22_root10000 certificate22_root10001)

theorem certificate22_root1000_checked :
    certificate22_root1000.fastVerify [8,10,12,16,17] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root10000_checked, certificate22_root10001_checked⟩

def certificate22_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 12) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 12) (.leaf 14)))))

theorem certificate22_root10010_checked :
    certificate22_root10010.fastVerify [10,12,16,17] [7,0] = true := rfl

def certificate22_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 8) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 14) (.leaf 14)))))

theorem certificate22_root10011_checked :
    certificate22_root10011.fastVerify [10,12,16,17] [8,7,0] = true := rfl

def certificate22_root1001 : OrbitCertificate :=
  (.split certificate22_root10010 certificate22_root10011)

theorem certificate22_root1001_checked :
    certificate22_root1001.fastVerify [8,10,12,16,17] [7,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root10010_checked, certificate22_root10011_checked⟩

def certificate22_root100 : OrbitCertificate :=
  (.split certificate22_root1000 certificate22_root1001)

theorem certificate22_root100_checked :
    certificate22_root100.fastVerify [7,8,10,12,16,17] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root1000_checked, certificate22_root1001_checked⟩

def certificate22_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 0) (.leaf 2))) (.split (.split (.leaf 0) (.leaf 9)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate22_root10100_checked :
    certificate22_root10100.fastVerify [10,12,16,17] [3,0] = true := rfl

def certificate22_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 9) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 2)))))

theorem certificate22_root10101_checked :
    certificate22_root10101.fastVerify [10,12,16,17] [8,3,0] = true := rfl

def certificate22_root1010 : OrbitCertificate :=
  (.split certificate22_root10100 certificate22_root10101)

theorem certificate22_root1010_checked :
    certificate22_root1010.fastVerify [8,10,12,16,17] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root10100_checked, certificate22_root10101_checked⟩

def certificate22_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 8)))))

theorem certificate22_root10110_checked :
    certificate22_root10110.fastVerify [10,12,16,17] [7,3,0] = true := rfl

def certificate22_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 8)))))

theorem certificate22_root10111_checked :
    certificate22_root10111.fastVerify [10,12,16,17] [8,7,3,0] = true := rfl

def certificate22_root1011 : OrbitCertificate :=
  (.split certificate22_root10110 certificate22_root10111)

theorem certificate22_root1011_checked :
    certificate22_root1011.fastVerify [8,10,12,16,17] [7,3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root10110_checked, certificate22_root10111_checked⟩

def certificate22_root101 : OrbitCertificate :=
  (.split certificate22_root1010 certificate22_root1011)

theorem certificate22_root101_checked :
    certificate22_root101.fastVerify [7,8,10,12,16,17] [3,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root1010_checked, certificate22_root1011_checked⟩

def certificate22_root10 : OrbitCertificate :=
  (.split certificate22_root100 certificate22_root101)

theorem certificate22_root10_checked :
    certificate22_root10.fastVerify [3,7,8,10,12,16,17] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root100_checked, certificate22_root101_checked⟩

def certificate22_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 6) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 6) (.leaf 14)))))

theorem certificate22_root11000_checked :
    certificate22_root11000.fastVerify [10,12,16,17] [2,0] = true := rfl

def certificate22_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 0) (.leaf 14)))))

theorem certificate22_root11001_checked :
    certificate22_root11001.fastVerify [10,12,16,17] [8,2,0] = true := rfl

def certificate22_root1100 : OrbitCertificate :=
  (.split certificate22_root11000 certificate22_root11001)

theorem certificate22_root1100_checked :
    certificate22_root1100.fastVerify [8,10,12,16,17] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root11000_checked, certificate22_root11001_checked⟩

def certificate22_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 0) (.leaf 14)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 0) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 0) (.leaf 14)))))

theorem certificate22_root11010_checked :
    certificate22_root11010.fastVerify [10,12,16,17] [7,2,0] = true := rfl

def certificate22_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 0) (.leaf 14)))) (.split (.split (.split (.leaf 0) (.leaf 8)) (.split (.leaf 2) (.leaf 8))) (.split (.split (.leaf 1) (.leaf 14)) (.split (.leaf 0) (.leaf 14)))))

theorem certificate22_root11011_checked :
    certificate22_root11011.fastVerify [10,12,16,17] [8,7,2,0] = true := rfl

def certificate22_root1101 : OrbitCertificate :=
  (.split certificate22_root11010 certificate22_root11011)

theorem certificate22_root1101_checked :
    certificate22_root1101.fastVerify [8,10,12,16,17] [7,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root11010_checked, certificate22_root11011_checked⟩

def certificate22_root110 : OrbitCertificate :=
  (.split certificate22_root1100 certificate22_root1101)

theorem certificate22_root110_checked :
    certificate22_root110.fastVerify [7,8,10,12,16,17] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root1100_checked, certificate22_root1101_checked⟩

def certificate22_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 2)))))

theorem certificate22_root11100_checked :
    certificate22_root11100.fastVerify [10,12,16,17] [3,2,0] = true := rfl

def certificate22_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 2)))))

theorem certificate22_root11101_checked :
    certificate22_root11101.fastVerify [10,12,16,17] [8,3,2,0] = true := rfl

def certificate22_root1110 : OrbitCertificate :=
  (.split certificate22_root11100 certificate22_root11101)

theorem certificate22_root1110_checked :
    certificate22_root1110.fastVerify [8,10,12,16,17] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root11100_checked, certificate22_root11101_checked⟩

def certificate22_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 0) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 2)))))

theorem certificate22_root11110_checked :
    certificate22_root11110.fastVerify [10,12,16,17] [7,3,2,0] = true := rfl

def certificate22_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 1) (.leaf 11)) (.split (.leaf 0) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 2)) (.split (.leaf 2) (.leaf 2))) (.split (.split (.leaf 1) (.leaf 9)) (.split (.leaf 0) (.leaf 2)))))

theorem certificate22_root11111_checked :
    certificate22_root11111.fastVerify [10,12,16,17] [8,7,3,2,0] = true := rfl

def certificate22_root1111 : OrbitCertificate :=
  (.split certificate22_root11110 certificate22_root11111)

theorem certificate22_root1111_checked :
    certificate22_root1111.fastVerify [8,10,12,16,17] [7,3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root11110_checked, certificate22_root11111_checked⟩

def certificate22_root111 : OrbitCertificate :=
  (.split certificate22_root1110 certificate22_root1111)

theorem certificate22_root111_checked :
    certificate22_root111.fastVerify [7,8,10,12,16,17] [3,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root1110_checked, certificate22_root1111_checked⟩

def certificate22_root11 : OrbitCertificate :=
  (.split certificate22_root110 certificate22_root111)

theorem certificate22_root11_checked :
    certificate22_root11.fastVerify [3,7,8,10,12,16,17] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root110_checked, certificate22_root111_checked⟩

def certificate22_root1 : OrbitCertificate :=
  (.split certificate22_root10 certificate22_root11)

theorem certificate22_root1_checked :
    certificate22_root1.fastVerify [2,3,7,8,10,12,16,17] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root10_checked, certificate22_root11_checked⟩

def certificate22_root : OrbitCertificate :=
  (.split certificate22_root0 certificate22_root1)

theorem certificate22_root_checked :
    certificate22_root.fastVerify [0,2,3,7,8,10,12,16,17] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate22_root0_checked, certificate22_root1_checked⟩

theorem covered_22 : ∀ C ∈ (box 22).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,2,3,7,8,10,12,16,17] [] certificate22_root
    certificate22_root_checked C
  have hs : C ⊆ ([0,2,3,7,8,10,12,16,17] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_22
