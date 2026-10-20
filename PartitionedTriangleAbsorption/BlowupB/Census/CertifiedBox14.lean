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

def certificate14_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate14_root00000_checked :
    certificate14_root00000.fastVerify [13,15,16,19] [] = true := rfl

def certificate14_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 22) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00001_checked :
    certificate14_root00001.fastVerify [13,15,16,19] [7] = true := rfl

def certificate14_root0000 : OrbitCertificate :=
  (.split certificate14_root00000 certificate14_root00001)

theorem certificate14_root0000_checked :
    certificate14_root0000.fastVerify [7,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root00000_checked, certificate14_root00001_checked⟩

def certificate14_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 18) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 22)) (.split (.leaf 0) (.leaf 22))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 22)))))

theorem certificate14_root00010_checked :
    certificate14_root00010.fastVerify [13,15,16,19] [5] = true := rfl

def certificate14_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00011_checked :
    certificate14_root00011.fastVerify [13,15,16,19] [7,5] = true := rfl

def certificate14_root0001 : OrbitCertificate :=
  (.split certificate14_root00010 certificate14_root00011)

theorem certificate14_root0001_checked :
    certificate14_root0001.fastVerify [7,13,15,16,19] [5] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root00010_checked, certificate14_root00011_checked⟩

def certificate14_root000 : OrbitCertificate :=
  (.split certificate14_root0000 certificate14_root0001)

theorem certificate14_root000_checked :
    certificate14_root000.fastVerify [5,7,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root0000_checked, certificate14_root0001_checked⟩

def certificate14_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 11)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00100_checked :
    certificate14_root00100.fastVerify [13,15,16,19] [2] = true := rfl

def certificate14_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00101_checked :
    certificate14_root00101.fastVerify [13,15,16,19] [7,2] = true := rfl

def certificate14_root0010 : OrbitCertificate :=
  (.split certificate14_root00100 certificate14_root00101)

theorem certificate14_root0010_checked :
    certificate14_root0010.fastVerify [7,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root00100_checked, certificate14_root00101_checked⟩

def certificate14_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 6) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00110_checked :
    certificate14_root00110.fastVerify [13,15,16,19] [5,2] = true := rfl

def certificate14_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 22) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 16)) (.split (.leaf 0) (.leaf 16))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate14_root00111_checked :
    certificate14_root00111.fastVerify [13,15,16,19] [7,5,2] = true := rfl

def certificate14_root0011 : OrbitCertificate :=
  (.split certificate14_root00110 certificate14_root00111)

theorem certificate14_root0011_checked :
    certificate14_root0011.fastVerify [7,13,15,16,19] [5,2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root00110_checked, certificate14_root00111_checked⟩

def certificate14_root001 : OrbitCertificate :=
  (.split certificate14_root0010 certificate14_root0011)

theorem certificate14_root001_checked :
    certificate14_root001.fastVerify [5,7,13,15,16,19] [2] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root0010_checked, certificate14_root0011_checked⟩

def certificate14_root00 : OrbitCertificate :=
  (.split certificate14_root000 certificate14_root001)

theorem certificate14_root00_checked :
    certificate14_root00.fastVerify [2,5,7,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root000_checked, certificate14_root001_checked⟩

def certificate14_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 12) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 0) (.leaf 18))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01000_checked :
    certificate14_root01000.fastVerify [13,15,16,19] [1] = true := rfl

def certificate14_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01001_checked :
    certificate14_root01001.fastVerify [13,15,16,19] [7,1] = true := rfl

def certificate14_root0100 : OrbitCertificate :=
  (.split certificate14_root01000 certificate14_root01001)

theorem certificate14_root0100_checked :
    certificate14_root0100.fastVerify [7,13,15,16,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root01000_checked, certificate14_root01001_checked⟩

def certificate14_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))) (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 0) (.leaf 18))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01010_checked :
    certificate14_root01010.fastVerify [13,15,16,19] [5,1] = true := rfl

def certificate14_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 12) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01011_checked :
    certificate14_root01011.fastVerify [13,15,16,19] [7,5,1] = true := rfl

def certificate14_root0101 : OrbitCertificate :=
  (.split certificate14_root01010 certificate14_root01011)

theorem certificate14_root0101_checked :
    certificate14_root0101.fastVerify [7,13,15,16,19] [5,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root01010_checked, certificate14_root01011_checked⟩

def certificate14_root010 : OrbitCertificate :=
  (.split certificate14_root0100 certificate14_root0101)

theorem certificate14_root010_checked :
    certificate14_root010.fastVerify [5,7,13,15,16,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root0100_checked, certificate14_root0101_checked⟩

def certificate14_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01100_checked :
    certificate14_root01100.fastVerify [13,15,16,19] [2,1] = true := rfl

def certificate14_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01101_checked :
    certificate14_root01101.fastVerify [13,15,16,19] [7,2,1] = true := rfl

def certificate14_root0110 : OrbitCertificate :=
  (.split certificate14_root01100 certificate14_root01101)

theorem certificate14_root0110_checked :
    certificate14_root0110.fastVerify [7,13,15,16,19] [2,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root01100_checked, certificate14_root01101_checked⟩

def certificate14_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01110_checked :
    certificate14_root01110.fastVerify [13,15,16,19] [5,2,1] = true := rfl

def certificate14_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 18)))))

theorem certificate14_root01111_checked :
    certificate14_root01111.fastVerify [13,15,16,19] [7,5,2,1] = true := rfl

def certificate14_root0111 : OrbitCertificate :=
  (.split certificate14_root01110 certificate14_root01111)

theorem certificate14_root0111_checked :
    certificate14_root0111.fastVerify [7,13,15,16,19] [5,2,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root01110_checked, certificate14_root01111_checked⟩

def certificate14_root011 : OrbitCertificate :=
  (.split certificate14_root0110 certificate14_root0111)

theorem certificate14_root011_checked :
    certificate14_root011.fastVerify [5,7,13,15,16,19] [2,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root0110_checked, certificate14_root0111_checked⟩

def certificate14_root01 : OrbitCertificate :=
  (.split certificate14_root010 certificate14_root011)

theorem certificate14_root01_checked :
    certificate14_root01.fastVerify [2,5,7,13,15,16,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root010_checked, certificate14_root011_checked⟩

def certificate14_root0 : OrbitCertificate :=
  (.split certificate14_root00 certificate14_root01)

theorem certificate14_root0_checked :
    certificate14_root0.fastVerify [1,2,5,7,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root00_checked, certificate14_root01_checked⟩

def certificate14_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate14_root10000_checked :
    certificate14_root10000.fastVerify [13,15,16,19] [0] = true := rfl

def certificate14_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 17) (.leaf 17)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate14_root10001_checked :
    certificate14_root10001.fastVerify [13,15,16,19] [7,0] = true := rfl

def certificate14_root1000 : OrbitCertificate :=
  (.split certificate14_root10000 certificate14_root10001)

theorem certificate14_root1000_checked :
    certificate14_root1000.fastVerify [7,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root10000_checked, certificate14_root10001_checked⟩

def certificate14_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate14_root10010_checked :
    certificate14_root10010.fastVerify [13,15,16,19] [5,0] = true := rfl

def certificate14_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate14_root10011_checked :
    certificate14_root10011.fastVerify [13,15,16,19] [7,5,0] = true := rfl

def certificate14_root1001 : OrbitCertificate :=
  (.split certificate14_root10010 certificate14_root10011)

theorem certificate14_root1001_checked :
    certificate14_root1001.fastVerify [7,13,15,16,19] [5,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root10010_checked, certificate14_root10011_checked⟩

def certificate14_root100 : OrbitCertificate :=
  (.split certificate14_root1000 certificate14_root1001)

theorem certificate14_root100_checked :
    certificate14_root100.fastVerify [5,7,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root1000_checked, certificate14_root1001_checked⟩

def certificate14_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate14_root10100_checked :
    certificate14_root10100.fastVerify [13,15,16,19] [2,0] = true := rfl

def certificate14_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate14_root10101_checked :
    certificate14_root10101.fastVerify [13,15,16,19] [7,2,0] = true := rfl

def certificate14_root1010 : OrbitCertificate :=
  (.split certificate14_root10100 certificate14_root10101)

theorem certificate14_root1010_checked :
    certificate14_root1010.fastVerify [7,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root10100_checked, certificate14_root10101_checked⟩

def certificate14_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 6) (.leaf 16)))))

theorem certificate14_root10110_checked :
    certificate14_root10110.fastVerify [13,15,16,19] [5,2,0] = true := rfl

def certificate14_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate14_root10111_checked :
    certificate14_root10111.fastVerify [13,15,16,19] [7,5,2,0] = true := rfl

def certificate14_root1011 : OrbitCertificate :=
  (.split certificate14_root10110 certificate14_root10111)

theorem certificate14_root1011_checked :
    certificate14_root1011.fastVerify [7,13,15,16,19] [5,2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root10110_checked, certificate14_root10111_checked⟩

def certificate14_root101 : OrbitCertificate :=
  (.split certificate14_root1010 certificate14_root1011)

theorem certificate14_root101_checked :
    certificate14_root101.fastVerify [5,7,13,15,16,19] [2,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root1010_checked, certificate14_root1011_checked⟩

def certificate14_root10 : OrbitCertificate :=
  (.split certificate14_root100 certificate14_root101)

theorem certificate14_root10_checked :
    certificate14_root10.fastVerify [2,5,7,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root100_checked, certificate14_root101_checked⟩

def certificate14_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11000_checked :
    certificate14_root11000.fastVerify [13,15,16,19] [1,0] = true := rfl

def certificate14_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 10)))))

theorem certificate14_root11001_checked :
    certificate14_root11001.fastVerify [13,15,16,19] [7,1,0] = true := rfl

def certificate14_root1100 : OrbitCertificate :=
  (.split certificate14_root11000 certificate14_root11001)

theorem certificate14_root1100_checked :
    certificate14_root1100.fastVerify [7,13,15,16,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root11000_checked, certificate14_root11001_checked⟩

def certificate14_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 7) (.leaf 3)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11010_checked :
    certificate14_root11010.fastVerify [13,15,16,19] [5,1,0] = true := rfl

def certificate14_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 12) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 10))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 12) (.leaf 10)))))

theorem certificate14_root11011_checked :
    certificate14_root11011.fastVerify [13,15,16,19] [7,5,1,0] = true := rfl

def certificate14_root1101 : OrbitCertificate :=
  (.split certificate14_root11010 certificate14_root11011)

theorem certificate14_root1101_checked :
    certificate14_root1101.fastVerify [7,13,15,16,19] [5,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root11010_checked, certificate14_root11011_checked⟩

def certificate14_root110 : OrbitCertificate :=
  (.split certificate14_root1100 certificate14_root1101)

theorem certificate14_root110_checked :
    certificate14_root110.fastVerify [5,7,13,15,16,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root1100_checked, certificate14_root1101_checked⟩

def certificate14_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11100_checked :
    certificate14_root11100.fastVerify [13,15,16,19] [2,1,0] = true := rfl

def certificate14_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11101_checked :
    certificate14_root11101.fastVerify [13,15,16,19] [7,2,1,0] = true := rfl

def certificate14_root1110 : OrbitCertificate :=
  (.split certificate14_root11100 certificate14_root11101)

theorem certificate14_root1110_checked :
    certificate14_root1110.fastVerify [7,13,15,16,19] [2,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root11100_checked, certificate14_root11101_checked⟩

def certificate14_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 6) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11110_checked :
    certificate14_root11110.fastVerify [13,15,16,19] [5,2,1,0] = true := rfl

def certificate14_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 5)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 5) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 0) (.leaf 4))) (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 6) (.leaf 4)))))

theorem certificate14_root11111_checked :
    certificate14_root11111.fastVerify [13,15,16,19] [7,5,2,1,0] = true := rfl

def certificate14_root1111 : OrbitCertificate :=
  (.split certificate14_root11110 certificate14_root11111)

theorem certificate14_root1111_checked :
    certificate14_root1111.fastVerify [7,13,15,16,19] [5,2,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root11110_checked, certificate14_root11111_checked⟩

def certificate14_root111 : OrbitCertificate :=
  (.split certificate14_root1110 certificate14_root1111)

theorem certificate14_root111_checked :
    certificate14_root111.fastVerify [5,7,13,15,16,19] [2,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root1110_checked, certificate14_root1111_checked⟩

def certificate14_root11 : OrbitCertificate :=
  (.split certificate14_root110 certificate14_root111)

theorem certificate14_root11_checked :
    certificate14_root11.fastVerify [2,5,7,13,15,16,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root110_checked, certificate14_root111_checked⟩

def certificate14_root1 : OrbitCertificate :=
  (.split certificate14_root10 certificate14_root11)

theorem certificate14_root1_checked :
    certificate14_root1.fastVerify [1,2,5,7,13,15,16,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root10_checked, certificate14_root11_checked⟩

def certificate14_root : OrbitCertificate :=
  (.split certificate14_root0 certificate14_root1)

theorem certificate14_root_checked :
    certificate14_root.fastVerify [0,1,2,5,7,13,15,16,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate14_root0_checked, certificate14_root1_checked⟩

theorem covered_14 : ∀ C ∈ (box 14).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,1,2,5,7,13,15,16,19] [] certificate14_root
    certificate14_root_checked C
  have hs : C ⊆ ([0,1,2,5,7,13,15,16,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_14
