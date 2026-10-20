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

def certificate01_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00000_checked :
    certificate01_root00000.fastVerify [16,17,18,19] [] = true := rfl

def certificate01_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00001_checked :
    certificate01_root00001.fastVerify [16,17,18,19] [15] = true := rfl

def certificate01_root0000 : OrbitCertificate :=
  (.split certificate01_root00000 certificate01_root00001)

theorem certificate01_root0000_checked :
    certificate01_root0000.fastVerify [15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root00000_checked, certificate01_root00001_checked⟩

def certificate01_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00010_checked :
    certificate01_root00010.fastVerify [16,17,18,19] [14] = true := rfl

def certificate01_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00011_checked :
    certificate01_root00011.fastVerify [16,17,18,19] [15,14] = true := rfl

def certificate01_root0001 : OrbitCertificate :=
  (.split certificate01_root00010 certificate01_root00011)

theorem certificate01_root0001_checked :
    certificate01_root0001.fastVerify [15,16,17,18,19] [14] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root00010_checked, certificate01_root00011_checked⟩

def certificate01_root000 : OrbitCertificate :=
  (.split certificate01_root0000 certificate01_root0001)

theorem certificate01_root000_checked :
    certificate01_root000.fastVerify [14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root0000_checked, certificate01_root0001_checked⟩

def certificate01_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00100_checked :
    certificate01_root00100.fastVerify [16,17,18,19] [13] = true := rfl

def certificate01_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00101_checked :
    certificate01_root00101.fastVerify [16,17,18,19] [15,13] = true := rfl

def certificate01_root0010 : OrbitCertificate :=
  (.split certificate01_root00100 certificate01_root00101)

theorem certificate01_root0010_checked :
    certificate01_root0010.fastVerify [15,16,17,18,19] [13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root00100_checked, certificate01_root00101_checked⟩

def certificate01_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00110_checked :
    certificate01_root00110.fastVerify [16,17,18,19] [14,13] = true := rfl

def certificate01_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root00111_checked :
    certificate01_root00111.fastVerify [16,17,18,19] [15,14,13] = true := rfl

def certificate01_root0011 : OrbitCertificate :=
  (.split certificate01_root00110 certificate01_root00111)

theorem certificate01_root0011_checked :
    certificate01_root0011.fastVerify [15,16,17,18,19] [14,13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root00110_checked, certificate01_root00111_checked⟩

def certificate01_root001 : OrbitCertificate :=
  (.split certificate01_root0010 certificate01_root0011)

theorem certificate01_root001_checked :
    certificate01_root001.fastVerify [14,15,16,17,18,19] [13] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root0010_checked, certificate01_root0011_checked⟩

def certificate01_root00 : OrbitCertificate :=
  (.split certificate01_root000 certificate01_root001)

theorem certificate01_root00_checked :
    certificate01_root00.fastVerify [13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root000_checked, certificate01_root001_checked⟩

def certificate01_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 5) (.leaf 9))) (.split (.split (.leaf 4) (.leaf 9)) (.split (.leaf 8) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 8) (.leaf 5))) (.split (.split (.leaf 8) (.leaf 4)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root01000_checked :
    certificate01_root01000.fastVerify [16,17,18,19] [1] = true := rfl

def certificate01_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 18) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 18)) (.split (.leaf 18) (.leaf 11)))))

theorem certificate01_root01001_checked :
    certificate01_root01001.fastVerify [16,17,18,19] [15,1] = true := rfl

def certificate01_root0100 : OrbitCertificate :=
  (.split certificate01_root01000 certificate01_root01001)

theorem certificate01_root0100_checked :
    certificate01_root0100.fastVerify [15,16,17,18,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root01000_checked, certificate01_root01001_checked⟩

def certificate01_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 8) (.leaf 9)) (.split (.leaf 8) (.leaf 9)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 8) (.leaf 19))) (.split (.split (.leaf 8) (.leaf 18)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root01010_checked :
    certificate01_root01010.fastVerify [16,17,18,19] [14,1] = true := rfl

def certificate01_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 13) (.leaf 13)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 18) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 18)) (.split (.leaf 18) (.leaf 11)))))

theorem certificate01_root01011_checked :
    certificate01_root01011.fastVerify [16,17,18,19] [15,14,1] = true := rfl

def certificate01_root0101 : OrbitCertificate :=
  (.split certificate01_root01010 certificate01_root01011)

theorem certificate01_root0101_checked :
    certificate01_root0101.fastVerify [15,16,17,18,19] [14,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root01010_checked, certificate01_root01011_checked⟩

def certificate01_root010 : OrbitCertificate :=
  (.split certificate01_root0100 certificate01_root0101)

theorem certificate01_root010_checked :
    certificate01_root010.fastVerify [14,15,16,17,18,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root0100_checked, certificate01_root0101_checked⟩

def certificate01_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 13)) (.split (.leaf 8) (.leaf 19))) (.split (.split (.leaf 8) (.leaf 19)) (.split (.leaf 8) (.leaf 19)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 8) (.leaf 19))) (.split (.split (.leaf 8) (.leaf 18)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root01100_checked :
    certificate01_root01100.fastVerify [16,17,18,19] [13,1] = true := rfl

def certificate01_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 19)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 18) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 18)) (.split (.leaf 18) (.leaf 18)))))

theorem certificate01_root01101_checked :
    certificate01_root01101.fastVerify [16,17,18,19] [15,13,1] = true := rfl

def certificate01_root0110 : OrbitCertificate :=
  (.split certificate01_root01100 certificate01_root01101)

theorem certificate01_root0110_checked :
    certificate01_root0110.fastVerify [15,16,17,18,19] [13,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root01100_checked, certificate01_root01101_checked⟩

def certificate01_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 12) (.leaf 19)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 8) (.leaf 19)) (.split (.leaf 8) (.leaf 19)))) (.split (.split (.split (.leaf 12) (.leaf 18)) (.split (.leaf 8) (.leaf 19))) (.split (.split (.leaf 8) (.leaf 18)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root01110_checked :
    certificate01_root01110.fastVerify [16,17,18,19] [14,13,1] = true := rfl

def certificate01_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 19) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 19)) (.split (.leaf 18) (.leaf 19)))) (.split (.split (.split (.leaf 18) (.leaf 18)) (.split (.leaf 18) (.leaf 19))) (.split (.split (.leaf 18) (.leaf 18)) (.split (.leaf 18) (.leaf 18)))))

theorem certificate01_root01111_checked :
    certificate01_root01111.fastVerify [16,17,18,19] [15,14,13,1] = true := rfl

def certificate01_root0111 : OrbitCertificate :=
  (.split certificate01_root01110 certificate01_root01111)

theorem certificate01_root0111_checked :
    certificate01_root0111.fastVerify [15,16,17,18,19] [14,13,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root01110_checked, certificate01_root01111_checked⟩

def certificate01_root011 : OrbitCertificate :=
  (.split certificate01_root0110 certificate01_root0111)

theorem certificate01_root011_checked :
    certificate01_root011.fastVerify [14,15,16,17,18,19] [13,1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root0110_checked, certificate01_root0111_checked⟩

def certificate01_root01 : OrbitCertificate :=
  (.split certificate01_root010 certificate01_root011)

theorem certificate01_root01_checked :
    certificate01_root01.fastVerify [13,14,15,16,17,18,19] [1] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root010_checked, certificate01_root011_checked⟩

def certificate01_root0 : OrbitCertificate :=
  (.split certificate01_root00 certificate01_root01)

theorem certificate01_root0_checked :
    certificate01_root0.fastVerify [1,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root00_checked, certificate01_root01_checked⟩

def certificate01_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate01_root10000_checked :
    certificate01_root10000.fastVerify [16,17,18,19] [0] = true := rfl

def certificate01_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate01_root10001_checked :
    certificate01_root10001.fastVerify [16,17,18,19] [15,0] = true := rfl

def certificate01_root1000 : OrbitCertificate :=
  (.split certificate01_root10000 certificate01_root10001)

theorem certificate01_root1000_checked :
    certificate01_root1000.fastVerify [15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root10000_checked, certificate01_root10001_checked⟩

def certificate01_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 10) (.leaf 11)) (.split (.leaf 10) (.leaf 11)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 17))) (.split (.split (.leaf 10) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate01_root10010_checked :
    certificate01_root10010.fastVerify [16,17,18,19] [14,0] = true := rfl

def certificate01_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))) (.split (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 17) (.leaf 17)) (.split (.leaf 17) (.leaf 17)))))

theorem certificate01_root10011_checked :
    certificate01_root10011.fastVerify [16,17,18,19] [15,14,0] = true := rfl

def certificate01_root1001 : OrbitCertificate :=
  (.split certificate01_root10010 certificate01_root10011)

theorem certificate01_root1001_checked :
    certificate01_root1001.fastVerify [15,16,17,18,19] [14,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root10010_checked, certificate01_root10011_checked⟩

def certificate01_root100 : OrbitCertificate :=
  (.split certificate01_root1000 certificate01_root1001)

theorem certificate01_root100_checked :
    certificate01_root100.fastVerify [14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root1000_checked, certificate01_root1001_checked⟩

def certificate01_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 0) (.leaf 10)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate01_root10100_checked :
    certificate01_root10100.fastVerify [16,17,18,19] [13,0] = true := rfl

def certificate01_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate01_root10101_checked :
    certificate01_root10101.fastVerify [16,17,18,19] [15,13,0] = true := rfl

def certificate01_root1010 : OrbitCertificate :=
  (.split certificate01_root10100 certificate01_root10101)

theorem certificate01_root1010_checked :
    certificate01_root1010.fastVerify [15,16,17,18,19] [13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root10100_checked, certificate01_root10101_checked⟩

def certificate01_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))) (.split (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16))) (.split (.split (.leaf 8) (.leaf 16)) (.split (.leaf 10) (.leaf 16)))))

theorem certificate01_root10110_checked :
    certificate01_root10110.fastVerify [16,17,18,19] [14,13,0] = true := rfl

def certificate01_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 17) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 17)) (.split (.leaf 16) (.leaf 17)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 16) (.leaf 17))) (.split (.split (.leaf 16) (.leaf 16)) (.split (.leaf 16) (.leaf 16)))))

theorem certificate01_root10111_checked :
    certificate01_root10111.fastVerify [16,17,18,19] [15,14,13,0] = true := rfl

def certificate01_root1011 : OrbitCertificate :=
  (.split certificate01_root10110 certificate01_root10111)

theorem certificate01_root1011_checked :
    certificate01_root1011.fastVerify [15,16,17,18,19] [14,13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root10110_checked, certificate01_root10111_checked⟩

def certificate01_root101 : OrbitCertificate :=
  (.split certificate01_root1010 certificate01_root1011)

theorem certificate01_root101_checked :
    certificate01_root101.fastVerify [14,15,16,17,18,19] [13,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root1010_checked, certificate01_root1011_checked⟩

def certificate01_root10 : OrbitCertificate :=
  (.split certificate01_root100 certificate01_root101)

theorem certificate01_root10_checked :
    certificate01_root10.fastVerify [13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root100_checked, certificate01_root101_checked⟩

def certificate01_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 9)) (.split (.leaf 8) (.leaf 9)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 8) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root11000_checked :
    certificate01_root11000.fastVerify [16,17,18,19] [1,0] = true := rfl

def certificate01_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 6) (.leaf 5)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate01_root11001_checked :
    certificate01_root11001.fastVerify [16,17,18,19] [15,1,0] = true := rfl

def certificate01_root1100 : OrbitCertificate :=
  (.split certificate01_root11000 certificate01_root11001)

theorem certificate01_root1100_checked :
    certificate01_root1100.fastVerify [15,16,17,18,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root11000_checked, certificate01_root11001_checked⟩

def certificate01_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 8) (.leaf 9)) (.split (.leaf 8) (.leaf 9)))) (.split (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 11))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root11010_checked :
    certificate01_root11010.fastVerify [16,17,18,19] [14,1,0] = true := rfl

def certificate01_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 7) (.leaf 9)) (.split (.leaf 9) (.leaf 9))) (.split (.split (.leaf 9) (.leaf 9)) (.split (.leaf 9) (.leaf 9)))) (.split (.split (.split (.leaf 12) (.leaf 11)) (.split (.leaf 11) (.leaf 11))) (.split (.split (.leaf 11) (.leaf 11)) (.split (.leaf 11) (.leaf 11)))))

theorem certificate01_root11011_checked :
    certificate01_root11011.fastVerify [16,17,18,19] [15,14,1,0] = true := rfl

def certificate01_root1101 : OrbitCertificate :=
  (.split certificate01_root11010 certificate01_root11011)

theorem certificate01_root1101_checked :
    certificate01_root1101.fastVerify [15,16,17,18,19] [14,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root11010_checked, certificate01_root11011_checked⟩

def certificate01_root110 : OrbitCertificate :=
  (.split certificate01_root1100 certificate01_root1101)

theorem certificate01_root110_checked :
    certificate01_root110.fastVerify [14,15,16,17,18,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root1100_checked, certificate01_root1101_checked⟩

def certificate01_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 7)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root11100_checked :
    certificate01_root11100.fastVerify [16,17,18,19] [13,1,0] = true := rfl

def certificate01_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 7)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 13)))) (.split (.split (.split (.leaf 6) (.leaf 4)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate01_root11101_checked :
    certificate01_root11101.fastVerify [16,17,18,19] [15,13,1,0] = true := rfl

def certificate01_root1110 : OrbitCertificate :=
  (.split certificate01_root11100 certificate01_root11101)

theorem certificate01_root1110_checked :
    certificate01_root1110.fastVerify [15,16,17,18,19] [13,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root11100_checked, certificate01_root11101_checked⟩

def certificate01_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))) (.split (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10))) (.split (.split (.leaf 8) (.leaf 10)) (.split (.leaf 8) (.leaf 10)))))

theorem certificate01_root11110_checked :
    certificate01_root11110.fastVerify [16,17,18,19] [14,13,1,0] = true := rfl

def certificate01_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 6) (.leaf 13)) (.split (.leaf 13) (.leaf 13))) (.split (.split (.leaf 12) (.leaf 13)) (.split (.leaf 12) (.leaf 13)))) (.split (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 12) (.leaf 17))) (.split (.split (.leaf 12) (.leaf 16)) (.split (.leaf 12) (.leaf 16)))))

theorem certificate01_root11111_checked :
    certificate01_root11111.fastVerify [16,17,18,19] [15,14,13,1,0] = true := rfl

def certificate01_root1111 : OrbitCertificate :=
  (.split certificate01_root11110 certificate01_root11111)

theorem certificate01_root1111_checked :
    certificate01_root1111.fastVerify [15,16,17,18,19] [14,13,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root11110_checked, certificate01_root11111_checked⟩

def certificate01_root111 : OrbitCertificate :=
  (.split certificate01_root1110 certificate01_root1111)

theorem certificate01_root111_checked :
    certificate01_root111.fastVerify [14,15,16,17,18,19] [13,1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root1110_checked, certificate01_root1111_checked⟩

def certificate01_root11 : OrbitCertificate :=
  (.split certificate01_root110 certificate01_root111)

theorem certificate01_root11_checked :
    certificate01_root11.fastVerify [13,14,15,16,17,18,19] [1,0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root110_checked, certificate01_root111_checked⟩

def certificate01_root1 : OrbitCertificate :=
  (.split certificate01_root10 certificate01_root11)

theorem certificate01_root1_checked :
    certificate01_root1.fastVerify [1,13,14,15,16,17,18,19] [0] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root10_checked, certificate01_root11_checked⟩

def certificate01_root : OrbitCertificate :=
  (.split certificate01_root0 certificate01_root1)

theorem certificate01_root_checked :
    certificate01_root.fastVerify [0,1,13,14,15,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate01_root0_checked, certificate01_root1_checked⟩

theorem covered_01 : ∀ C ∈ (box 1).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [0,1,13,14,15,16,17,18,19] [] certificate01_root
    certificate01_root_checked C
  have hs : C ⊆ ([0,1,13,14,15,16,17,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_01
