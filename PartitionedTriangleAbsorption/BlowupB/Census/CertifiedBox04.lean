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

def certificate04_root00000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root00000_checked :
    certificate04_root00000.fastVerify [16,17,18,19] [] = true := rfl

def certificate04_root00001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root00001_checked :
    certificate04_root00001.fastVerify [16,17,18,19] [10] = true := rfl

def certificate04_root0000 : OrbitCertificate :=
  (.split certificate04_root00000 certificate04_root00001)

theorem certificate04_root0000_checked :
    certificate04_root0000.fastVerify [10,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root00000_checked, certificate04_root00001_checked⟩

def certificate04_root00010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root00010_checked :
    certificate04_root00010.fastVerify [16,17,18,19] [9] = true := rfl

def certificate04_root00011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate04_root00011_checked :
    certificate04_root00011.fastVerify [16,17,18,19] [10,9] = true := rfl

def certificate04_root0001 : OrbitCertificate :=
  (.split certificate04_root00010 certificate04_root00011)

theorem certificate04_root0001_checked :
    certificate04_root0001.fastVerify [10,16,17,18,19] [9] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root00010_checked, certificate04_root00011_checked⟩

def certificate04_root000 : OrbitCertificate :=
  (.split certificate04_root0000 certificate04_root0001)

theorem certificate04_root000_checked :
    certificate04_root000.fastVerify [9,10,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root0000_checked, certificate04_root0001_checked⟩

def certificate04_root00100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root00100_checked :
    certificate04_root00100.fastVerify [16,17,18,19] [8] = true := rfl

def certificate04_root00101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 20) (.leaf 21)) (.split (.leaf 20) (.leaf 21)))) (.split (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 23))) (.split (.split (.leaf 20) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate04_root00101_checked :
    certificate04_root00101.fastVerify [16,17,18,19] [10,8] = true := rfl

def certificate04_root0010 : OrbitCertificate :=
  (.split certificate04_root00100 certificate04_root00101)

theorem certificate04_root0010_checked :
    certificate04_root0010.fastVerify [10,16,17,18,19] [8] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root00100_checked, certificate04_root00101_checked⟩

def certificate04_root00110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root00110_checked :
    certificate04_root00110.fastVerify [16,17,18,19] [9,8] = true := rfl

def certificate04_root00111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))) (.split (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 23) (.leaf 23)) (.split (.leaf 23) (.leaf 23)))))

theorem certificate04_root00111_checked :
    certificate04_root00111.fastVerify [16,17,18,19] [10,9,8] = true := rfl

def certificate04_root0011 : OrbitCertificate :=
  (.split certificate04_root00110 certificate04_root00111)

theorem certificate04_root0011_checked :
    certificate04_root0011.fastVerify [10,16,17,18,19] [9,8] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root00110_checked, certificate04_root00111_checked⟩

def certificate04_root001 : OrbitCertificate :=
  (.split certificate04_root0010 certificate04_root0011)

theorem certificate04_root001_checked :
    certificate04_root001.fastVerify [9,10,16,17,18,19] [8] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root0010_checked, certificate04_root0011_checked⟩

def certificate04_root00 : OrbitCertificate :=
  (.split certificate04_root000 certificate04_root001)

theorem certificate04_root00_checked :
    certificate04_root00.fastVerify [8,9,10,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root000_checked, certificate04_root001_checked⟩

def certificate04_root01000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root01000_checked :
    certificate04_root01000.fastVerify [16,17,18,19] [7] = true := rfl

def certificate04_root01001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 0) (.leaf 20)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate04_root01001_checked :
    certificate04_root01001.fastVerify [16,17,18,19] [10,7] = true := rfl

def certificate04_root0100 : OrbitCertificate :=
  (.split certificate04_root01000 certificate04_root01001)

theorem certificate04_root0100_checked :
    certificate04_root0100.fastVerify [10,16,17,18,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root01000_checked, certificate04_root01001_checked⟩

def certificate04_root01010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root01010_checked :
    certificate04_root01010.fastVerify [16,17,18,19] [9,7] = true := rfl

def certificate04_root01011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 22) (.leaf 23)) (.split (.leaf 22) (.leaf 23)))) (.split (.split (.split (.leaf 2) (.leaf 22)) (.split (.leaf 22) (.leaf 23))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate04_root01011_checked :
    certificate04_root01011.fastVerify [16,17,18,19] [10,9,7] = true := rfl

def certificate04_root0101 : OrbitCertificate :=
  (.split certificate04_root01010 certificate04_root01011)

theorem certificate04_root0101_checked :
    certificate04_root0101.fastVerify [10,16,17,18,19] [9,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root01010_checked, certificate04_root01011_checked⟩

def certificate04_root010 : OrbitCertificate :=
  (.split certificate04_root0100 certificate04_root0101)

theorem certificate04_root010_checked :
    certificate04_root010.fastVerify [9,10,16,17,18,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root0100_checked, certificate04_root0101_checked⟩

def certificate04_root01100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root01100_checked :
    certificate04_root01100.fastVerify [16,17,18,19] [8,7] = true := rfl

def certificate04_root01101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))) (.split (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22))) (.split (.split (.leaf 14) (.leaf 22)) (.split (.leaf 20) (.leaf 22)))))

theorem certificate04_root01101_checked :
    certificate04_root01101.fastVerify [16,17,18,19] [10,8,7] = true := rfl

def certificate04_root0110 : OrbitCertificate :=
  (.split certificate04_root01100 certificate04_root01101)

theorem certificate04_root0110_checked :
    certificate04_root0110.fastVerify [10,16,17,18,19] [8,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root01100_checked, certificate04_root01101_checked⟩

def certificate04_root01110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))) (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0))) (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 0) (.leaf 0)))))

theorem certificate04_root01110_checked :
    certificate04_root01110.fastVerify [16,17,18,19] [9,8,7] = true := rfl

def certificate04_root01111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 23) (.leaf 23))) (.split (.split (.leaf 22) (.leaf 23)) (.split (.leaf 22) (.leaf 23)))) (.split (.split (.split (.leaf 2) (.leaf 22)) (.split (.leaf 22) (.leaf 23))) (.split (.split (.leaf 22) (.leaf 22)) (.split (.leaf 22) (.leaf 22)))))

theorem certificate04_root01111_checked :
    certificate04_root01111.fastVerify [16,17,18,19] [10,9,8,7] = true := rfl

def certificate04_root0111 : OrbitCertificate :=
  (.split certificate04_root01110 certificate04_root01111)

theorem certificate04_root0111_checked :
    certificate04_root0111.fastVerify [10,16,17,18,19] [9,8,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root01110_checked, certificate04_root01111_checked⟩

def certificate04_root011 : OrbitCertificate :=
  (.split certificate04_root0110 certificate04_root0111)

theorem certificate04_root011_checked :
    certificate04_root011.fastVerify [9,10,16,17,18,19] [8,7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root0110_checked, certificate04_root0111_checked⟩

def certificate04_root01 : OrbitCertificate :=
  (.split certificate04_root010 certificate04_root011)

theorem certificate04_root01_checked :
    certificate04_root01.fastVerify [8,9,10,16,17,18,19] [7] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root010_checked, certificate04_root011_checked⟩

def certificate04_root0 : OrbitCertificate :=
  (.split certificate04_root00 certificate04_root01)

theorem certificate04_root0_checked :
    certificate04_root0.fastVerify [7,8,9,10,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root00_checked, certificate04_root01_checked⟩

def certificate04_root10000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 14) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root10000_checked :
    certificate04_root10000.fastVerify [16,17,18,19] [4] = true := rfl

def certificate04_root10001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 19) (.leaf 15))) (.split (.split (.leaf 18) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 14) (.leaf 19))) (.split (.split (.leaf 14) (.leaf 18)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root10001_checked :
    certificate04_root10001.fastVerify [16,17,18,19] [10,4] = true := rfl

def certificate04_root1000 : OrbitCertificate :=
  (.split certificate04_root10000 certificate04_root10001)

theorem certificate04_root1000_checked :
    certificate04_root1000.fastVerify [10,16,17,18,19] [4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root10000_checked, certificate04_root10001_checked⟩

def certificate04_root10010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 2) (.leaf 5)) (.split (.leaf 4) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 4) (.leaf 21)))))

theorem certificate04_root10010_checked :
    certificate04_root10010.fastVerify [16,17,18,19] [9,4] = true := rfl

def certificate04_root10011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 0)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 0) (.leaf 19)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate04_root10011_checked :
    certificate04_root10011.fastVerify [16,17,18,19] [10,9,4] = true := rfl

def certificate04_root1001 : OrbitCertificate :=
  (.split certificate04_root10010 certificate04_root10011)

theorem certificate04_root1001_checked :
    certificate04_root1001.fastVerify [10,16,17,18,19] [9,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root10010_checked, certificate04_root10011_checked⟩

def certificate04_root100 : OrbitCertificate :=
  (.split certificate04_root1000 certificate04_root1001)

theorem certificate04_root100_checked :
    certificate04_root100.fastVerify [9,10,16,17,18,19] [4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root1000_checked, certificate04_root1001_checked⟩

def certificate04_root10100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 3)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 14) (.leaf 5))) (.split (.split (.leaf 14) (.leaf 4)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root10100_checked :
    certificate04_root10100.fastVerify [16,17,18,19] [8,4] = true := rfl

def certificate04_root10101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 14) (.leaf 15)) (.split (.leaf 14) (.leaf 15)))) (.split (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 21))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root10101_checked :
    certificate04_root10101.fastVerify [16,17,18,19] [10,8,4] = true := rfl

def certificate04_root1010 : OrbitCertificate :=
  (.split certificate04_root10100 certificate04_root10101)

theorem certificate04_root1010_checked :
    certificate04_root1010.fastVerify [10,16,17,18,19] [8,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root10100_checked, certificate04_root10101_checked⟩

def certificate04_root10110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 3) (.leaf 3)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 4) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 4) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 4) (.leaf 21)))))

theorem certificate04_root10110_checked :
    certificate04_root10110.fastVerify [16,17,18,19] [9,8,4] = true := rfl

def certificate04_root10111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 1) (.leaf 15)) (.split (.leaf 15) (.leaf 15))) (.split (.split (.leaf 15) (.leaf 15)) (.split (.leaf 15) (.leaf 15)))) (.split (.split (.split (.leaf 2) (.leaf 21)) (.split (.leaf 21) (.leaf 21))) (.split (.split (.leaf 21) (.leaf 21)) (.split (.leaf 21) (.leaf 21)))))

theorem certificate04_root10111_checked :
    certificate04_root10111.fastVerify [16,17,18,19] [10,9,8,4] = true := rfl

def certificate04_root1011 : OrbitCertificate :=
  (.split certificate04_root10110 certificate04_root10111)

theorem certificate04_root1011_checked :
    certificate04_root1011.fastVerify [10,16,17,18,19] [9,8,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root10110_checked, certificate04_root10111_checked⟩

def certificate04_root101 : OrbitCertificate :=
  (.split certificate04_root1010 certificate04_root1011)

theorem certificate04_root101_checked :
    certificate04_root101.fastVerify [9,10,16,17,18,19] [8,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root1010_checked, certificate04_root1011_checked⟩

def certificate04_root10 : OrbitCertificate :=
  (.split certificate04_root100 certificate04_root101)

theorem certificate04_root10_checked :
    certificate04_root10.fastVerify [8,9,10,16,17,18,19] [4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root100_checked, certificate04_root101_checked⟩

def certificate04_root11000 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 14) (.leaf 5))) (.split (.split (.leaf 14) (.leaf 5)) (.split (.leaf 14) (.leaf 5)))) (.split (.split (.split (.leaf 0) (.leaf 4)) (.split (.leaf 14) (.leaf 5))) (.split (.split (.leaf 14) (.leaf 4)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root11000_checked :
    certificate04_root11000.fastVerify [16,17,18,19] [7,4] = true := rfl

def certificate04_root11001 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root11001_checked :
    certificate04_root11001.fastVerify [16,17,18,19] [10,7,4] = true := rfl

def certificate04_root1100 : OrbitCertificate :=
  (.split certificate04_root11000 certificate04_root11001)

theorem certificate04_root1100_checked :
    certificate04_root1100.fastVerify [10,16,17,18,19] [7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root11000_checked, certificate04_root11001_checked⟩

def certificate04_root11010 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 4) (.leaf 5)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 4) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 4) (.leaf 4)))))

theorem certificate04_root11010_checked :
    certificate04_root11010.fastVerify [16,17,18,19] [9,7,4] = true := rfl

def certificate04_root11011 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 1)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 2) (.leaf 3)) (.split (.leaf 2) (.leaf 3)))) (.split (.split (.split (.leaf 0) (.leaf 18)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 2) (.leaf 22)) (.split (.leaf 2) (.leaf 22)))))

theorem certificate04_root11011_checked :
    certificate04_root11011.fastVerify [16,17,18,19] [10,9,7,4] = true := rfl

def certificate04_root1101 : OrbitCertificate :=
  (.split certificate04_root11010 certificate04_root11011)

theorem certificate04_root1101_checked :
    certificate04_root1101.fastVerify [10,16,17,18,19] [9,7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root11010_checked, certificate04_root11011_checked⟩

def certificate04_root110 : OrbitCertificate :=
  (.split certificate04_root1100 certificate04_root1101)

theorem certificate04_root110_checked :
    certificate04_root110.fastVerify [9,10,16,17,18,19] [7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root1100_checked, certificate04_root1101_checked⟩

def certificate04_root11100 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 2) (.leaf 5)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 14) (.leaf 5)) (.split (.leaf 14) (.leaf 5)))) (.split (.split (.split (.leaf 2) (.leaf 4)) (.split (.leaf 14) (.leaf 5))) (.split (.split (.leaf 14) (.leaf 4)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root11100_checked :
    certificate04_root11100.fastVerify [16,17,18,19] [8,7,4] = true := rfl

def certificate04_root11101 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))) (.split (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20))) (.split (.split (.leaf 14) (.leaf 20)) (.split (.leaf 14) (.leaf 20)))))

theorem certificate04_root11101_checked :
    certificate04_root11101.fastVerify [16,17,18,19] [10,8,7,4] = true := rfl

def certificate04_root1110 : OrbitCertificate :=
  (.split certificate04_root11100 certificate04_root11101)

theorem certificate04_root1110_checked :
    certificate04_root1110.fastVerify [10,16,17,18,19] [8,7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root11100_checked, certificate04_root11101_checked⟩

def certificate04_root11110 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 5) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 5)) (.split (.leaf 4) (.leaf 5)))) (.split (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 4) (.leaf 5))) (.split (.split (.leaf 4) (.leaf 4)) (.split (.leaf 4) (.leaf 4)))))

theorem certificate04_root11110_checked :
    certificate04_root11110.fastVerify [16,17,18,19] [9,8,7,4] = true := rfl

def certificate04_root11111 : OrbitCertificate :=
  (.split (.split (.split (.split (.leaf 0) (.leaf 3)) (.split (.leaf 3) (.leaf 3))) (.split (.split (.leaf 2) (.leaf 3)) (.split (.leaf 2) (.leaf 3)))) (.split (.split (.split (.leaf 2) (.leaf 22)) (.split (.leaf 2) (.leaf 23))) (.split (.split (.leaf 2) (.leaf 22)) (.split (.leaf 2) (.leaf 22)))))

theorem certificate04_root11111_checked :
    certificate04_root11111.fastVerify [16,17,18,19] [10,9,8,7,4] = true := rfl

def certificate04_root1111 : OrbitCertificate :=
  (.split certificate04_root11110 certificate04_root11111)

theorem certificate04_root1111_checked :
    certificate04_root1111.fastVerify [10,16,17,18,19] [9,8,7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root11110_checked, certificate04_root11111_checked⟩

def certificate04_root111 : OrbitCertificate :=
  (.split certificate04_root1110 certificate04_root1111)

theorem certificate04_root111_checked :
    certificate04_root111.fastVerify [9,10,16,17,18,19] [8,7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root1110_checked, certificate04_root1111_checked⟩

def certificate04_root11 : OrbitCertificate :=
  (.split certificate04_root110 certificate04_root111)

theorem certificate04_root11_checked :
    certificate04_root11.fastVerify [8,9,10,16,17,18,19] [7,4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root110_checked, certificate04_root111_checked⟩

def certificate04_root1 : OrbitCertificate :=
  (.split certificate04_root10 certificate04_root11)

theorem certificate04_root1_checked :
    certificate04_root1.fastVerify [7,8,9,10,16,17,18,19] [4] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root10_checked, certificate04_root11_checked⟩

def certificate04_root : OrbitCertificate :=
  (.split certificate04_root0 certificate04_root1)

theorem certificate04_root_checked :
    certificate04_root.fastVerify [4,7,8,9,10,16,17,18,19] [] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨certificate04_root0_checked, certificate04_root1_checked⟩

theorem covered_04 : ∀ C ∈ (box 4).powerset,
    UsesAll C → ∃ i : Fin 24, repMem (familyMask (actCode i C)) = true := by
  intro C hC hu
  have hh := OrbitCertificate.fastVerify_sound [4,7,8,9,10,16,17,18,19] [] certificate04_root
    certificate04_root_checked C
  have hs : C ⊆ ([4,7,8,9,10,16,17,18,19] : List (Fin 20)).toFinset :=
    Finset.mem_powerset.mp hC
  simpa only [List.toFinset_nil, Finset.empty_union] using
    hh hs (by simpa only [List.toFinset_nil, Finset.empty_union] using hu)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.covered_04
