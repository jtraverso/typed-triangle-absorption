/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Certificate

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem bitIndices_or (m n : ℕ) :
    Finset.equivBitIndices (m ||| n) =
      Finset.equivBitIndices m ∪ Finset.equivBitIndices n := by
  ext i
  simp [Finset.equivBitIndices, Nat.mem_bitIndices]

theorem familyMask_insert (i : Fin 20) (C : Finset (Fin 20)) :
    familyMask (insert i C) = 2 ^ i.val ||| familyMask C := by
  apply Finset.equivBitIndices.injective
  rw [bitIndices_or]
  simp only [familyMask, Equiv.apply_symm_apply, Finset.image_insert]
  simp [Finset.equivBitIndices]

def listActionMask (i : Fin 24) : List (Fin 20) → ℕ
  | [] => 0
  | a :: xs => 2 ^ (typeAction i a).val ||| listActionMask i xs

theorem listActionMask_correct (i : Fin 24) (xs : List (Fin 20)) :
    listActionMask i xs = familyMask (actCode i xs.toFinset) := by
  induction xs with
  | nil => simp [listActionMask, actCode, familyMask, Finset.equivBitIndices]
  | cons a xs ih =>
    simpa only [listActionMask, List.toFinset_cons, actCode, Finset.image_insert,
      familyMask_insert] using congrArg (fun m => 2 ^ (typeAction i a).val ||| m) ih

def labelBits : Fin 20 → ℕ :=
  ![1,3,5,9,3,7,11,5,13,9,2,6,10,6,14,10,4,12,12,8]

theorem labelBits_correct : ∀ i : Fin 20, ∀ a : Fin 4,
    (labelBits i).testBit a.val = true ↔ a ∈ tri i := by
  decide +kernel

def listUsesAll (xs : List (Fin 20)) : Bool :=
  (List.finRange 4).all fun a => xs.any fun i => (labelBits i).testBit a.val

theorem listUsesAll_correct (xs : List (Fin 20)) :
    listUsesAll xs = true ↔ UsesAll xs.toFinset := by
  simp [listUsesAll, UsesAll, List.all_eq_true, List.any_eq_true, labelBits_correct]

def OrbitCertificate.fastVerify : List (Fin 20) → List (Fin 20) → OrbitCertificate → Bool
  | [], P, .leaf i => !listUsesAll P || repMem (listActionMask i P)
  | a :: xs, P, .split l r => l.fastVerify xs P && r.fastVerify xs (a :: P)
  | _, _, _ => false

theorem OrbitCertificate.fastVerify_correct (xs P : List (Fin 20))
    (cert : OrbitCertificate) :
    cert.fastVerify xs P = cert.verify xs P.toFinset := by
  induction xs generalizing P cert with
  | nil =>
    cases cert with
    | leaf i =>
      have hb : listUsesAll P = decide (UsesAll P.toFinset) :=
        Bool.eq_iff_iff.mpr (by simpa using listUsesAll_correct P)
      simp only [fastVerify, verify, listActionMask_correct, hb]
    | split l r => rfl
  | cons a xs ih =>
    cases cert with
    | leaf i => rfl
    | split l r =>
      simp only [fastVerify, verify, ih, List.toFinset_cons]

theorem OrbitCertificate.fastVerify_sound (xs P : List (Fin 20))
    (cert : OrbitCertificate) (h : cert.fastVerify xs P = true) :
    ∀ C ⊆ xs.toFinset, UsesAll (P.toFinset ∪ C) →
      ∃ i : Fin 24, repMem (familyMask (actCode i (P.toFinset ∪ C))) = true := by
  apply cert.verify_sound xs P.toFinset
  rwa [← cert.fastVerify_correct xs P]

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.OrbitCertificate.fastVerify_sound
