/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Lookup

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

/-- Untrusted finite data: a permutation at each leaf of a subset tree. -/
inductive OrbitCertificate where
  | leaf (permutation : Fin 24)
  | split (absent present : OrbitCertificate)

def OrbitCertificate.verify : List (Fin 20) → Finset (Fin 20) → OrbitCertificate → Bool
  | [], P, .leaf i => !(decide (UsesAll P)) || repMem (familyMask (actCode i P))
  | a :: xs, P, .split l r => l.verify xs P && r.verify xs (insert a P)
  | _, _, _ => false

/-- The checker covers every subset, not just the enumerated positive examples. -/
theorem OrbitCertificate.verify_sound (xs : List (Fin 20))
    (P : Finset (Fin 20)) (cert : OrbitCertificate)
    (h : cert.verify xs P = true) :
    ∀ C ⊆ xs.toFinset, UsesAll (P ∪ C) →
      ∃ i : Fin 24, repMem (familyMask (actCode i (P ∪ C))) = true := by
  induction xs generalizing P cert with
  | nil =>
    intro C hC hu
    have hc : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro x hx
      simpa using hC hx)
    subst C
    simp only [Finset.union_empty] at hu ⊢
    cases cert with
    | leaf i =>
      refine ⟨i, ?_⟩
      simpa [verify, hu] using h
    | split l r => simp [verify] at h
  | cons a xs ih =>
    cases cert with
    | leaf i => simp [verify] at h
    | split l r =>
      have hlr := Bool.and_eq_true_iff.mp h
      intro C hC hu
      by_cases ha : a ∈ C
      · have he : C.erase a ⊆ xs.toFinset := by
          intro x hx
          have hc := hC (Finset.mem_of_mem_erase hx)
          simp only [List.toFinset_cons, Finset.mem_insert] at hc
          exact hc.resolve_left (Finset.ne_of_mem_erase hx)
        have heq : insert a P ∪ C.erase a = P ∪ C := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
          by_cases hx : x = a <;> simp_all
        have hh := ih (insert a P) r hlr.2 (C.erase a) he
        rw [heq] at hh
        exact hh hu
      · have he : C ⊆ xs.toFinset := by
          intro x hx
          have hc := hC hx
          simp only [List.toFinset_cons, Finset.mem_insert] at hc
          exact hc.resolve_left (by intro hh; subst x; exact ha hx)
        exact ih P l hlr.1 C he hu

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.OrbitCertificate.verify_sound
