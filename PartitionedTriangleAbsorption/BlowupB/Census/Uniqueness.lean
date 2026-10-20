/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Action

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

def IsLeast (C : Finset (Fin 20)) : Prop :=
  ∀ i : Fin 24, familyMask C ≤ familyMask (actCode i C)

instance (C : Finset (Fin 20)) : Decidable (IsLeast C) := by
  unfold IsLeast
  infer_instance

/-- A representative must be admissible and genuinely least in its orbit. -/
def GoodRepresentative (m : ℕ) : Prop :=
  Admissible (decodeMask m) ∧ familyMask (decodeMask m) = m ∧ IsLeast (decodeMask m)

instance (m : ℕ) : Decidable (GoodRepresentative m) := by
  unfold GoodRepresentative
  infer_instance

theorem decode_injective : Function.Injective decode := by
  intro C D h
  simpa only [encode_decode] using congrArg encode h

theorem relabel_inverse (F : Finset (Multiset (Fin 4))) (s : Equiv.Perm (Fin 4)) :
    (F.image (Multiset.map s)).image (Multiset.map s.symm) = F := by
  simp [Finset.image_image, Multiset.map_map, Function.comp_def]

/-- Least masks distinguish orbits for the actual action on multiset families. -/
theorem least_orbit_unique (C D : Finset (Fin 20))
    (hC : IsLeast C) (hD : IsLeast D) (s : Equiv.Perm (Fin 4))
    (h : decode D = (decode C).image (Multiset.map s)) : C = D := by
  obtain ⟨i, hi⟩ := sigma_covers s
  have hact : actCode i C = D := by
    apply decode_injective
    rw [decode_actCode, hi, ← h]
  have hle : familyMask C ≤ familyMask D := by
    rw [← hact]
    exact hC i
  obtain ⟨j, hj⟩ := sigma_covers s.symm
  have hback : actCode j D = C := by
    apply decode_injective
    rw [decode_actCode, hj, h, relabel_inverse]
  have hge : familyMask D ≤ familyMask C := by
    rw [← hback]
    exact hD j
  exact familyMask_injective (Nat.le_antisymm hle hge)

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.least_orbit_unique
