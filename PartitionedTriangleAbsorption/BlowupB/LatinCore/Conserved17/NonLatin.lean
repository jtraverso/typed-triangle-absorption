/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarExample
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarMono
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarRemaining
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Scales

@[expose] public section

/-! Actual certificates for the non-Latin components. Packaging each case
keeps its dependent dimension abstract while assembling the finite table. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17
open Finset BalFixer
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A possibly different scale for each occupied non-core component. -/
def NonCoreCertificates (d : Case) : Prop :=
  ∀ k : Fin d.t, k ≠ d.core → (∀ r, d.comp r ≠ k) ∨
    ∃ L, ComponentCertFlexTL (componentFamily d k) d.comp k L

/-- One scale for all occupied non-core components of a case. -/
def NonCoreAt (d : Case) (L : ℕ) : Prop :=
  ∀ k : Fin d.t, k ≠ d.core → (∀ r, d.comp r ≠ k) ∨
    ComponentCertFlexTL (componentFamily d k) d.comp k L


theorem noncore_at_mono (d : Case) {L L' : ℕ} (hLL : L ≤ L')
    (h : NonCoreAt d L) : NonCoreAt d L' := by
  intro k hk
  rcases h k hk with h | h
  · exact Or.inl h
  · exact Or.inr (componentCertificate_mono hLL h)

theorem NonCoreCertificates.exists_scale (d : Case) (h : NonCoreCertificates d) :
    ∃ L, NonCoreAt d L := by
  classical
  have hex : ∀ k : Fin d.t, ∃ L, k ≠ d.core → (∀ r, d.comp r ≠ k) ∨
      ComponentCertFlexTL (componentFamily d k) d.comp k L := by
    intro k
    by_cases hk : k = d.core
    · exact ⟨0, fun hn => (hn hk).elim⟩
    · rcases h k hk with h | ⟨L, h⟩
      · exact ⟨0, fun _ => Or.inl h⟩
      · exact ⟨L, fun _ => Or.inr h⟩
  choose f hf using hex
  refine ⟨∑ k, f k, ?_⟩
  intro k hk
  rcases hf k hk with h | h
  · exact Or.inl h
  · right
    exact componentCertificate_mono
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)) h


theorem noncore_certificates : ∀ i : Fin 17, NonCoreCertificates (cases i) := by
  intro i
  fin_cases i
  · change ∀ k : Fin 4, k ≠ case00.core →
      (∀ r, case00.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case00 k) case00.comp k L
    intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 4, (![0, 0, 0, 0] : Fin 4 → Fin 4) r ≠ (1 : Fin 4)
      decide +kernel
    · left
      change ∀ r : Fin 4, (![0, 0, 0, 0] : Fin 4 → Fin 4) r ≠ (2 : Fin 4)
      decide +kernel
    · left
      change ∀ r : Fin 4, (![0, 0, 0, 0] : Fin 4 → Fin 4) r ≠ (3 : Fin 4)
      decide +kernel
  · change ∀ k : Fin 5, k ≠ case01.core →
      (∀ r, case01.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case01 k) case01.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case01.comp : Fin 5 → Fin 5) = Star01_0.c := rfl
      rw [hc]
      exact Star01_0.exists_certificate
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (1 : Fin 5)
      decide +kernel
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (3 : Fin 5)
      decide +kernel
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (4 : Fin 5)
      decide +kernel
  · change ∀ k : Fin 6, k ≠ case02.core →
      (∀ r, case02.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case02 k) case02.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case02.comp : Fin 6 → Fin 6) = Star02_0.c := rfl
      rw [hc]
      exact Star02_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 3, 1, 3] : Fin 6 → Fin 6) r ≠ (2 : Fin 6)
      decide +kernel
    · right
      have hc : (case02.comp : Fin 6 → Fin 6) = Star02_3.c := rfl
      rw [hc]
      exact Star02_3.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 3, 1, 3] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 3, 1, 3] : Fin 6 → Fin 6) r ≠ (5 : Fin 6)
      decide +kernel
  · change ∀ k : Fin 4, k ≠ case03.core →
      (∀ r, case03.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case03 k) case03.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case03.comp : Fin 4 → Fin 4) = Star03_0.c := rfl
      rw [hc]
      exact Star03_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 4, (![0, 1, 1, 1] : Fin 4 → Fin 4) r ≠ (2 : Fin 4)
      decide +kernel
    · left
      change ∀ r : Fin 4, (![0, 1, 1, 1] : Fin 4 → Fin 4) r ≠ (3 : Fin 4)
      decide +kernel
  · change ∀ k : Fin 5, k ≠ case04.core →
      (∀ r, case04.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case04 k) case04.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case04.comp : Fin 5 → Fin 5) = Star04_0.c := rfl
      rw [hc]
      exact Star04_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 5, (![0, 1, 1, 1, 4] : Fin 5 → Fin 5) r ≠ (2 : Fin 5)
      decide +kernel
    · left
      change ∀ r : Fin 5, (![0, 1, 1, 1, 4] : Fin 5 → Fin 5) r ≠ (3 : Fin 5)
      decide +kernel
    · right
      have hc : (case04.comp : Fin 5 → Fin 5) = Star04_4.c := rfl
      rw [hc]
      exact Star04_4.exists_certificate
  · change ∀ k : Fin 5, k ≠ case05.core →
      (∀ r, case05.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case05 k) case05.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case05.comp : Fin 5 → Fin 5) = Star05_0.c := rfl
      rw [hc]
      exact Star05_0.exists_certificate
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (1 : Fin 5)
      decide +kernel
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (3 : Fin 5)
      decide +kernel
    · left
      change ∀ r : Fin 5, (![0, 0, 2, 2, 2] : Fin 5 → Fin 5) r ≠ (4 : Fin 5)
      decide +kernel
  · change ∀ k : Fin 5, k ≠ case06.core →
      (∀ r, case06.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case06 k) case06.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case06.comp : Fin 5 → Fin 5) = Star06_0.c := rfl
      rw [hc]
      exact Star06_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 5, (![0, 1, 1, 1, 1] : Fin 5 → Fin 5) r ≠ (2 : Fin 5)
      decide +kernel
    · left
      change ∀ r : Fin 5, (![0, 1, 1, 1, 1] : Fin 5 → Fin 5) r ≠ (3 : Fin 5)
      decide +kernel
    · left
      change ∀ r : Fin 5, (![0, 1, 1, 1, 1] : Fin 5 → Fin 5) r ≠ (4 : Fin 5)
      decide +kernel
  · change ∀ k : Fin 6, k ≠ case07.core →
      (∀ r, case07.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case07 k) case07.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case07.comp : Fin 6 → Fin 6) = Star07_0.c := rfl
      rw [hc]
      exact Star07_0.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (1 : Fin 6)
      decide +kernel
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (3 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (5 : Fin 6)
      decide +kernel
  · change ∀ k : Fin 6, k ≠ case08.core →
      (∀ r, case08.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case08 k) case08.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case08.comp : Fin 6 → Fin 6) = Star08_0.c := rfl
      rw [hc]
      exact Star08_0.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 3, 2, 2] : Fin 6 → Fin 6) r ≠ (1 : Fin 6)
      decide +kernel
    · exact (hk rfl).elim
    · right
      have hc : (case08.comp : Fin 6 → Fin 6) = Star08_3.c := rfl
      rw [hc]
      exact Star08_3.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 3, 2, 2] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 3, 2, 2] : Fin 6 → Fin 6) r ≠ (5 : Fin 6)
      decide +kernel
  · change ∀ k : Fin 6, k ≠ case09.core →
      (∀ r, case09.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case09 k) case09.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case09.comp : Fin 6 → Fin 6) = Star09_0.c := rfl
      rw [hc]
      exact Star09_0.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (1 : Fin 6)
      decide +kernel
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (3 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 0, 2, 0, 2, 2] : Fin 6 → Fin 6) r ≠ (5 : Fin 6)
      decide +kernel
  · change ∀ k : Fin 7, k ≠ case10.core →
      (∀ r, case10.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case10 k) case10.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case10.comp : Fin 7 → Fin 7) = Star10_0.c := rfl
      rw [hc]
      exact Star10_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 7, (![0, 1, 1, 3, 1, 3, 3] : Fin 7 → Fin 7) r ≠ (2 : Fin 7)
      decide +kernel
    · right
      have hc : (case10.comp : Fin 7 → Fin 7) = Star10_3.c := rfl
      rw [hc]
      exact Star10_3.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 1, 1, 3, 1, 3, 3] : Fin 7 → Fin 7) r ≠ (4 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 1, 1, 3, 1, 3, 3] : Fin 7 → Fin 7) r ≠ (5 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 1, 1, 3, 1, 3, 3] : Fin 7 → Fin 7) r ≠ (6 : Fin 7)
      decide +kernel
  · change ∀ k : Fin 7, k ≠ case11.core →
      (∀ r, case11.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case11 k) case11.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case11.comp : Fin 7 → Fin 7) = Star11_0.c := rfl
      rw [hc]
      exact Star11_0.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 0, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (1 : Fin 7)
      decide +kernel
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 0, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (3 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 0, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (4 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 0, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (5 : Fin 7)
      decide +kernel
    · right
      have hc : (case11.comp : Fin 7 → Fin 7) = Star11_6.c := rfl
      rw [hc]
      exact Star11_6.exists_certificate
  · change ∀ k : Fin 6, k ≠ case12.core →
      (∀ r, case12.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case12 k) case12.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case12.comp : Fin 6 → Fin 6) = Star12_0.c := rfl
      rw [hc]
      exact Star12_0.exists_certificate
    · exact (hk rfl).elim
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 1, 1, 5] : Fin 6 → Fin 6) r ≠ (2 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 1, 1, 5] : Fin 6 → Fin 6) r ≠ (3 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 1, 1, 1, 1, 5] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · right
      have hc : (case12.comp : Fin 6 → Fin 6) = Star12_5.c := rfl
      rw [hc]
      exact Star12_5.exists_certificate
  · change ∀ k : Fin 6, k ≠ case13.core →
      (∀ r, case13.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case13 k) case13.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case13.comp : Fin 6 → Fin 6) = Star13_0.c := rfl
      rw [hc]
      exact Star13_0.exists_certificate
    · exact (hk rfl).elim
    · right
      have hc : (case13.comp : Fin 6 → Fin 6) = Star13_2.c := rfl
      rw [hc]
      exact Star13_2.exists_certificate
    · left
      change ∀ r : Fin 6, (![0, 1, 2, 1, 1, 5] : Fin 6 → Fin 6) r ≠ (3 : Fin 6)
      decide +kernel
    · left
      change ∀ r : Fin 6, (![0, 1, 2, 1, 1, 5] : Fin 6 → Fin 6) r ≠ (4 : Fin 6)
      decide +kernel
    · right
      have hc : (case13.comp : Fin 6 → Fin 6) = Star13_5.c := rfl
      rw [hc]
      exact Star13_5.exists_certificate
  · change ∀ k : Fin 7, k ≠ case14.core →
      (∀ r, case14.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case14 k) case14.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case14.comp : Fin 7 → Fin 7) = Star14_0.c := rfl
      rw [hc]
      exact Star14_0.exists_certificate
    · exact (hk rfl).elim
    · right
      have hc : (case14.comp : Fin 7 → Fin 7) = Star14_2.c := rfl
      rw [hc]
      exact Star14_2.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 1, 2, 1, 1, 5, 5] : Fin 7 → Fin 7) r ≠ (3 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 1, 2, 1, 1, 5, 5] : Fin 7 → Fin 7) r ≠ (4 : Fin 7)
      decide +kernel
    · right
      have hc : (case14.comp : Fin 7 → Fin 7) = Star14_5.c := rfl
      rw [hc]
      exact Star14_5.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 1, 2, 1, 1, 5, 5] : Fin 7 → Fin 7) r ≠ (6 : Fin 7)
      decide +kernel
  · change ∀ k : Fin 7, k ≠ case15.core →
      (∀ r, case15.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case15 k) case15.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case15.comp : Fin 7 → Fin 7) = Star15_0.c := rfl
      rw [hc]
      exact Star15_0.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 3, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (1 : Fin 7)
      decide +kernel
    · exact (hk rfl).elim
    · right
      have hc : (case15.comp : Fin 7 → Fin 7) = Star15_3.c := rfl
      rw [hc]
      exact Star15_3.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 3, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (4 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 0, 2, 3, 2, 2, 6] : Fin 7 → Fin 7) r ≠ (5 : Fin 7)
      decide +kernel
    · right
      have hc : (case15.comp : Fin 7 → Fin 7) = Star15_6.c := rfl
      rw [hc]
      exact Star15_6.exists_certificate
  · change ∀ k : Fin 7, k ≠ case16.core →
      (∀ r, case16.comp r ≠ k) ∨ ∃ L,
        ComponentCertFlexTL (componentFamily case16 k) case16.comp k L
    intro k hk
    fin_cases k
    · right
      have hc : (case16.comp : Fin 7 → Fin 7) = Star16_0.c := rfl
      rw [hc]
      exact Star16_0.exists_certificate
    · exact (hk rfl).elim
    · right
      have hc : (case16.comp : Fin 7 → Fin 7) = Star16_2.c := rfl
      rw [hc]
      exact Star16_2.exists_certificate
    · left
      change ∀ r : Fin 7, (![0, 1, 2, 1, 1, 5, 6] : Fin 7 → Fin 7) r ≠ (3 : Fin 7)
      decide +kernel
    · left
      change ∀ r : Fin 7, (![0, 1, 2, 1, 1, 5, 6] : Fin 7 → Fin 7) r ≠ (4 : Fin 7)
      decide +kernel
    · right
      have hc : (case16.comp : Fin 7 → Fin 7) = Star16_5.c := rfl
      rw [hc]
      exact Star16_5.exists_certificate
    · right
      have hc : (case16.comp : Fin 7 → Fin 7) = Star16_6.c := rfl
      rw [hc]
      exact Star16_6.exists_certificate

/-- All non-Latin component certificates use a scale fixed before the host. -/
theorem noncore_common_scale : ∃ L, ∀ i : Fin 17, NonCoreAt (cases i) L := by
  classical
  have hex : ∀ i : Fin 17, ∃ L, NonCoreAt (cases i) L :=
    fun i => NonCoreCertificates.exists_scale (cases i) (noncore_certificates i)
  choose f hf using hex
  refine ⟨∑ i, f i, ?_⟩
  intro i
  exact noncore_at_mono (cases i)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hf i)


end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.noncore_certificates
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.noncore_common_scale


