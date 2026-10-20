/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Inverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Covered

@[expose] public section

/-!
# Transfer from Fbit to its bit-only supersets

The census found five bit-only families (quotient `ℤ/2`) with the allowed pairs of Fbit:
`Fbit`, `Fbit ∪ {333}`, `Fbit ∪ {111}`, `Fbit ∪ {111, 222}`, `Fbit ∪ {111, 222, 333}`. Every extra
type is monochromatic, so it adds no allowed pair and has an even 01-count. For such an `F ⊇ Fbit`:

* the universal absorbers of Fbit are universal for `F`: an Fbit decomposition is an `F`
  decomposition, and an `F`-divisible leftover is Fbit-divisible (`F`-divisibility forces `Even3` and
  an even 01-count, i.e. `FbitGood ∧ bit = 0`, which is Fbit-divisibility);
* the Fbit ternary inverse is `F`-supported, so the copy step of the F* certificate runs for `F`.

`keevashPaddedSpec_of_fbitSuper` packages this; the four supersets are instantiated with `decide`.
-/

namespace PaddedFbit

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedF12

/-- The hypotheses on a superset of Fbit (all decidable for a concrete family). -/
structure FbitSuper (F : Finset (Multiset (Fin 4))) : Prop where
  sub : Fbit ⊆ F
  allowed : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link Fbit i j k)
  bit : ∀ τ ∈ F, (2 : ℤ) ∣ typeEdgeVec τ 0 1
  facts : PaddedGeneral.FamilyFacts F

theorem hasDecomp_of_subset {V : Type*} [DecidableEq V] {p : V → Fin 4}
    {F F' : Finset (Multiset (Fin 4))} (h : F ⊆ F') {E : Finset (Sym2 V)}
    (hd : HasDecomp p F E) : HasDecomp p F' E := by
  obtain ⟨D, hD, hdis, hU⟩ := hd
  exact ⟨D, fun s hs => ⟨(hD s hs).1, h (hD s hs).2⟩, hdis, hU⟩

theorem allowed_fun_eq {F : Finset (Multiset (Fin 4))} (hF : FbitSuper F) :
    (fun i j : Fin 4 => ∃ k, Link F i j k) = (fun i j => ∃ k, Link Fbit i j k) :=
  funext fun i => funext fun j => propext (hF.allowed i j)

/-- An `F`-divisible loopless set is Fbit-divisible. -/
theorem isIntDiv_Fbit_of_super {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Multiset (Fin 4))} (hF : FbitSuper F) (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F E) : IsIntDiv p Fbit E := by
  have hcard := hF.facts.card_three
  obtain ⟨h3, heven⟩ := PaddedTrivial.even3_of_isIntDiv hcard p hloop hd
  have hact : ActiveEdges Fbit p E := by
    intro a b hab
    exact (hF.allowed _ _).mp (active_of_isIntDiv hcard hd a b hab)
  refine (isIntDiv_Fbit_iff_good_bit p E hloop).mpr ⟨⟨hloop, hact, heven, h3⟩, ?_⟩
  obtain ⟨c, hc⟩ := hd.1
  have h01 := congrFun (congrFun hc 0) 1
  rw [edgeVec_unorderedCount] at h01
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h01
  unfold fbitBit
  rw [intParity_eq_zero_iff]
  have hdvd : (2 : ℤ) ∣ ∑ τ ∈ F, c τ * typeEdgeVec τ 0 1 :=
    Finset.dvd_sum fun τ hτ => dvd_mul_of_dvd_right (hF.bit τ hτ) _
  have hone : (if (0 : Fin 4) = 1 then (2 : ℤ) else 1) = 1 := by decide
  rw [hone, one_mul] at h01
  rw [h01]
  exact hdvd

theorem universalCert_of_fbitSuper {F : Finset (Multiset (Fin 4))} (hF : FbitSuper F) :
    PaddedGeneral.UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hG' : ∀ u v, G.Adj u v → ∃ k, Link Fbit (p u) (p v) k :=
    fun u v h => (hF.allowed _ _).mp (hG u v h)
  rw [allowed_fun_eq hF] at hs
  have U := universal_simple_Fbit p G ω hG' hs hω hω1 hn
  intro X hXG hX
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hL⟩ := U X hXG hX
  refine ⟨A, hAG, hAX, hasDecomp_of_subset hF.sub hAdec, hAdeg, ?_⟩
  intro L hLX hLdiv
  have hloop : ∀ e ∈ L, ¬ e.IsDiag :=
    fun e he => G.not_isDiag_of_mem_edgeFinset (hXG (hLX he))
  exact hasDecomp_of_subset hF.sub (hL L hLX (isIntDiv_Fbit_of_super hF p L hloop hLdiv))

theorem activeCompleteGraph_eq {V : Type*} [DecidableEq V] {F : Finset (Multiset (Fin 4))}
    (hF : FbitSuper F) (p : V → Fin 4) :
    activeCompleteGraph p F = activeCompleteGraph p Fbit := by
  ext a b
  change (a ≠ b ∧ ∃ k, Link F (p a) (p b) k) ↔ (a ≠ b ∧ ∃ k, Link Fbit (p a) (p b) k)
  rw [hF.allowed]

theorem completeInverseCert_of_fbitSuper {F : Finset (Multiset (Fin 4))} (hF : FbitSuper F) :
    PaddedGeneral.CompleteInverseCert F := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  have hsE : EdgeSupported p Fbit (fun a b => r s(a, b)) := by
    intro a b hab
    exact hs.edgeSupported a b (fun h => hab ((hF.allowed _ _).mp h))
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_Fbit p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hsE
    (fun a b => hr s(a, b))
  have htwF : TernarySupported p F w := by
    intro a b c hna
    exact htw a b c fun h => hna ⟨h.1, h.2.1, h.2.2.1, hF.sub h.2.2.2⟩
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p F w hsw htwF _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p F (activeCompleteGraph p F) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p F (activeCompleteGraph p F) z,
    copyRestriction_supported p F (activeCompleteGraph p F) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p F (activeCompleteGraph p F) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p F (activeCompleteGraph p F) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

/-- **`KeevashPaddedSpec` for every bit-only superset of Fbit.** -/
theorem keevashPaddedSpec_of_fbitSuper {F : Finset (Multiset (Fin 4))} (hF : FbitSuper F) :
    PaddedInputs.KeevashPaddedSpec F :=
  PaddedGeneral.keevashPaddedSpec_of_certs F hF.facts (universalCert_of_fbitSuper hF)
    (completeInverseCert_of_fbitSuper hF)

/-! ### The five bit-only families of the census -/

noncomputable def Fbit333 : Finset (Multiset (Fin 4)) := insert {3, 3, 3} Fbit
noncomputable def Fbit111 : Finset (Multiset (Fin 4)) := insert {1, 1, 1} Fbit
noncomputable def Fbit111222 : Finset (Multiset (Fin 4)) := insert {1, 1, 1} (insert {2, 2, 2} Fbit)
noncomputable def FbitMono : Finset (Multiset (Fin 4)) :=
  insert {1, 1, 1} (insert {2, 2, 2} (insert {3, 3, 3} Fbit))

theorem facts_of_decide (F : Finset (Multiset (Fin 4)))
    (h1 : ∀ τ ∈ F, Multiset.card τ = 3)
    (h2 : ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ F →
      (∃ a, Link F i k a) ∧ (∃ a, Link F j k a))
    (h3 : ∀ i : Fin 4, ∃ j, ¬ ∃ k, Link F i j k) : PaddedGeneral.FamilyFacts F :=
  ⟨h1, h2, h3⟩

theorem fbitSuper_Fbit : FbitSuper Fbit :=
  ⟨subset_rfl, fun _ _ => Iff.rfl, by unfold Fbit; decide,
    facts_of_decide _ Fbit_card (by unfold Link Fbit; decide)
      (by intro i; fin_cases i <;> (unfold Link Fbit; decide))⟩

theorem fbitSuper_Fbit333 : FbitSuper Fbit333 :=
  ⟨by unfold Fbit333; exact subset_insert _ _, by unfold Fbit333 Link Fbit; decide,
    by unfold Fbit333 Fbit; decide,
    facts_of_decide _ (by unfold Fbit333 Fbit; decide) (by unfold Fbit333 Link Fbit; decide)
      (by intro i; fin_cases i <;> (unfold Fbit333 Link Fbit; decide))⟩

theorem fbitSuper_Fbit111 : FbitSuper Fbit111 :=
  ⟨by unfold Fbit111; exact subset_insert _ _, by unfold Fbit111 Link Fbit; decide,
    by unfold Fbit111 Fbit; decide,
    facts_of_decide _ (by unfold Fbit111 Fbit; decide) (by unfold Fbit111 Link Fbit; decide)
      (by intro i; fin_cases i <;> (unfold Fbit111 Link Fbit; decide))⟩

theorem fbitSuper_Fbit111222 : FbitSuper Fbit111222 :=
  ⟨by unfold Fbit111222; decide, by unfold Fbit111222 Link Fbit; decide,
    by unfold Fbit111222 Fbit; decide,
    facts_of_decide _ (by unfold Fbit111222 Fbit; decide)
      (by unfold Fbit111222 Link Fbit; decide)
      (by intro i; fin_cases i <;> (unfold Fbit111222 Link Fbit; decide))⟩

theorem fbitSuper_FbitMono : FbitSuper FbitMono :=
  ⟨by unfold FbitMono; decide, by unfold FbitMono Link Fbit; decide,
    by unfold FbitMono Fbit; decide,
    facts_of_decide _ (by unfold FbitMono Fbit; decide) (by unfold FbitMono Link Fbit; decide)
      (by intro i; fin_cases i <;> (unfold FbitMono Link Fbit; decide))⟩

theorem keevashPaddedSpec_Fbit : PaddedInputs.KeevashPaddedSpec Fbit :=
  keevashPaddedSpec_of_fbitSuper fbitSuper_Fbit
theorem keevashPaddedSpec_Fbit333 : PaddedInputs.KeevashPaddedSpec Fbit333 :=
  keevashPaddedSpec_of_fbitSuper fbitSuper_Fbit333
theorem keevashPaddedSpec_Fbit111 : PaddedInputs.KeevashPaddedSpec Fbit111 :=
  keevashPaddedSpec_of_fbitSuper fbitSuper_Fbit111
theorem keevashPaddedSpec_Fbit111222 : PaddedInputs.KeevashPaddedSpec Fbit111222 :=
  keevashPaddedSpec_of_fbitSuper fbitSuper_Fbit111222
theorem keevashPaddedSpec_FbitMono : PaddedInputs.KeevashPaddedSpec FbitMono :=
  keevashPaddedSpec_of_fbitSuper fbitSuper_FbitMono

#print axioms keevashPaddedSpec_of_fbitSuper
#print axioms keevashPaddedSpec_Fbit
#print axioms keevashPaddedSpec_Fbit333
#print axioms keevashPaddedSpec_Fbit111
#print axioms keevashPaddedSpec_Fbit111222
#print axioms keevashPaddedSpec_FbitMono

end PaddedFbit
