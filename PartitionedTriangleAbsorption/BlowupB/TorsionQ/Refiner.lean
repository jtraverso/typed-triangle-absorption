/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.Value
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.PredEnumeration

@[expose] public section

/-!
# A universal mod-`q` torsion layer for physical predicate refiners (generalizes `PaddedF12.torsion_layer`)

The old predicate refiner, its complete enumeration and all private torsion
tokens are fixed before the leftover. Only the selected chain path depends on
the later leftover. The parity is required to be additive only on its domain
`Good`; this includes the divided parity used by F2.
-/

namespace TorsionQ

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [DecidableEq V] {q : Nat}

/-- Physical torsion-one tokens, with no graph completeness hypothesis. -/
structure QTokenReal {Good : Finset (Sym2 V) → Prop} (ev : QEvaluation q Good)
    (B : Finset (Sym2 V)) (S : Finset Atom) (tok : Atom → Finset (Sym2 V)) : Prop where
  disj : (S : Set Atom).PairwiseDisjoint tok
  avoid : ∀ a ∈ S, Disjoint (tok a) B
  good : ∀ a ∈ S, Good (tok a)
  value : ∀ a ∈ S, ev.value (tok a) = 1

theorem incidentLoad_eq_sum_indicator (E : Finset (Sym2 V)) (v : V) :
    incidentLoad E v = ∑ e ∈ E, if v ∈ e then 1 else 0 := by
  simp only [incidentLoad, card_eq_sum_ones, sum_filter]

/-- The complete parity layer for an already enumerated old library. -/
theorem torsion_layerQ_enumerated (hq : 0 < q)
    {X : Finset (Sym2 V)} {Q Good : Finset (Sym2 V) → Prop}
    (E : PredRefiner ℕ X Q) (N : ℕ) (hlib : E.lib = range N)
    (ev : QEvaluation q Good) (hQ0 : Q ∅)
    (hold : ∀ i ∈ E.lib, Good (E.P i))
    (hQgood : ∀ L ⊆ X, Q L → Good L)
    (hloop : ∀ A, Good A → ∀ e ∈ A, ¬ e.IsDiag)
    (heven : ∀ A, Good A → ∀ v, Even (incidentLoad A v))
    (K g : ℕ) (hsize : ∀ i ∈ E.lib, (E.P i).card ≤ K)
    (Extra : Finset Atom → (Atom → Finset (Sym2 V)) → Prop)
    (hsupply : ∀ S : Finset Atom, S.card ≤ q * N →
      ∃ tok, QTokenReal ev (E.R0 ∪ X) S tok ∧
        (∀ a ∈ S, (tok a).card ≤ g) ∧ Extra S tok) :
    ∃ (S : Finset Atom) (tok : Atom → Finset (Sym2 V))
      (E' : PredRefiner Index X (fun L => Q L ∧ ev.value L = 0)),
      QTokenReal ev (E.R0 ∪ X) S tok ∧ Extra S tok ∧
      S.card ≤ q * N ∧ E'.R0 = E.R0 ∪ S.biUnion tok ∧
      (∀ i ∈ E'.lib, Good (E'.P i) ∧ ev.value (E'.P i) = 0 ∧
        (E'.P i).card ≤ K + 3 * q * g) ∧
      E'.lib.card ≤ 2 * q * N ∧
      ∀ v, ∑ i ∈ E'.lib, incidentLoad (E'.P i) v ≤
        q * ∑ j ∈ E.lib, incidentLoad (E.P j) v +
          4 * q * ∑ a ∈ S, incidentLoad (tok a) v := by
  classical
  have hmem (j : ℕ) (hj : j < N) : j ∈ E.lib := by
    rw [hlib]
    exact mem_range.mpr hj
  have holdN : ∀ j < N, Good (E.P j) := fun j hj => hold j (hmem j hj)
  have hsubN : ∀ j < N, E.P j ⊆ E.R0 ∪ X := fun j hj => E.subP j (hmem j hj)
  have hsizeN : ∀ j < N, (E.P j).card ≤ K := fun j hj => hsize j (hmem j hj)
  obtain ⟨T0, hT0, hd0, hu0⟩ := E.refines ∅ (empty_subset _) hQ0
  have hRgood : Good E.R0 := by
    have h := ev.good_biUnion T0 E.P hd0 (fun i hi => hold i (hT0 hi))
    simpa only [hu0, union_empty] using h
  let eps : ℕ → ℕ := fun j => ev.value (E.P j)
  let r := ev.value E.R0
  have hr : r < q := ev.value_lt E.R0 hRgood
  have heps : ∀ j < N, ev.value (E.P j) = eps j % q := fun j hj =>
    (Nat.mod_eq_of_lt (ev.value_lt (E.P j) (holdN j hj))).symm
  let S := tokens q N r
  obtain ⟨tok, hreal, htokSize, hextra⟩ := hsupply S (card_tokens_le N r)
  let Rn := E.R0 ∪ S.biUnion tok
  have hpGood : ∀ i ∈ library q N eps r, Good (physicalPiece q N eps r E.P tok i) := by
    intro i hi
    exact physicalPiece_good ev (mem_library.mp hi) hsubN hreal.disj hreal.avoid holdN hreal.good
  have hpVal : ∀ i ∈ library q N eps r, ev.value (physicalPiece q N eps r E.P tok i) = 0 := by
    intro i hi
    exact physicalPiece_value_zero ev (mem_library.mp hi) hsubN hreal.disj hreal.avoid
      holdN hreal.good hq heps hreal.value
  have hpSub : ∀ i ∈ library q N eps r,
      physicalPiece q N eps r E.P tok i ⊆ Rn ∪ X := by
    intro i hi e he
    obtain ⟨a, ha, he⟩ := mem_biUnion.mp he
    have haAll := atoms_subset_all (mem_library.mp hi) ha
    rcases mem_union.mp haAll with ho | ht
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp ho
      have heOld := hsubN j (mem_range.mp hj) he
      exact (union_subset_union subset_union_left le_rfl) heOld
    · rw [realize_token E.P tok ht] at he
      exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨a, ht, he⟩))
  have hRX : Disjoint Rn X := by
    apply disjoint_union_left.mpr
    refine ⟨E.disjRX, ?_⟩
    rw [disjoint_biUnion_left]
    intro a ha
    exact (hreal.avoid a ha).mono_right subset_union_right
  let E' : PredRefiner Index X (fun L => Q L ∧ ev.value L = 0) :=
    { lib := library q N eps r
      P := physicalPiece q N eps r E.P tok
      R0 := Rn
      loopP := fun i hi => hloop _ (hpGood i hi)
      evenP := fun i hi => heven _ (hpGood i hi)
      subP := hpSub
      disjRX := hRX
      refines := by
        rintro L hLX ⟨hQL, hLval⟩
        obtain ⟨T, hT, hdisT, hUT⟩ := E.refines L hLX hQL
        have hTrange : T ⊆ range N := by simpa only [hlib] using hT
        let choose : ℕ → Bool := fun j => decide (j ∈ T)
        have hcT : chosenOld N choose = T := by
          ext j
          simp only [chosenOld, mem_filter, mem_range, choose, decide_eq_true_eq]
          exact ⟨fun h => h.2, fun hj => ⟨mem_range.mp (hTrange hj), hj⟩⟩
        have hsum : (∑ j ∈ range N, if choose j then eps j % q else 0) =
            ∑ j ∈ T, ev.value (E.P j) := by
          calc
            _ = ∑ j ∈ range N, if j ∈ T then ev.value (E.P j) else 0 := by
              apply sum_congr rfl
              intro j hj
              simp only [choose, decide_eq_true_eq]
              split_ifs
              · exact (heps j (mem_range.mp hj)).symm
              · rfl
            _ = _ := by
              rw [← sum_filter]
              congr 1
        have hfinal : carry q eps choose N = r := by
          rw [carry_eq_sum_mod, hsum]
          rw [← ev.value_biUnion T E.P hdisT (fun i hi => hold i (hT hi)), hUT]
          rw [ev.union_value (E.disjRX.mono_right hLX) hRgood (hQgood L hLX hQL), hLval,
            add_zero]
          exact Nat.mod_eq_of_lt hr
        have hdisChosen : (chosenOld N choose : Set ℕ).PairwiseDisjoint E.P := by
          simpa only [hcT] using hdisT
        refine ⟨selectedLibrary q N eps choose, selectedLibrary_subset hq hfinal,
          pairwiseDisjoint_physical_selected hq hfinal hsubN hdisChosen hreal.disj hreal.avoid, ?_⟩
        rw [biUnion_physical_selected hq E.P tok hfinal, hcT, hUT]
        change E.R0 ∪ L ∪ S.biUnion tok = (E.R0 ∪ S.biUnion tok) ∪ L
        ext e
        simp only [mem_union]
        tauto }
  refine ⟨S, tok, E', hreal, hextra, card_tokens_le N r, rfl, ?_, card_library_le N eps r, ?_⟩
  · intro i hi
    exact ⟨hpGood i hi, hpVal i hi,
      physicalPiece_card_le hq (mem_library.mp hi) hsizeN htokSize⟩
  · intro v
    have h := physical_weighted_incidence_le hq N eps r E.P tok (E.R0 ∪ X)
      (fun e => if v ∈ e then 1 else 0) hsubN hreal.disj hreal.avoid
    simpa only [← incidentLoad_eq_sum_indicator, ← hlib] using h

#print axioms torsion_layerQ_enumerated

/-- The parity layer for any finite index type, preserving the exact old
incidence sum through the proved enumeration. -/
theorem torsion_layerQ (hq : 0 < q) {κ : Type*}
    {X : Finset (Sym2 V)} {Q Good : Finset (Sym2 V) → Prop}
    (E : PredRefiner κ X Q)
    (ev : QEvaluation q Good) (hQ0 : Q ∅)
    (hold : ∀ i ∈ E.lib, Good (E.P i))
    (hQgood : ∀ L ⊆ X, Q L → Good L)
    (hloop : ∀ A, Good A → ∀ e ∈ A, ¬ e.IsDiag)
    (heven : ∀ A, Good A → ∀ v, Even (incidentLoad A v))
    (K g : ℕ) (hsize : ∀ i ∈ E.lib, (E.P i).card ≤ K)
    (Extra : Finset Atom → (Atom → Finset (Sym2 V)) → Prop)
    (hsupply : ∀ S : Finset Atom, S.card ≤ q * E.lib.card →
      ∃ tok, QTokenReal ev (E.R0 ∪ X) S tok ∧
        (∀ a ∈ S, (tok a).card ≤ g) ∧ Extra S tok) :
    ∃ (S : Finset Atom) (tok : Atom → Finset (Sym2 V))
      (E' : PredRefiner Index X (fun L => Q L ∧ ev.value L = 0)),
      QTokenReal ev (E.R0 ∪ X) S tok ∧ Extra S tok ∧
      S.card ≤ q * E.lib.card ∧ E'.R0 = E.R0 ∪ S.biUnion tok ∧
      (∀ i ∈ E'.lib, Good (E'.P i) ∧ ev.value (E'.P i) = 0 ∧
        (E'.P i).card ≤ K + 3 * q * g) ∧
      E'.lib.card ≤ 2 * q * E.lib.card ∧
      ∀ v, ∑ i ∈ E'.lib, incidentLoad (E'.P i) v ≤
        q * ∑ j ∈ E.lib, incidentLoad (E.P j) v +
          4 * q * ∑ a ∈ S, incidentLoad (tok a) v := by
  obtain ⟨S, tok, E', hreal, hextra, hS, hR, hP, hcard, hload⟩ :=
    torsion_layerQ_enumerated hq E.enumerate E.lib.card rfl ev hQ0
      ((E.enumerate_forall_iff Good).mpr hold) hQgood hloop heven K g
      (E.enumerate_size K hsize) Extra hsupply
  refine ⟨S, tok, E', hreal, hextra, hS, hR, hP, hcard, ?_⟩
  intro v
  simpa only [E.enumerate_incidence v] using hload v

#print axioms torsion_layerQ

end TorsionQ
