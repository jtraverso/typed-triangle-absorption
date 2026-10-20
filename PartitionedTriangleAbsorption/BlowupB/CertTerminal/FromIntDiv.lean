/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Produce
public import PartitionedTriangleAbsorption.BlowupB.Deletions

@[expose] public section

/-!
# From `IsIntDiv` to a short explicit signed certificate, for every family

The certificate absorber of `BlowupB.CertAbsorber` (ported from Aristotle 52daa09e/b430df22)
needs an explicit signed certificate. Aristotle proves `IsIntDiv ⇒ certificate` only for `K₃`.
For an arbitrary family the route BlowupB already has the missing step, once the support may be
enlarged by `5` representatives per class: in a complete allowed blowup with at least `5` vertices
per class every `IsIntDiv` edge set has a physical certificate of uniformly bounded cost
(`physDivCost_complete`). Converting physical copies into signed occurrences
(`exists_signedCert_of_rep`) gives

`exists_signedCert_complete`: for every `F` (cardinality three) and `K` there is `C` such that
on any labelled finite `W` with `5` representatives per class, every loopless allowed
`IsIntDiv` edge set `P` with `|P| ≤ K` has an explicit signed certificate with at most `C`
occurrences.
-/

namespace PartitionedTriangleAbsorption.BlowupB.CertTerminal

open Finset PartitionedTriangleAbsorption PaperII.CertAbsorber

variable {t : ℕ}

/-- The complete allowed blowup on a labelled type. -/
def completeG {W : Type*} (p : W → Fin t) (F : Finset (Multiset (Fin t))) : SimpleGraph W :=
  SimpleGraph.fromRel fun u v => AllowedPair F (p u) (p v)

theorem completeG_isComplete {W : Type*} (p : W → Fin t) (F : Finset (Multiset (Fin t))) :
    IsCompleteBlowup p F (completeG p F) := by
  intro u v
  simp only [completeG, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.symm⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, Or.inl h'⟩

/-- **Short signed certificates from `IsIntDiv`, for every family.** -/
theorem exists_signedCert_complete (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (K : ℕ) :
    ∃ C : ℕ, ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin t), Reps p 5 →
      ∀ P : Finset (Sym2 W), (∀ e ∈ P, ¬ e.IsDiag) →
        (∀ u v, s(u, v) ∈ P → AllowedPair F (p u) (p v)) →
        IsIntDiv p F P → P.card ≤ K → ∃ c : SignedCert p F P, c.k ≤ C := by
  classical
  obtain ⟨C0, hC0⟩ := physDivCost_complete F hF3 K
  refine ⟨C0.toNat, ?_⟩
  intro W _ _ p R P hloop hall hdiv hK
  have hG := completeG_isComplete p F
  have hE : P ⊆ (completeG p F).edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hG]
      exact ⟨fun h => hloop _ he (by simp [h]), hall u v he⟩
  obtain ⟨ι, _, T, cc, ⟨hcopy, hsum⟩, hcost⟩ := hC0 hG R hE hdiv hK
  let z : Finset W → ℤ := fun s => ∑ j ∈ univ.filter (fun j => T j = s), cc j
  have htyped : ∀ j, T j ∈ typedTris p F := fun j =>
    mem_typedTris.mpr ⟨(hcopy j).1.card_eq, (hcopy j).2⟩
  have hz : ∀ e, triBd p F z e = if e ∈ P then 1 else 0 := by
    intro e
    calc triBd p F z e = ∑ s ∈ typedTris p F, ∑ j ∈ univ.filter (fun j => T j = s),
          cc j * (if e ∈ triEdges (T j) then 1 else 0) := by
          unfold triBd
          refine sum_congr rfl fun s _ => ?_
          simp only [z, sum_mul]
          refine sum_congr rfl fun j hj => ?_
          rw [(mem_filter.mp hj).2]
      _ = ∑ j, cc j * (if e ∈ triEdges (T j) then 1 else 0) :=
          sum_fiberwise_of_maps_to (fun j _ => htyped j) _
      _ = if e ∈ P then 1 else 0 := by
          have h := hsum e
          simp only [indZ] at h
          exact h.symm
  have hl1 : ((l1Norm p F z : ℕ) : ℤ) ≤ C0 := by
    unfold l1Norm
    push_cast
    calc ∑ s ∈ typedTris p F, |z s| ≤ ∑ s ∈ typedTris p F, ∑ j ∈ univ.filter (fun j => T j = s), |cc j| :=
          sum_le_sum fun s _ => abs_sum_le_sum_abs _ _
      _ = ∑ j, |cc j| := sum_fiberwise_of_maps_to (fun j _ => htyped j) _
      _ ≤ C0 := hcost
  obtain ⟨c, hc⟩ := exists_signedCert_of_rep z hz
  exact ⟨c, hc.trans (by omega)⟩

end PartitionedTriangleAbsorption.BlowupB.CertTerminal

#print axioms PartitionedTriangleAbsorption.BlowupB.CertTerminal.exists_signedCert_complete
