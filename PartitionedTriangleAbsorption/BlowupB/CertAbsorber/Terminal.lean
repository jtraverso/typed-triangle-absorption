/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Budgets

/-! # The terminal absorber produced by an explicit signed certificate (abstract form)

`exists_certificate_absorber`: from an explicit signed certificate of `P` with `k`
occurrences (`k⁻` of them negative) one builds a finite extension `W ↪ W'`, a labelling `p'`
extending `p`, and an edge set `A` such that
1. no edge of `A` has both endpoints in `W`;
2. `A` and `A ∪ P` are `F`-decomposable (physical `HasDecomp`), and `A ∩ P = ∅`;
3. `|A| = 9k + 21k⁻ ≤ 30k` and `|W'| = |W| + 9k`;
4. `incidentLoad A (x) ≤ 4 · occ(x)` for every `x ∈ W`.

No near-completeness, no decomposition of `P`, no absorber and no `nash_williams` is used.
The case `k = 0` is included (then the boundary condition forces `P = ∅` and `A = ∅`).
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection

universe u

/-- **Terminal absorber from an explicit signed certificate.** -/
theorem exists_certificate_absorber {W : Type u} [Fintype W] [DecidableEq W] {t : ℕ}
    {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
    (c : SignedCert p F P) :
    ∃ (W' : Type u) (_ : Fintype W') (_ : DecidableEq W') (ι : W ↪ W') (p' : W' → Fin t)
      (A : Finset (Sym2 W')),
      (∀ x, p' (ι x) = p x) ∧
      Fintype.card W' = Fintype.card W + 9 * c.k ∧
      (∀ e ∈ A, ∀ x y : W, e ≠ s(ι x, ι y)) ∧
      HasDecomp p' F A ∧
      HasDecomp p' F (A ∪ P.image (Sym2.map ι)) ∧
      Disjoint A (P.image (Sym2.map ι)) ∧
      A.card = 9 * c.k + 21 * c.negCount ∧ A.card ≤ 30 * c.k ∧
      ∀ x, incidentLoad A (ι x) ≤ 4 * c.occCount x := by
  obtain ⟨M⟩ := exists_matching c
  exact ⟨Ext W c.k, inferInstance, inferInstance, ⟨Sum.inl, Sum.inl_injective⟩, c.extLabel,
    M.absorber, fun _ => rfl, card_ext, absorber_no_old_edge M, hasDecomp_absorber M,
    hasDecomp_absorber_union M, absorber_disjoint_P M, card_absorber M, card_absorber_le M,
    incidentLoad_absorber M⟩

end PaperII.CertAbsorber
