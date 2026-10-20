/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Terminal
public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Greedy
public import PartitionedTriangleAbsorption.ColouredHub.Lattice

/-! # Realising the certificate absorber in a host graph

The roots `W` are placed in the host `V` by a prescribed injection `ρ`.  The `9k` new vertices
of the abstract gadget are placed greedily, in the rank order
`occurrence clones of corner 0 < corner 1 < corner 2 < hinge clone a < hinge clone b`.
Each new vertex has at most four adjacency demands towards roots or earlier new vertices,
and every demanded pair of labels lies in a type of `F` (so the existing compatible
four-root supply `CompatibleSupply` applies).  The abstract decompositions are then
transported by the existing `ColouredHub.hasDecomp_image_typed`.
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
  PartitionedTriangleAbsorption.PairMoveSelectionStage85 PartitionedTriangleAbsorption.TypedTransformer

variable {W : Type*} [DecidableEq W] {t : ℕ}
variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable {c : SignedCert p F P}

/-- The new vertices of the gadget. -/
abbrev NewV (k : ℕ) := (Fin k × Fin 3) ⊕ ((Fin k × Fin 3) × Bool)

namespace SignedCert

variable (c)

/-- Rank of a new vertex in the greedy order. -/
def gRank : NewV c.k → ℕ
  | Sum.inl s => s.2.val
  | Sum.inr (_, false) => 3
  | Sum.inr (_, true) => 4

/-- Root demands of a new vertex. -/
def gRoots : NewV c.k → Finset W
  | Sum.inl s => {c.U s, c.V s}
  | Sum.inr (s, false) => if c.pos s.1 = false then {c.V s} else ∅
  | Sum.inr (s, true) => if c.pos s.1 = false then {c.U s} else ∅

end SignedCert

namespace Matching

variable (M : Matching c)

/-- Demands of a new vertex towards earlier new vertices. -/
def gBack : NewV c.k → Finset (NewV c.k)
  | Sum.inl s => (univ.filter fun m : Fin 3 => m.val < s.2.val).image fun m => Sum.inl (s.1, m)
  | Sum.inr (s, false) => if c.pos s.1 = false then {Sum.inl s, Sum.inl (M.mu s)} else ∅
  | Sum.inr (s, true) =>
      if c.pos s.1 = false then {Sum.inr (s, false), Sum.inl s, Sum.inl (M.mu s)} else ∅

end Matching

private lemma ms_eq_312 {α : Type*} (a b d : α) : ({a, b, d} : Multiset α) = {d, a, b} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; ac_rfl
private lemma ms_eq_321 {α : Type*} (a b d : α) : ({a, b, d} : Multiset α) = {d, b, a} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; ac_rfl
private lemma ms_eq_213 {α : Type*} (a b d : α) : ({a, b, d} : Multiset α) = {b, a, d} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; ac_rfl
private lemma ms_eq_132 {α : Type*} (a b d : α) : ({a, b, d} : Multiset α) = {a, d, b} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; ac_rfl
private lemma ms_eq_231 {α : Type*} (a b d : α) : ({a, b, d} : Multiset α) = {b, d, a} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; ac_rfl

lemma gBack_rank (M : Matching c) (x : NewV c.k) : ∀ y ∈ M.gBack x, c.gRank y < c.gRank x := by
  rcases x with s | ⟨s, b⟩
  · intro y hy
    simp only [Matching.gBack, mem_image, mem_filter, mem_univ, true_and] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    simpa [SignedCert.gRank] using hm
  · cases b <;> intro y hy <;> simp only [Matching.gBack] at hy <;> split_ifs at hy <;>
      simp at hy <;> rcases hy with rfl | rfl | rfl <;> simp [SignedCert.gRank] <;> omega

lemma gDemand_card (M : Matching c) (x : NewV c.k) :
    (c.gRoots x).card + (M.gBack x).card ≤ 4 := by
  rcases x with s | ⟨s, b⟩
  · have h1 : (c.gRoots (Sum.inl s)).card ≤ 2 := card_le_two
    have h2 : (M.gBack (Sum.inl s)).card ≤ 2 := by
      have hsub : (univ.filter fun m : Fin 3 => m.val < s.2.val) ⊆ univ.erase s.2 := by
        intro m hm
        refine mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩
        rw [h] at hm
        simp at hm
      exact card_image_le.trans ((card_le_card hsub).trans (by simp))
    omega
  · cases b <;> simp only [SignedCert.gRoots, Matching.gBack] <;> split_ifs <;>
      first
        | (simp; done)
        | exact (Nat.add_le_add (card_singleton _).le card_le_two).trans (by norm_num)
        | exact (Nat.add_le_add (card_singleton _).le card_le_three).trans (by norm_num)

lemma pair_typed (i : Fin c.k) (m m' : Fin 3) (h : m ≠ m') :
    ∃ k, ({p (c.vtx i m), p (c.vtx i m'), k} : Multiset (Fin t)) ∈ F := by
  have ht := c.typed i
  fin_cases m <;> fin_cases m' <;> simp at h
  · exact ⟨_, ht⟩
  · exact ⟨_, by rw [ms_eq_132] at ht; exact ht⟩
  · exact ⟨_, by rw [ms_eq_213] at ht; exact ht⟩
  · exact ⟨_, by rw [ms_eq_231] at ht; exact ht⟩
  · exact ⟨_, by rw [ms_eq_312] at ht; exact ht⟩
  · exact ⟨_, by rw [ms_eq_321] at ht; exact ht⟩

lemma gRoots_compat (x : NewV c.k) :
    ∀ w ∈ c.gRoots x, ∃ k, Link F (c.extLabel (Sum.inr x)) (p w) k := by
  rcases x with s | ⟨s, b⟩
  · intro w hw
    have h := side_typed (c := c) s
    simp only [SignedCert.gRoots, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨p (c.V s), by rw [ms_eq_312] at h; exact h⟩
    · exact ⟨p (c.U s), by rw [ms_eq_321] at h; exact h⟩
  · have h := side_typed (c := c) s
    cases b <;> intro w hw <;> simp only [SignedCert.gRoots] at hw <;> split_ifs at hw <;>
      simp only [mem_singleton, notMem_empty] at hw <;> subst hw
    · exact ⟨_, h⟩
    · exact ⟨_, by rw [ms_eq_213] at h; exact h⟩

lemma gBack_compat (M : Matching c) (x : NewV c.k) :
    ∀ y ∈ M.gBack x, ∃ k, Link F (c.extLabel (Sum.inr x)) (c.extLabel (Sum.inr y)) k := by
  rcases x with s | ⟨s, b⟩
  · intro y hy
    simp only [Matching.gBack, mem_image, mem_filter, mem_univ, true_and] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact pair_typed s.1 s.2 m (fun h => by rw [h] at hm; omega)
  · have h := side_typed (c := c) s
    cases b <;> intro y hy <;> simp only [Matching.gBack] at hy <;> split_ifs at hy with hs <;>
      simp only [mem_insert, mem_singleton, notMem_empty] at hy
    · have hmu := mu_typed M s hs
      rcases hy with rfl | rfl
      · exact ⟨_, by rw [ms_eq_132] at h; exact h⟩
      · exact ⟨_, by rw [ms_eq_132] at hmu; exact hmu⟩
    · have hmu := mu_typed M s hs
      rcases hy with rfl | rfl | rfl
      · exact ⟨_, by rw [ms_eq_213] at h; exact h⟩
      · exact ⟨_, by rw [ms_eq_231] at h; exact h⟩
      · exact ⟨_, by rw [ms_eq_231] at hmu; exact hmu⟩

/-- Every edge of the absorber is a demand of its later endpoint. -/
lemma edge_demand (M : Matching c) (σ : Slot W c.k) (hσ : σ ∈ c.aSlots) :
    ∃ x : NewV c.k, (∃ w ∈ c.gRoots x, M.ed σ = s(Sum.inl w, Sum.inr x)) ∨
      (∃ y ∈ M.gBack x, M.ed σ = s(Sum.inr y, Sum.inr x)) := by
  rcases σ with ⟨s, x'⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e
  · rw [mem_aSlots_wv] at hσ
    exact ⟨Sum.inl s, Or.inl ⟨x', by rcases hσ with rfl | rfl <;> simp [SignedCert.gRoots],
      rfl⟩⟩
  · fin_cases m
    · exact ⟨Sum.inl (i, 2), Or.inr ⟨Sum.inl (i, 1), mem_image.mpr ⟨1, by simp, rfl⟩, rfl⟩⟩
    · exact ⟨Sum.inl (i, 2), Or.inr ⟨Sum.inl (i, 0), mem_image.mpr ⟨0, by simp, rfl⟩,
        Sym2.eq_swap⟩⟩
    · exact ⟨Sum.inl (i, 1), Or.inr ⟨Sum.inl (i, 0), mem_image.mpr ⟨0, by simp, rfl⟩, rfl⟩⟩
  · rw [mem_aSlots_h] at hσ
    cases κ
    · exact ⟨Sum.inr (s, true), Or.inl ⟨c.U s, by simp [SignedCert.gRoots, hσ], rfl⟩⟩
    · exact ⟨Sum.inr (s, false), Or.inl ⟨c.V s, by simp [SignedCert.gRoots, hσ], Sym2.eq_swap⟩⟩
    · exact ⟨Sum.inr (s, true), Or.inr ⟨Sum.inr (s, false), by simp [Matching.gBack, hσ], rfl⟩⟩
    · exact ⟨Sum.inr (s, false), Or.inr ⟨Sum.inl s, by simp [Matching.gBack, hσ], Sym2.eq_swap⟩⟩
    · exact ⟨Sum.inr (s, true), Or.inr ⟨Sum.inl s, by simp [Matching.gBack, hσ], Sym2.eq_swap⟩⟩
    · exact ⟨Sum.inr (s, false), Or.inr ⟨Sum.inl (M.mu s), by simp [Matching.gBack, hσ],
        Sym2.eq_swap⟩⟩
    · exact ⟨Sum.inr (s, true), Or.inr ⟨Sum.inl (M.mu s), by simp [Matching.gBack, hσ],
        Sym2.eq_swap⟩⟩
  · exact absurd hσ (not_mem_aSlots_pe e)

/-- **Host realisation of the certificate absorber.**

Premises: the roots are placed by an injection `ρ : W ↪ V` (labels `p = pV ∘ ρ`); the host has
the verifiable compatible four-root supply `CompatibleSupply pV F G a`; `B` is a set of
forbidden edges of maximum degree `≤ d`; `Z` is a set of forbidden vertices; and
`|Z| + |W| + 9k + 4d < a`.

Conclusion: an edge set `A ⊆ E(G)`, disjoint from `B` and from `ρ(P)`, with `HasDecomp A` and
`HasDecomp (A ∪ ρ(P))`, `|A| = 9k + 21k⁻ ≤ 30k`, whose vertices are roots or lie in a set `N`
of at most `9k` new vertices avoiding `Z` and the roots, every edge of `A` meeting `N`, and
`incidentLoad A (ρ x) ≤ 4 · occ(x)`. -/
theorem host_certificate_absorber {V : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (pV : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj] (ρ : W ↪ V)
    {P : Finset (Sym2 W)} (c : SignedCert (pV ∘ ρ) F P)
    (a d : ℝ) (hs : CompatibleSupply pV F G a) (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (hd : 0 ≤ d) (Z : Finset V)
    (hbud : (Z.card : ℝ) + Fintype.card W + 9 * c.k + 4 * d < a) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A B ∧
      HasDecomp pV F A ∧ HasDecomp pV F (A ∪ P.image (Sym2.map ρ)) ∧
      Disjoint A (P.image (Sym2.map ρ)) ∧
      A.card = 9 * c.k + 21 * c.negCount ∧ A.card ≤ 30 * c.k ∧
      (∃ N : Finset V, N.card ≤ 9 * c.k ∧ Disjoint N (Z ∪ univ.image ρ) ∧
        (∀ e ∈ A, ∀ v ∈ e, v ∈ univ.image ρ ∨ v ∈ N) ∧ ∀ e ∈ A, ∃ v ∈ e, v ∈ N) ∧
      ∀ x, incidentLoad A (ρ x) ≤ 4 * c.occCount x := by
  classical
  obtain ⟨M⟩ := exists_matching c
  set Zf : Finset V := Z ∪ univ.image ρ with hZf
  have hZf : (Zf.card : ℝ) + Fintype.card (NewV c.k) + 4 * d < a := by
    have h1 : Zf.card ≤ Z.card + Fintype.card W :=
      (card_union_le _ _).trans (Nat.add_le_add_left (card_image_le.trans (by simp)) _)
    have h2 : Fintype.card (NewV c.k) = 9 * c.k := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
    have h1' : (Zf.card : ℝ) ≤ Z.card + Fintype.card W := by exact_mod_cast h1
    rw [h2]; push_cast; linarith
  obtain ⟨φ, hφinj, hgood⟩ := greedy_embedding pV F G a d hs B hB hd Zf
    (fun x => c.extLabel (Sum.inr x)) (fun x => (c.gRoots x).image ρ) M.gBack c.gRank
    (gBack_rank M) (fun x => (Nat.add_le_add_right card_image_le _).trans (gDemand_card M x))
    (fun x v hv => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
      exact gRoots_compat x w hw)
    (gBack_compat M) hZf
  -- the physical map
  let f : Ext W c.k → V := Sum.elim ρ φ
  have hφZ : ∀ x, φ x ∉ Zf := fun x => (hgood x).2.1
  have hφρ : ∀ x w, φ x ≠ ρ w := fun x w h =>
    hφZ x (mem_union.mpr (Or.inr (mem_image.mpr ⟨w, mem_univ _, h.symm⟩)))
  have hfinj : Function.Injective f := by
    rintro (u | u) (v | v) h
    · exact congrArg Sum.inl (ρ.injective h)
    · exact absurd h.symm (hφρ v u)
    · exact absurd h (hφρ u v)
    · exact congrArg Sum.inr (hφinj h)
  have hflab : ∀ v, pV (f v) = c.extLabel v := by
    rintro (w | x)
    · rfl
    · exact (hgood x).1
  set A := M.absorber.image (Sym2.map f) with hA
  have hPimg : (P.image (Sym2.map Sum.inl)).image (Sym2.map f) = P.image (Sym2.map ρ) := by
    rw [image_image]
    refine image_congr fun e _ => ?_
    simp only [Function.comp, Sym2.map_map]
    rfl
  have hphys : ∀ e ∈ M.absorber, e.map f ∈ G.edgeFinset ∧ e.map f ∉ B := by
    intro e he
    obtain ⟨σ, hσ, rfl⟩ := mem_image.mp he
    obtain ⟨x, ⟨w, hw, hσe⟩ | ⟨y, hy, hσe⟩⟩ := edge_demand M σ hσ
    · rw [hσe]
      have := (hgood x).2.2.1 (ρ w) (mem_image.mpr ⟨w, hw, rfl⟩)
      exact ⟨by simpa [f] using this.1, by simpa [f] using this.2⟩
    · rw [hσe]
      have := (hgood x).2.2.2 y hy
      exact ⟨by simpa [f] using this.1, by simpa [f] using this.2⟩
  refine ⟨A, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    exact (hphys e' he').1
  · rw [disjoint_left]
    intro e he hb
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    exact (hphys e' he').2 hb
  · exact ColouredHub.hasDecomp_image_typed f hfinj hflab _ (hasDecomp_absorber M)
  · have h := ColouredHub.hasDecomp_image_typed f hfinj hflab _ (hasDecomp_absorber_union M)
    rwa [image_union, hPimg] at h
  · rw [← hPimg]
    exact (disjoint_image (Sym2.map.injective hfinj)).mpr (absorber_disjoint_P M)
  · rw [hA, card_image_of_injective _ (Sym2.map.injective hfinj), card_absorber]
  · rw [hA, card_image_of_injective _ (Sym2.map.injective hfinj)]
    exact card_absorber_le M
  · refine ⟨univ.image φ, card_image_le.trans (by
      simp only [card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool]; omega), ?_, ?_, ?_⟩
    · rw [disjoint_left]
      intro v hv hvZ
      obtain ⟨x, -, rfl⟩ := mem_image.mp hv
      exact hφZ x hvZ
    · intro e he v hv
      obtain ⟨e', -, rfl⟩ := mem_image.mp he
      obtain ⟨u, -, rfl⟩ := Sym2.mem_map.mp hv
      rcases u with w | x
      · exact Or.inl (mem_image.mpr ⟨w, mem_univ _, rfl⟩)
      · exact Or.inr (mem_image.mpr ⟨x, mem_univ _, rfl⟩)
    · intro e he
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      have hno := absorber_no_old_edge M e' he'
      induction e' using Sym2.ind with
      | _ u v =>
        rcases u with w | x
        · rcases v with w' | x'
          · exact absurd rfl (hno w w')
          · exact ⟨φ x', by simp [f], mem_image.mpr ⟨x', mem_univ _, rfl⟩⟩
        · exact ⟨φ x, by simp [f], mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩
  · intro x
    have hfilter : A.filter (fun e => ρ x ∈ e) =
        (M.absorber.filter (fun e => Sum.inl x ∈ e)).image (Sym2.map f) := by
      rw [hA, filter_image]
      congr 1
      ext e
      simp only [mem_filter]
      show _ ∧ f (Sum.inl x) ∈ Sym2.map f e ↔ _
      constructor
      · rintro ⟨he, hx⟩
        obtain ⟨u, hu, hfu⟩ := Sym2.mem_map.mp hx
        exact ⟨he, hfinj hfu ▸ hu⟩
      · rintro ⟨he, hx⟩
        exact ⟨he, Sym2.mem_map.mpr ⟨_, hx, rfl⟩⟩
    unfold incidentLoad
    rw [hfilter, card_image_of_injective _ (Sym2.map.injective hfinj)]
    exact incidentLoad_absorber M x

end PaperII.CertAbsorber
