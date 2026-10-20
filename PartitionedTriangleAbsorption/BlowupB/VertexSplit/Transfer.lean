/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Decomp
public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Div
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.UniversalF3

@[expose] public section

/-!
# Vertex splitting: universal absorbers come back from the split host (Theorem B)

`universalAbsorbers_of_split`: universal absorbers for the split family `F'` in the split host
`splitG G` (with degree constant `δ / t'²`) give universal absorbers for `F` in `G`. A reserve
`X` is split (degrees do not grow, and `|V| ≤ |V'|`), its absorber `A'` is projected back
(`A = π(A')`, degrees grow by at most the `t'` copies of a vertex, and `|V'| ≤ t' |V|`), and
decompositions come back by `hasDecomp_of_split`, divisibility goes forward by `isIntDiv_split`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.VertexSplit

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

variable {t t' : ℕ} {F : Finset (Multiset (Fin t))} (S : SplitData F t')
variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin t)

/-- The split host. -/
def splitG (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (SV S p) :=
  SimpleGraph.fromRel fun x y => s(x, y) ∈ splitE S p G.edgeFinset

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (splitG S p G).Adj := by
  unfold splitG; classical infer_instance

theorem splitE_loopless (G : SimpleGraph V) [DecidableRel G.Adj] {f : Sym2 (SV S p)}
    (hf : f ∈ splitE S p G.edgeFinset) : ¬ f.IsDiag := by
  induction f using Sym2.ind with
  | _ x y =>
    intro hd
    rw [Sym2.mk_isDiag_iff] at hd
    subst hd
    exact fst_ne_of_mem_splitE S p (fun e he => G.not_isDiag_of_mem_edgeFinset he) hf rfl

theorem edgeFinset_splitG (G : SimpleGraph V) [DecidableRel G.Adj] :
    (splitG S p G).edgeFinset = splitE S p G.edgeFinset := by
  ext f
  induction f using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [splitG, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · rwa [Sym2.eq_swap]
    · intro h
      refine ⟨fun hxy => splitE_loopless S p G h (by rw [hxy]; exact Sym2.mk_isDiag_iff.mpr rfl),
        Or.inl h⟩

/-- Degrees do not grow under splitting. -/
theorem card_filter_splitE_le (X : Finset (Sym2 V)) (x : SV S p) :
    ((splitE S p X).filter (x ∈ ·)).card ≤ (X.filter (fstV S p x ∈ ·)).card := by
  refine card_le_card_of_injOn (s := (splitE S p X).filter (x ∈ ·)) (t := X.filter (fstV S p x ∈ ·))
    (Sym2.map (fstV S p)) ?_ ?_
  · intro f hf
    obtain ⟨hfX, hxf⟩ := mem_filter.mp hf
    obtain ⟨e, he, rfl⟩ := mem_image.mp hfX
    rw [map_fst_splitEdge]
    exact mem_filter.mpr ⟨he, by
      have : fstV S p x ∈ Sym2.map (fstV S p) (splitEdge S p e) := Sym2.mem_map.mpr ⟨x, hxf, rfl⟩
      rwa [map_fst_splitEdge] at this⟩
  · intro f hf f' hf' h
    obtain ⟨e, -, rfl⟩ := mem_image.mp (mem_filter.mp hf).1
    obtain ⟨e', -, rfl⟩ := mem_image.mp (mem_filter.mp hf').1
    simp only [map_fst_splitEdge] at h
    rw [h]

theorem card_V_le : Fintype.card V ≤ Fintype.card (SV S p) :=
  Fintype.card_le_of_injective (fun v => cp S p v (p v)) fun u v h => congrArg (fstV S p) h

theorem card_SV_le : Fintype.card (SV S p) ≤ t' * Fintype.card V := by
  have h := Fintype.card_le_of_injective (fun x : SV S p => x.1) Subtype.val_injective
  simpa [Fintype.card_prod, Fintype.card_fin, mul_comm] using h

/-- The copies of a vertex. -/
def copies (v : V) : Finset (SV S p) := univ.filter fun x => fstV S p x = v

theorem card_copies_le (v : V) : (copies S p v).card ≤ t' := by
  have := card_le_card_of_injOn (sp S p) (s := copies S p v) (t := (univ : Finset (Fin t'))) (fun _ _ => mem_coe.mpr
    (mem_univ _)) (fun x hx y hy h => by
      have hx' := (mem_filter.mp (mem_coe.mp hx)).2
      have hy' := (mem_filter.mp (mem_coe.mp hy)).2
      apply Subtype.ext
      exact Prod.ext (hx'.trans hy'.symm) h)
  simpa using this

/-- Degrees of a projected edge set: at most `t'` times the split degree. -/
theorem card_filter_proj_le (A' : Finset (Sym2 (SV S p))) (v : V) (D : ℕ)
    (hD : ∀ x : SV S p, (A'.filter (x ∈ ·)).card ≤ D) :
    ((A'.image (Sym2.map (fstV S p))).filter (v ∈ ·)).card ≤ t' * D := by
  classical
  have hsub : (A'.image (Sym2.map (fstV S p))).filter (v ∈ ·) ⊆
      ((copies S p v).biUnion fun x => A'.filter (x ∈ ·)).image (Sym2.map (fstV S p)) := by
    intro e he
    obtain ⟨heA, hve⟩ := mem_filter.mp he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp heA
    obtain ⟨x, hx, hxv⟩ := Sym2.mem_map.mp hve
    exact mem_image.mpr ⟨f, mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hxv⟩,
      mem_filter.mpr ⟨hf, hx⟩⟩, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ((copies S p v).biUnion fun x => A'.filter (x ∈ ·)).card := card_image_le
    _ ≤ ∑ x ∈ copies S p v, (A'.filter (x ∈ ·)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ copies S p v, D := sum_le_sum fun x _ => hD x
    _ = (copies S p v).card * D := by rw [sum_const, smul_eq_mul]
    _ ≤ t' * D := Nat.mul_le_mul_right _ (card_copies_le S p v)

/-- **Theorem B of the written proof.** -/
theorem universalAbsorbers_of_split (hC : S.Compat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ρ δ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (ht' : 0 < t')
    (hU : UniversalAbsorbers (sp S p) S.F' (splitG S p G) ρ (δ / ((t' : ℝ) * t'))) :
    UniversalAbsorbers p F G ρ δ := by
  classical
  intro X hXG hX
  have hV : (Fintype.card V : ℝ) ≤ Fintype.card (SV S p) := by exact_mod_cast card_V_le S p
  have hV' : (Fintype.card (SV S p) : ℝ) ≤ t' * Fintype.card V := by exact_mod_cast card_SV_le S p
  have hX'G : splitE S p X ⊆ (splitG S p G).edgeFinset := by
    rw [edgeFinset_splitG]; exact image_subset_image hXG
  have hX' : DegBounded (splitE S p X) (2 * ρ * Fintype.card (SV S p)) := by
    intro x
    have h1 : (((splitE S p X).filter (x ∈ ·)).card : ℝ) ≤ (X.filter (fstV S p x ∈ ·)).card := by
      exact_mod_cast card_filter_splitE_le S p X x
    have h2 := hX (fstV S p x)
    have h3 : 2 * ρ * (Fintype.card V : ℝ) ≤ 2 * ρ * Fintype.card (SV S p) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    exact h1.trans (h2.trans h3)
  obtain ⟨A', hA'G, hA'X, hA'dec, hA'deg, hA'all⟩ := hU (splitE S p X) hX'G hX'
  have hA'sub : A' ⊆ splitE S p G.edgeFinset := by rw [← edgeFinset_splitG]; exact hA'G
  set A := A'.image (Sym2.map (fstV S p)) with hAdef
  have hAsplit : splitE S p A = A' := by
    ext f
    constructor
    · intro hf
      obtain ⟨e, he, rfl⟩ := mem_image.mp hf
      obtain ⟨f', hf', rfl⟩ := mem_image.mp he
      rw [(splitEdge_map_fst S p (hA'sub hf')).1]; exact hf'
    · intro hf
      rw [← (splitEdge_map_fst S p (hA'sub hf)).1]
      exact mem_image_of_mem _ (mem_image_of_mem _ hf)
  have hAG : A ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    exact (splitEdge_map_fst S p (hA'sub hf)).2
  have hloopG : ∀ B ⊆ G.edgeFinset, ∀ e ∈ B, ¬ e.IsDiag :=
    fun B hB e he => G.not_isDiag_of_mem_edgeFinset (hB he)
  refine ⟨A, hAG, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro e heA heX
    have h1 : splitEdge S p e ∈ A' := by rw [← hAsplit]; exact mem_image_of_mem _ heA
    exact disjoint_left.mp hA'X h1 (mem_image_of_mem _ heX)
  · exact hasDecomp_of_split S p (hloopG A hAG) (by rw [hAsplit]; exact hA'dec)
  · intro v
    have hD : ∀ x : SV S p, (A'.filter (x ∈ ·)).card ≤
        ⌊2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)⌋₊ := fun x =>
      Nat.le_floor (hA'deg x)
    have h1 := card_filter_proj_le S p A' v _ hD
    have ht'R : (0 : ℝ) < t' := by exact_mod_cast ht'
    have h2 : ((t' * ⌊2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)⌋₊ : ℕ) : ℝ) ≤
        t' * (2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by
        have := hA'deg (cp S p v (p v))
        exact (Nat.cast_nonneg _).trans this)) ht'R.le
    have h3 : (t' : ℝ) * (2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)) ≤
        2 * δ * Fintype.card V := by
      have : (t' : ℝ) * (2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)) =
          2 * δ * (Fintype.card (SV S p) / t') := by field_simp
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ ht'R]; linarith
    have h1' : (((A.filter (v ∈ ·)).card : ℕ) : ℝ) ≤
        ((t' * ⌊2 * (δ / ((t' : ℝ) * t')) * Fintype.card (SV S p)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans (h2.trans h3)
  · intro L hLX hLdiv
    have hL' : splitE S p L ⊆ splitE S p X := image_subset_image hLX
    have hdec := hA'all (splitE S p L) hL' (isIntDiv_split S p hC hLdiv)
    rw [← hAsplit, ← splitE_union] at hdec
    exact hasDecomp_of_split S p (hloopG (A ∪ L) (union_subset hAG (hLX.trans hXG))) hdec

/-- **Theorem B with absolute degree bounds**: a reserve of degree `≤ R` in `G` splits to a reserve
of degree `≤ R`; an absorber of degree `≤ D` in the split host projects to one of degree `≤ t' D`. -/
theorem absorbers_of_split_abs (hC : S.Compat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (R D : ℝ) (hD0 : 0 ≤ D)
    (hU : ∀ X' : Finset (Sym2 (SV S p)), X' ⊆ (splitG S p G).edgeFinset → DegBounded X' R →
      ∃ A' : Finset (Sym2 (SV S p)), A' ⊆ (splitG S p G).edgeFinset ∧ Disjoint A' X' ∧
        HasDecomp (sp S p) S.F' A' ∧ DegBounded A' D ∧
        ∀ L' ⊆ X', IsIntDiv (sp S p) S.F' L' → HasDecomp (sp S p) S.F' (A' ∪ L')) :
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X R →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ HasDecomp p F A ∧
        DegBounded A (t' * D) ∧ ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L) := by
  classical
  intro X hXG hX
  have hX'G : splitE S p X ⊆ (splitG S p G).edgeFinset := by
    rw [edgeFinset_splitG]; exact image_subset_image hXG
  have hX' : DegBounded (splitE S p X) R := by
    intro x
    have h1 : (((splitE S p X).filter (x ∈ ·)).card : ℝ) ≤ (X.filter (fstV S p x ∈ ·)).card := by
      exact_mod_cast card_filter_splitE_le S p X x
    exact h1.trans (hX (fstV S p x))
  obtain ⟨A', hA'G, hA'X, hA'dec, hA'deg, hA'all⟩ := hU (splitE S p X) hX'G hX'
  have hA'sub : A' ⊆ splitE S p G.edgeFinset := by rw [← edgeFinset_splitG]; exact hA'G
  set A := A'.image (Sym2.map (fstV S p)) with hAdef
  have hAsplit : splitE S p A = A' := by
    ext f
    constructor
    · intro hf
      obtain ⟨e, he, rfl⟩ := mem_image.mp hf
      obtain ⟨f', hf', rfl⟩ := mem_image.mp he
      rw [(splitEdge_map_fst S p (hA'sub hf')).1]; exact hf'
    · intro hf
      rw [← (splitEdge_map_fst S p (hA'sub hf)).1]
      exact mem_image_of_mem _ (mem_image_of_mem _ hf)
  have hAG : A ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    exact (splitEdge_map_fst S p (hA'sub hf)).2
  have hloopG : ∀ B ⊆ G.edgeFinset, ∀ e ∈ B, ¬ e.IsDiag :=
    fun B hB e he => G.not_isDiag_of_mem_edgeFinset (hB he)
  refine ⟨A, hAG, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro e heA heX
    have h1 : splitEdge S p e ∈ A' := by rw [← hAsplit]; exact mem_image_of_mem _ heA
    exact disjoint_left.mp hA'X h1 (mem_image_of_mem _ heX)
  · exact hasDecomp_of_split S p (hloopG A hAG) (by rw [hAsplit]; exact hA'dec)
  · intro v
    have hD : ∀ x : SV S p, (A'.filter (x ∈ ·)).card ≤ ⌊D⌋₊ := fun x => Nat.le_floor (hA'deg x)
    have h1 := card_filter_proj_le S p A' v _ hD
    have h1' : (((A.filter (v ∈ ·)).card : ℕ) : ℝ) ≤ ((t' * ⌊D⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : ((t' * ⌊D⌋₊ : ℕ) : ℝ) ≤ t' * D := by
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hD0) (Nat.cast_nonneg _)
    exact h1'.trans h2
  · intro L hLX hLdiv
    have hL' : splitE S p L ⊆ splitE S p X := image_subset_image hLX
    have hdec := hA'all (splitE S p L) hL' (isIntDiv_split S p hC hLdiv)
    rw [← hAsplit, ← splitE_union] at hdec
    exact hasDecomp_of_split S p (hloopG (A ∪ L) (union_subset hAG (hLX.trans hXG))) hdec

end PartitionedTriangleAbsorption.BlowupB.VertexSplit

#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.universalAbsorbers_of_split
#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.absorbers_of_split_abs
