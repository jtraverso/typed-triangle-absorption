/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.VertexLayers
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TemplateTransport

@[expose] public section

/-!
# Physical tokens rooted at one vertex

A rooted template is a loopless even edge set on `Fin (m + 1)` with at most `g` edges and
labels; its root is `0`.
`rooted_copies` embeds one copy of a template per token identity (`+` tokens use `Tp`, `-` tokens
use `Tm`) into the host `G`, all with root `x`, pairwise edge-disjoint, avoiding a bounded edge set
`B`, with internal vertices outside a vertex set `Z` and distinct across tokens.
It is the sequential guarded embedding (`guarded_exists_embedding`) with the root fixed.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t m g : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {ι : Type*}

/-- The image of an edge set on `Fin n` under a vertex map. -/
def mappedM {n : ℕ} (E : Finset (Sym2 (Fin n))) (f : Fin n → W) : Finset (Sym2 W) :=
  E.image (Sym2.map f)

/-- A rooted token template on `Fin (m + 1)` with at most `g` edges, root `0`. -/
structure RootedTemplate (t m g : ℕ) where
  E : Finset (Sym2 (Fin (m + 1)))
  L : Fin (m + 1) → Fin t
  loop : ∀ e ∈ E, ¬ e.IsDiag
  even : ∀ w, Even (incidentLoad E w)
  card : E.card ≤ g

/-- The template of a token identity. -/
def tmpl (Tp Tm : RootedTemplate t m g) (τ : Tok ι) : RootedTemplate t m g :=
  if τ.sign then Tp else Tm

/-- Rooted copies of the templates, one per token identity of `S`. -/
structure RootedCopies (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (B : Finset (Sym2 W)) (Z : Finset W) (x : W) (T : Tok ι → RootedTemplate t m g)
    (S : Finset (Tok ι)) (f : Tok ι → Fin (m + 1) → W) : Prop where
  injective : ∀ τ ∈ S, Function.Injective (f τ)
  root : ∀ τ ∈ S, f τ 0 = x
  labels : ∀ τ ∈ S, ∀ j, p (f τ j) = (T τ).L j
  subgraph : ∀ τ ∈ S, mappedM (T τ).E (f τ) ⊆ G.edgeFinset
  avoid : ∀ τ ∈ S, Disjoint (mappedM (T τ).E (f τ)) B
  disjoint : (S : Set (Tok ι)).PairwiseDisjoint fun τ => mappedM (T τ).E (f τ)
  outside : ∀ τ ∈ S, ∀ j, j ≠ 0 → f τ j ∉ Z
  internal : ∀ τ ∈ S, ∀ τ' ∈ S, τ ≠ τ' → ∀ j j', j ≠ 0 → f τ j ≠ f τ' j'

theorem incidentLoad_mapped_le {n : ℕ} (E : Finset (Sym2 (Fin n))) (h : E.card ≤ g)
    (f : Fin n → W) (v : W) : incidentLoad (mappedM E f) v ≤ g :=
  (PrivateFamily.incidentLoad_le_card _ v).trans (card_image_le.trans h)

/-- The rooted embedding of one template. -/
theorem rooted_copy (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (T : RootedTemplate t m g)
    (hproper : ∀ i j, s(i, j) ∈ T.E → Allowed (T.L i) (T.L j))
    (x : W) (hx : p x = T.L 0)
    (a d : ℝ) (hs : GuardedSupply p G Allowed (m + 1) a)
    (B : Finset (Sym2 W)) (Z : Finset W) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : ((m + 1 : ℕ) : ℝ) + (Z.card : ℝ) + ((m + 1 : ℕ) : ℝ) * d < a) :
    ∃ e : Fin (m + 1) ↪ W, (∀ j, p (e j) = T.L j) ∧ e 0 = x ∧
      mappedM T.E e ⊆ G.edgeFinset ∧ Disjoint (mappedM T.E e) B ∧ ∀ j, j ≠ 0 → e j ∉ Z := by
  classical
  let TG : SimpleGraph (Fin (m + 1)) := SimpleGraph.fromEdgeSet T.E
  have hadj (i j : Fin (m + 1)) (hij : s(i, j) ∈ T.E) : TG.Adj i j := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact T.loop _ hij (by simp [heq])
  have hT : ∀ i j, TG.Adj i j → Allowed (T.L i) (T.L j) :=
    fun i j hij => hproper i j ((SimpleGraph.fromEdgeSet_adj _).mp hij).1
  let rootMap : Fin (m + 1) → W := fun _ => x
  have hroot : PartialEmbedding TG G B {0} rootMap := by
    constructor
    · intro i hi j hj _
      rw [mem_singleton.mp hi, mem_singleton.mp hj]
    · intro i hi j hj hij
      rw [mem_singleton.mp hi, mem_singleton.mp hj] at hij
      exact absurd hij (TG.irrefl)
  obtain ⟨e, hlabel, hgr, hedges, havoid⟩ := guarded_exists_embedding TG G p T.L Allowed hT
    a d (by simpa using hs) B Z hB hd (by simpa using hbudget) {0} rootMap hroot
    (by intro i hi; rw [mem_singleton.mp hi]; exact hx)
  refine ⟨e, hlabel, hgr 0 (mem_singleton_self _), ?_, ?_,
    fun j hj => havoid j (by simpa using hj)⟩
  · intro d' he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact SimpleGraph.mem_edgeFinset.mpr (hedges i j (hadj i j he')).1
  · rw [disjoint_left]
    intro d' he hB'
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact (hedges i j (hadj i j he')).2 hB'

/-- **Rooted copies of a token family.** -/
theorem rooted_copies (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (Tp Tm : RootedTemplate t m g)
    (hpP : ∀ i j, s(i, j) ∈ Tp.E → Allowed (Tp.L i) (Tp.L j))
    (hpM : ∀ i j, s(i, j) ∈ Tm.E → Allowed (Tm.L i) (Tm.L j))
    (x : W) (hxP : p x = Tp.L 0) (hxM : p x = Tm.L 0)
    (a d : ℝ) (hs : GuardedSupply p G Allowed (m + 1) a)
    (B : Finset (Sym2 W)) (Z : Finset W) (hB : DegBounded B d) (hd : 0 ≤ d)
    (S : Finset (Tok ι))
    (hbudget : ((m + 1 : ℕ) : ℝ) + ((Z.card : ℝ) + ((m + 1 : ℕ) : ℝ) * S.card) +
      ((m + 1 : ℕ) : ℝ) * (d + g * S.card) < a) :
    ∃ f : Tok ι → Fin (m + 1) → W, RootedCopies p G B Z x (tmpl Tp Tm) S f := by
  classical
  have hp : ∀ τ : Tok ι, ∀ i j, s(i, j) ∈ (tmpl Tp Tm τ).E →
      Allowed ((tmpl Tp Tm τ).L i) ((tmpl Tp Tm τ).L j) := by
    intro τ; unfold tmpl; split_ifs
    · exact hpP
    · exact hpM
  have hx : ∀ τ : Tok ι, p x = (tmpl Tp Tm τ).L 0 := by
    intro τ; unfold tmpl; split_ifs
    · exact hxP
    · exact hxM
  have H : ∀ K : Finset (Tok ι), K ⊆ S → ∃ f, RootedCopies p G B Z x (tmpl Tp Tm) K f := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => x, ?_⟩
      constructor <;> simp
    | @insert j K hj ih =>
      intro hKs
      have hK : K ⊆ S := fun i hi => hKs (mem_insert_of_mem hi)
      obtain ⟨f, hf⟩ := ih hK
      let U := K.biUnion fun τ => mappedM (tmpl Tp Tm τ).E (f τ)
      let Int := K.biUnion fun τ => (univ.erase (0 : Fin (m + 1))).image (f τ)
      have hUd : DegBounded U (g * K.card) := by
        intro v
        have h1 : incidentLoad U v ≤ ∑ τ ∈ K, incidentLoad (mappedM (tmpl Tp Tm τ).E (f τ)) v :=
          incidentLoad_biUnion_le _ _ v
        have h2 : ∑ τ ∈ K, incidentLoad (mappedM (tmpl Tp Tm τ).E (f τ)) v ≤ ∑ _τ ∈ K, g :=
          sum_le_sum fun τ _ => incidentLoad_mapped_le _ (tmpl Tp Tm τ).card _ v
        have h3 : (incidentLoad U v : ℝ) ≤ g * K.card := by
          have := h1.trans h2
          rw [sum_const, smul_eq_mul] at this
          have : (incidentLoad U v : ℝ) ≤ (K.card * g : ℕ) := by exact_mod_cast this
          push_cast at this
          linarith
        exact h3
      have hInt : (Int.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * K.card := by
        have h1 : Int.card ≤ ∑ τ ∈ K, ((univ.erase (0 : Fin (m + 1))).image (f τ)).card :=
          card_biUnion_le
        have h2 : ∑ τ ∈ K, ((univ.erase (0 : Fin (m + 1))).image (f τ)).card ≤
            ∑ _τ ∈ K, (m + 1) :=
          sum_le_sum fun τ _ => card_image_le.trans (card_erase_le.trans (by simp))
        have := h1.trans h2
        rw [sum_const, smul_eq_mul] at this
        have : (Int.card : ℝ) ≤ (K.card * (m + 1) : ℕ) := by exact_mod_cast this
        push_cast at this ⊢
        linarith
      have hKS : (K.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hK
      have hBU : DegBounded (B ∪ U) (d + g * K.card) := degree_union hB hUd
      have hZI : ((Z ∪ Int).card : ℝ) ≤ Z.card + ((m + 1 : ℕ) : ℝ) * K.card := by
        have : (Z ∪ Int).card ≤ Z.card + Int.card := card_union_le _ _
        have : ((Z ∪ Int).card : ℝ) ≤ Z.card + Int.card := by exact_mod_cast this
        linarith
      have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      have hg0' : (0 : ℝ) ≤ (g : ℝ) := by positivity
      obtain ⟨e, hglabel, hg0, hgG, hgavoid, hgZ⟩ := rooted_copy p G Allowed (tmpl Tp Tm j)
        (hp j) x (hx j) a (d + g * K.card) hs (B ∪ U) (Z ∪ Int) hBU (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hKS hm0, mul_le_mul_of_nonneg_left hKS hg0',
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKS hg0') hm0])
      let f' : Tok ι → Fin (m + 1) → W := fun i => if i = j then e else f i
      have hfj : f' j = e := by simp [f']
      have hfi : ∀ i ∈ K, f' i = f i := fun i hi => by
        have hij : i ≠ j := fun hij => hj (hij ▸ hi)
        simp only [f', ite_eq_right hij]
      have hAU : Disjoint (mappedM (tmpl Tp Tm j).E e) U := hgavoid.mono_right subset_union_right
      have hAi : ∀ i ∈ K, Disjoint (mappedM (tmpl Tp Tm j).E e) (mappedM (tmpl Tp Tm i).E (f i)) :=
        fun i hi => hAU.mono_right (subset_biUnion_of_mem
          (fun i => mappedM (tmpl Tp Tm i).E (f i)) hi)
      have hgInt : ∀ k, k ≠ 0 → ∀ i ∈ K, ∀ k', e k ≠ f i k' := by
        intro k hk i hi k' he
        by_cases hk0 : k' = 0
        · -- `f i 0 = x = e 0`, contradicting injectivity of `g`
          have : e k = e 0 := by rw [he, hk0, hf.root i hi, hg0]
          exact hk (e.injective this)
        · exact hgZ k hk (mem_union.mpr (Or.inr (mem_biUnion.mpr
            ⟨i, hi, mem_image.mpr ⟨k', by simpa using hk0, he.symm⟩⟩)))
      refine ⟨f', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact e.injective
        · rw [hfi i hi]; exact hf.injective i hi
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hg0
        · rw [hfi i hi]; exact hf.root i hi
      · intro i hi k
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hglabel k
        · rw [hfi i hi]; exact hf.labels i hi k
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hgG
        · rw [hfi i hi]; exact hf.subgraph i hi
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hgavoid.mono_right subset_union_left
        · rw [hfi i hi]; exact hf.avoid i hi
      · intro i hi k hk hik
        change Disjoint (mappedM (tmpl Tp Tm i).E (f' i)) (mappedM (tmpl Tp Tm k).E (f' k))
        rcases mem_insert.mp hi with hij | hiK
        · subst i
          rcases mem_insert.mp hk with hkj | hkK
          · subst k; exact False.elim (hik rfl)
          · rw [hfj, hfi k hkK]; exact hAi k hkK
        · rcases mem_insert.mp hk with hkj | hkK
          · subst k; rw [hfi i hiK, hfj]; exact (hAi i hiK).symm
          · rw [hfi i hiK, hfi k hkK]; exact hf.disjoint hiK hkK hik
      · intro i hi k hk
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact fun hz => hgZ k hk (mem_union.mpr (Or.inl hz))
        · rw [hfi i hi]; exact hf.outside i hi k hk
      · intro i hi i' hi' hii k k' hk
        rcases mem_insert.mp hi with rfl | hiK
        · rcases mem_insert.mp hi' with rfl | hi'K
          · exact absurd rfl hii
          · rw [hfj, hfi i' hi'K]; exact hgInt k hk i' hi'K k'
        · rcases mem_insert.mp hi' with rfl | hi'K
          · rw [hfi i hiK, hfj]
            intro he
            by_cases hk0 : k' = 0
            · have : f i k = f i 0 := by rw [he, hk0, hg0, hf.root i hiK]
              exact hk (hf.injective i hiK this)
            · exact hgInt k' hk0 i hiK k he.symm
          · rw [hfi i hiK, hfi i' hi'K]; exact hf.internal i hiK i' hi'K hii k k' hk
  exact H S le_rfl

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.rooted_copies
