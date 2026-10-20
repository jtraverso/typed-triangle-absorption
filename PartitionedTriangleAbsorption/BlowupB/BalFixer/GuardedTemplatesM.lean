/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTemplates

@[expose] public section

/-!
# Sparse families of templates on `Fin n` (`n ≤ 12`)

`GuardedTemplates` for templates with `n` positions instead of six: injective guarded embeddings,
pairwise disjoint physical edges avoiding a ledger `B`, bounded total incidence. The scaled form
(`guarded_template_family_scaled_m`) takes `n ≤ 12`, a ledger of degree `≤ 12 λ |V|` and at most
`2^22 ρ |V|²` copies, under the same scales as the six-position version.
-/

namespace PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplatesM

open Finset AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates

variable {V I : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def mappedN {n : ℕ} (E : Finset (Sym2 (Fin n))) (f : Fin n → V) : Finset (Sym2 V) :=
  E.image (Sym2.map f)

theorem guarded_template_copy_m [Nonempty V] (n : ℕ)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop)
    (E : Finset (Sym2 (Fin n))) (label : Fin n → Fin t)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hproper : ∀ i j, s(i, j) ∈ E → Allowed (label i) (label j))
    (a d : ℝ) (hs : GuardedSupply p G Allowed n a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (n : ℝ) + (Z.card : ℝ) + n * d < a) :
    ∃ f : Fin n ↪ V, (∀ i, p (f i) = label i) ∧
      mappedN E f ⊆ G.edgeFinset ∧ Disjoint (mappedN E f) B ∧ ∀ i, f i ∉ Z := by
  classical
  let T : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet E
  have hadj (i j : Fin n) (hij : s(i, j) ∈ E) : T.Adj i j := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact hloop _ hij (by simp [heq])
  have hT : ∀ i j, T.Adj i j → Allowed (label i) (label j) :=
    fun i j hij => hproper i j ((SimpleGraph.fromEdgeSet_adj _).mp hij).1
  let rootMap : Fin n → V := fun _ => Classical.choice (inferInstance : Nonempty V)
  have hroot : PartialEmbedding T G B ∅ rootMap := by
    constructor <;> simp
  obtain ⟨f, hlabel, _, hedges, havoid⟩ := guarded_exists_embedding T G p label Allowed hT
    a d (by simpa using hs) B Z hB hd (by simpa using hbudget) ∅ rootMap hroot (by simp)
  refine ⟨f, hlabel, ?_, ?_, fun i => havoid i (by simp)⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact SimpleGraph.mem_edgeFinset.mpr (hedges i j (hadj i j he')).1
  · rw [disjoint_left]
    intro e he hB'
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact (hedges i j (hadj i j he')).2 hB'

structure CopiesM (n : ℕ) (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (E : I → Finset (Sym2 (Fin n)))
    (label : I → Fin n → Fin t) (T : ℝ) (s : Finset I) (f : I → Fin n → V) : Prop where
  injective : ∀ i ∈ s, Function.Injective (f i)
  labels : ∀ i ∈ s, ∀ j, p (f i j) = label i j
  subgraph : ∀ i ∈ s, mappedN (E i) (f i) ⊆ G.edgeFinset
  avoid : ∀ i ∈ s, Disjoint (mappedN (E i) (f i)) B
  disjoint : (s : Set I).PairwiseDisjoint (fun i => mappedN (E i) (f i))
  degree : DegBounded (s.biUnion fun i => mappedN (E i) (f i)) (T + n)
  card : (s.biUnion fun i => mappedN (E i) (f i)).card ≤ s.card * n

theorem CopiesM.incidence {n : ℕ} {p : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset (Sym2 V)} {E : I → Finset (Sym2 (Fin n))}
    {label : I → Fin n → Fin t} {T : ℝ} {s : Finset I} {f : I → Fin n → V}
    (h : CopiesM n p G B E label T s f) (v : V) :
    ((∑ i ∈ s, incidentLoad (mappedN (E i) (f i)) v : ℕ) : ℝ) ≤ T + n := by
  have heq : ∑ i ∈ s, incidentLoad (mappedN (E i) (f i)) v =
      incidentLoad (s.biUnion fun i => mappedN (E i) (f i)) v := by
    unfold incidentLoad
    rw [filter_biUnion, card_biUnion]
    intro i hi j hj hij
    exact disjoint_filter_filter (h.disjoint hi hj hij)
  rw [heq]
  exact h.degree v

theorem guarded_template_family_m [Nonempty V] (n : ℕ)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (s : Finset I)
    (E : I → Finset (Sym2 (Fin n))) (label : I → Fin n → Fin t)
    (hloop : ∀ i ∈ s, ∀ e ∈ E i, ¬ e.IsDiag)
    (hproper : ∀ i ∈ s, ∀ x y, s(x, y) ∈ E i → Allowed (label i x) (label i y))
    (hcard : ∀ i ∈ s, (E i).card ≤ n)
    (a d T : ℝ) (hs : GuardedSupply p G Allowed n a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d) (hT : 0 < T)
    (hbudget : (n : ℝ) + n * (d + T + n) < a / 2)
    (hcount : 4 * (n : ℝ) * (s.card : ℝ) ≤ T * a) :
    ∃ f : I → Fin n → V, CopiesM n p G B E label T s f := by
  classical
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have H : ∀ K : Finset I, K ⊆ s → ∃ f, CopiesM n p G B E label T K f := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => Classical.choice (inferInstance : Nonempty V), ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [biUnion_empty, filter_empty, card_empty, Nat.cast_zero]
        linarith
      · simp
    | @insert j K hj ih =>
      intro hKs
      have hjS : j ∈ s := hKs (mem_insert_self _ _)
      have hK : K ⊆ s := fun i hi => hKs (mem_insert_of_mem hi)
      obtain ⟨f, hf⟩ := ih hK
      let U := K.biUnion fun i => mappedN (E i) (f i)
      let High : Finset V := univ.filter fun v => T < (incidentLoad U v : ℝ)
      have hcountU : 4 * (U.card : ℝ) ≤ T * a := by
        have h1 : (U.card : ℝ) ≤ K.card * n := by exact_mod_cast hf.card
        have h2 : (K.card : ℝ) ≤ s.card := by exact_mod_cast card_le_card hK
        have h3 := mul_le_mul_of_nonneg_right h2 hn0
        nlinarith
      have hHigh : (High.card : ℝ) ≤ a / 2 := by
        have hc := PrivateFamily.card_highLoad_le U T
        change (High.card : ℝ) * T ≤ 2 * U.card at hc
        nlinarith
      have hBU : DegBounded (B ∪ U) (d + T + n) := by
        convert degree_union hB hf.degree using 1
        ring
      obtain ⟨g, hglabel, hgG, hgavoid, hgHigh⟩ := guarded_template_copy_m n p G Allowed (E j)
        (label j) (hloop j hjS) (hproper j hjS) a (d + T + n) hs (B ∪ U) High hBU
        (by positivity) (by nlinarith)
      let f' : I → Fin n → V := fun i => if i = j then g else f i
      have hfj : f' j = g := by simp [f']
      have hfi : ∀ i ∈ K, f' i = f i := fun i hi => by
        have hij : i ≠ j := by
          intro hij
          exact hj (hij ▸ hi)
        simp only [f', ite_eq_right hij]
      let A := mappedN (E j) g
      have hAc : A.card ≤ n := card_image_le.trans (hcard j hjS)
      have hAB : Disjoint A B := hgavoid.mono_right subset_union_left
      have hAU : Disjoint A U := hgavoid.mono_right subset_union_right
      have hAi : ∀ i ∈ K, Disjoint A (mappedN (E i) (f i)) := fun i hi =>
        hAU.mono_right (subset_biUnion_of_mem (fun i => mappedN (E i) (f i)) hi)
      have hbig : ((insert j K).biUnion fun i => mappedN (E i) (f' i)) = U ∪ A := by
        rw [biUnion_insert, hfj, union_comm]
        congr 1
        exact biUnion_congr rfl fun i hi => by rw [hfi i hi]
      refine ⟨f', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact g.injective
        · rw [hfi i hi]; exact hf.injective i hi
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
        · rw [hfj]; exact hAB
        · rw [hfi i hi]; exact hf.avoid i hi
      · intro i hi k hk hik
        change Disjoint (mappedN (E i) (f' i)) (mappedN (E k) (f' k))
        rcases mem_insert.mp hi with hij | hiK
        · subst i
          rcases mem_insert.mp hk with hkj | hkK
          · subst k; exact False.elim (hik rfl)
          · rw [hfj, hfi k hkK]; exact hAi k hkK
        · rcases mem_insert.mp hk with hkj | hkK
          · subst k; rw [hfi i hiK, hfj]; exact (hAi i hiK).symm
          · rw [hfi i hiK, hfi k hkK]; exact hf.disjoint hiK hkK hik
      · intro v
        change (incidentLoad ((insert j K).biUnion fun i => mappedN (E i) (f' i)) v : ℝ) ≤ T + n
        rw [hbig, PrivateFamily.incidentLoad_union hAU.symm]
        have hAv : (incidentLoad A v : ℝ) ≤ n := by
          exact_mod_cast (PrivateFamily.incidentLoad_le_card A v).trans hAc
        by_cases hv : v ∈ vertSet A
        · have hvHigh : v ∉ High := by
            obtain ⟨e, he, hve⟩ := SignedHinge.mem_vertSet.mp hv
            obtain ⟨e', he', rfl⟩ := mem_image.mp he
            obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hve
            exact hgHigh w
          have hUv : (incidentLoad U v : ℝ) ≤ T :=
            le_of_not_gt fun h => hvHigh (mem_filter.mpr ⟨mem_univ _, h⟩)
          push_cast
          linarith
        · rw [PrivateFamily.incidentLoad_eq_zero hv, add_zero]
          exact hf.degree v
      · rw [hbig, card_insert_of_notMem hj, add_mul, one_mul]
        exact (card_union_le U A).trans (Nat.add_le_add hf.card hAc)
  exact H s le_rfl

theorem template_scalar_budget_m (ω lam rho N k nn : ℝ) (hnn0 : 0 ≤ nn) (hnn : nn ≤ 12)
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hN0 : 0 ≤ N) (hn1 : 1 ≤ rho * N) (hk : k ≤ 2 ^ 22 * rho * N ^ 2) :
    0 < N ∧ 0 < lam * N / 2 ∧
      nn + nn * (12 * lam * N + lam * N / 2 + nn) < ω * N / 2 ∧
      4 * nn * k ≤ (lam * N / 2) * (ω * N) ∧ lam * N / 2 + nn ≤ lam * N := by
  have hN : 0 < N := by nlinarith only [hn1, hrho.le, hN0]
  have hlam1 : lam ≤ 1 := by linarith only [hlamω, hω, hlam.le]
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith only [hlam1, hlam.le]
  have hrholam : 24 * rho ≤ lam := by
    norm_num at hscale
    nlinarith only [hscale, hlam2, hrho.le]
  have hnlam : 24 ≤ lam * N := by
    have h1 := mul_le_mul_of_nonneg_left hn1 (show (0 : ℝ) ≤ 24 by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hrholam hN0
    nlinarith only [h1, h2]
  have hlnωn := mul_le_mul_of_nonneg_right hlamω hN0
  have hbudget : nn + nn * (12 * lam * N + lam * N / 2 + nn) < ω * N / 2 := by
    have h1 : nn * (12 * lam * N + lam * N / 2 + nn) ≤ 12 * (12 * lam * N + lam * N / 2 + 12) :=
      mul_le_mul hnn (by linarith) (by positivity) (by norm_num)
    nlinarith only [h1, hnn, hnlam, hlnωn]
  have hcoef : 48 * (2 ^ 22 : ℝ) * rho ≤ lam * ω / 2 := by
    have hll := mul_le_mul_of_nonneg_left hlamω hlam.le
    norm_num at hscale ⊢
    nlinarith only [hscale, hll, sq_nonneg lam]
  have hk0 : 0 ≤ k ∨ k < 0 := le_or_gt 0 k
  have hcount : 4 * nn * k ≤ (lam * N / 2) * (ω * N) := by
    rcases hk0 with hk0 | hk0
    · calc 4 * nn * k ≤ 48 * k := by nlinarith
        _ ≤ 48 * (2 ^ 22 * rho * N ^ 2) := mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = (48 * 2 ^ 22 * rho) * N ^ 2 := by ring
        _ ≤ (lam * ω / 2) * N ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg N)
        _ = _ := by ring
    · have : 4 * nn * k ≤ 0 := by nlinarith
      have : 0 ≤ (lam * N / 2) * (ω * N) := by
        have : 0 ≤ ω := le_trans (by positivity) hlamω
        positivity
      linarith
  exact ⟨hN, by positivity, hbudget, hcount, by linarith only [hnlam, hnn]⟩

/-- **Templates on `Fin n`, `n ≤ 12`, under the common scales.** -/
theorem guarded_template_family_scaled_m (n : ℕ) (hn : n ≤ 12)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (s : Finset I)
    (E : I → Finset (Sym2 (Fin n))) (label : I → Fin n → Fin t)
    (hloop : ∀ i ∈ s, ∀ e ∈ E i, ¬ e.IsDiag)
    (hproper : ∀ i ∈ s, ∀ x y, s(x, y) ∈ E i → Allowed (label i x) (label i y))
    (hcard : ∀ i ∈ s, (E i).card ≤ n)
    (ω lam rho : ℝ) (hs : GuardedSupply p G Allowed n (ω * Fintype.card V))
    (B : Finset (Sym2 V)) (hB : DegBounded B (12 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (s.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ f : I → Fin n → V,
      CopiesM n p G B E label (lam * Fintype.card V / 2) s f ∧
      ∀ v, ((∑ i ∈ s, incidentLoad (mappedN (E i) (f i)) v : ℕ) : ℝ) ≤
        lam * Fintype.card V := by
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  obtain ⟨hN, hT, hbudget, htokens, hfinal⟩ := template_scalar_budget_m ω lam rho
    (Fintype.card V) s.card n (Nat.cast_nonneg _) hnR hω hlam hlamω hrho hscale (Nat.cast_nonneg _)
    hn1 hcount
  have hnNat : 0 < Fintype.card V := by exact_mod_cast hN
  let : Nonempty V := Fintype.card_pos_iff.mp hnNat
  obtain ⟨f, hf⟩ := guarded_template_family_m n p G Allowed s E label hloop hproper hcard
    (ω * Fintype.card V) (12 * lam * Fintype.card V) (lam * Fintype.card V / 2) hs B hB
    (by positivity) hT hbudget htokens
  exact ⟨f, hf, fun v => (hf.incidence v).trans hfinal⟩

end PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplatesM

#print axioms PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplatesM.guarded_template_family_scaled_m
