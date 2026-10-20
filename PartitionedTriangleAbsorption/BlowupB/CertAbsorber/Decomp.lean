/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Gadget

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption

variable {W : Type*} [DecidableEq W] {t : ℕ}
variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable {c : SignedCert p F P}

namespace Matching

variable (M : Matching c)

/-- **Physical distinctness of all named edges** (including roots shared by occurrences and
repeated labels): different slots name different edges. -/
theorem ed_injective : Function.Injective M.ed := by
  have hne : ∀ s, s ≠ M.mu s := fun s h => M.ne s h.symm
  have hy : ∀ m m' : Fin 3, m + 1 = m' + 2 → m + 2 = m' + 1 → m = m' := by decide
  intro a b hab
  rcases a with ⟨s, x⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e <;>
    rcases b with ⟨s', x'⟩ | ⟨i', m'⟩ | ⟨s', κ'⟩ | e' <;>
    (try cases κ) <;> (try cases κ') <;> (try induction e using Sym2.ind) <;>
    (try induction e' using Sym2.ind) <;>
    simp [Matching.ed, Matching.hEdge, occV, hngV] at hab ⊢
  all_goals (try (simp_all; done))
  · rcases hab with h | ⟨⟨rfl, h1⟩, -, h2⟩
    · exact h
    · exact ⟨rfl, hy _ _ h1 h2⟩
  all_goals (obtain ⟨rfl, h⟩ := hab; first | exact hne _ h | exact M.ne _ h)

end Matching

lemma ms_rot {α : Type*} (a b c : α) : ({a, b, c} : Multiset α) = {b, c, a} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  ac_rfl

lemma ms_swap {α : Type*} (a b c : α) : ({a, b, c} : Multiset α) = {b, a, c} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  ac_rfl

lemma fin3_add_one_eq_add_two_iff (m : Fin 3) : m + 1 = m + 2 ↔ False := by revert m; decide

lemma U_eq_V_iff (s : Fin c.k × Fin 3) : c.U s = c.V s ↔ False :=
  iff_false_intro (c.U_ne_V s)

attribute [local simp] occV hngV fin3_add_one_eq_add_two_iff U_eq_V_iff

lemma side_typed (s : Fin c.k × Fin 3) :
    ({p (c.U s), p (c.V s), p (c.vtx s.1 s.2)} : Multiset (Fin t)) ∈ F := by
  have h := c.typed s.1
  rcases s with ⟨i, m⟩
  fin_cases m <;> simp only [SignedCert.U, SignedCert.V] at h ⊢
  · rw [ms_rot] at h; simpa using h
  · rw [ms_rot, ms_rot] at h; simpa using h
  · simpa using h
lemma mu_typed (M : Matching c) (s : Fin c.k × Fin 3) (hs : c.pos s.1 = false) :
    ({p (c.U s), p (c.V s), p (c.vtx (M.mu s).1 (M.mu s).2)} : Multiset (Fin t)) ∈ F := by
  have h := side_typed (M.mu s)
  have he := M.side_mu s hs
  simp only [SignedCert.side, Sym2.eq_iff] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [h1, h2] at h
  · rwa [h1, h2, ms_swap] at h
lemma typedTri_of {V : Type*} [DecidableEq V] (lab : V → Fin t) {a b d : V} (hab : a ≠ b)
    (had : a ≠ d) (hbd : b ≠ d) (hF : ({lab a, lab b, lab d} : Multiset (Fin t)) ∈ F) :
    IsTypedTri lab F {a, b, d} :=
  ⟨card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩, by rw [map_three _ hab had hbd]; exact hF⟩
/-- Every triangle used in either mode is an allowed triangle of `F` with three distinct
vertices. -/
theorem tri_typed (M : Matching c) (j : TriIx c.k) (hj : c.inMode0 j ∨ M.inModeP j) :
    IsTypedTri c.extLabel F (M.tri j) := by
  cases j <;> simp only [SignedCert.inMode0, Matching.inModeP, or_false, false_or] at hj <;>
    rw [Matching.tri] <;>
    refine typedTri_of (V := Ext W c.k) c.extLabel (by simp) (by simp)
      (by simp) ?_ <;>
    simp only [SignedCert.extLabel, occV, hngV]
  · rename_i i m
    rw [ms_rot]; exact side_typed (c := c) (i, m)
  · exact c.typed _
  all_goals first | exact side_typed _ | exact mu_typed M _ hj
/-- The edge set of each triangle is exactly the image of its three slots. -/
theorem tri_edges (M : Matching c) (j : TriIx c.k) : triEdges (M.tri j) = (M.sl j).image M.ed := by
  have h12 : ∀ m : Fin 3, m + 1 + 2 = m := by decide
  have h21 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  cases j <;>
    rw [Matching.tri, triEdges_three (by simp) (by simp)
      (by simp)] <;>
    simp only [Matching.sl, image_insert, image_singleton, Matching.ed, Matching.hEdge,
      SignedCert.U, SignedCert.V, SignedCert.side, h12, h21, Sym2.map_mk] <;>
    ext e <;> simp only [mem_insert, mem_singleton] <;>
    constructor <;> rintro (h | h | h) <;> subst h <;> simp [-occV, -hngV, Sym2.eq_swap]

@[simp] lemma fin3_a12 (m : Fin 3) : m + 1 + 2 = m := by revert m; decide
@[simp] lemma fin3_a21 (m : Fin 3) : m + 2 + 1 = m := by revert m; decide
@[simp] lemma fin3_x12 (m m' : Fin 3) : m + 1 = m' + 2 ↔ m = m' + 1 := by revert m m'; decide
@[simp] lemma fin3_x21 (m m' : Fin 3) : m + 2 = m' + 1 ↔ m' = m + 1 := by revert m m'; decide
@[simp] lemma fin3_s1 (m : Fin 3) : m + 1 = m ↔ False := by revert m; decide
@[simp] lemma fin3_s2 (m : Fin 3) : m + 2 = m ↔ False := by revert m; decide
@[simp] lemma fin3_s1' (m : Fin 3) : m = m + 1 ↔ False := by revert m; decide
@[simp] lemma fin3_s2' (m : Fin 3) : m = m + 2 ↔ False := by revert m; decide
@[simp] lemma fin3_s12 (m : Fin 3) : m + 1 = m + 2 ↔ False := by revert m; decide
@[simp] lemma fin3_s21 (m : Fin 3) : m + 2 = m + 1 ↔ False := by revert m; decide
@[simp] lemma vtx_inj_iff (i : Fin c.k) (a b : Fin 3) : c.vtx i a = c.vtx i b ↔ a = b :=
  (c.inj i).eq_iff
/-- Slot-disjointness of the triangles of the empty mode. -/
theorem sl_disjoint_mode0 (M : Matching c) (j j' : TriIx c.k) (hj : c.inMode0 j) (hj' : c.inMode0 j') (hne : j ≠ j') :
    Disjoint (M.sl j) (M.sl j') := by
  cases j <;> cases j' <;> simp only [SignedCert.inMode0] at hj hj' <;>
    simp [Matching.sl, disjoint_insert_right, SignedCert.U, SignedCert.V] at hne ⊢
  all_goals (try (repeat' constructor) <;> intros <;> subst_vars <;> simp_all)
  all_goals first
    | exact Ne.symm hne
    | exact ⟨Ne.symm hne, fun h => absurd h.symm hne⟩
/-- Slot-disjointness of the triangles of mode `P`. -/
theorem sl_disjoint_modeP (M : Matching c) (j j' : TriIx c.k) (hj : M.inModeP j) (hj' : M.inModeP j') (hne : j ≠ j') :
    Disjoint (M.sl j) (M.sl j') := by
  have hUV := c.U_ne_V
  rcases j with ⟨i, m⟩ | i | s | s | s | s | s | s | s <;>
  rcases j' with ⟨i', m'⟩ | i' | s' | s' | s' | s' | s' | s' | s' <;>
    simp only [Matching.inModeP, Matching.Unmatched] at hj hj' <;>
    (try have hps := M.pos_mu s hj) <;> (try have hps' := M.pos_mu s' hj') <;>
    (try have hinj := M.inj s s' hj hj') <;>
    (try have hu := hj'.2 s hj) <;> (try have hu' := hj.2 s' hj') <;>
    (try have hsi := fun h => M.unmatched_inj hj' hj h) <;>
    (try obtain ⟨hj, -⟩ := hj) <;> (try obtain ⟨hj', -⟩ := hj') <;>
    simp [Matching.sl, disjoint_insert_right] at hne ⊢
  all_goals (try (repeat' constructor) <;> intros <;> subst_vars <;> simp_all [SignedCert.U, SignedCert.V])
  all_goals (try exact Ne.symm hne)
  all_goals (try (rename_i h; rw [← h] at hps; simp_all))
  all_goals exact fun h => hne (hsi h).symm
lemma mem_aSlots_wv (s : Fin c.k × Fin 3) (x : W) :
    Slot.wv s x ∈ c.aSlots ↔ x = c.U s ∨ x = c.V s := by
  simp [SignedCert.aSlots, SignedCert.occSlots, SignedCert.hSlots]
  constructor
  · rintro ⟨i, m, h | h⟩ <;> obtain ⟨rfl, rfl⟩ := h <;> simp
  · rintro (h | h) <;> exact ⟨s.1, s.2, by simp [h]⟩
lemma mem_aSlots_y (i : Fin c.k) (m : Fin 3) : Slot.y i m ∈ c.aSlots := by
  simp [SignedCert.aSlots, SignedCert.occSlots]
lemma mem_aSlots_h (s : Fin c.k × Fin 3) (κ : HK) :
    Slot.h s κ ∈ c.aSlots ↔ c.pos s.1 = false := by
  cases κ <;> simp [SignedCert.aSlots, SignedCert.occSlots, SignedCert.hSlots, SignedCert.negS]
lemma not_mem_aSlots_pe (e : Sym2 W) : Slot.pe e ∉ c.aSlots := by
  simp [SignedCert.aSlots, SignedCert.occSlots, SignedCert.hSlots]

theorem biUnion_sl_mode0 (M : Matching c) : (univ.filter c.inMode0).biUnion M.sl = c.aSlots := by
  ext σ
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hσ⟩
    rcases j with ⟨i, m⟩ | i | s | s | s | s | s | s | s <;> simp only [SignedCert.inMode0] at hj <;>
      simp only [Matching.sl, mem_insert, mem_singleton] at hσ <;> rcases hσ with h | h | h <;>
      subst h <;>
      simp [mem_aSlots_wv, mem_aSlots_y, mem_aSlots_h, hj, SignedCert.U, SignedCert.V]
  · intro hσ
    rcases σ with ⟨s, x⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e
    · rw [mem_aSlots_wv] at hσ
      cases hp : c.pos s.1
      · rcases hσ with rfl | rfl
        · exact ⟨.hz0 s, hp, by simp [Matching.sl]⟩
        · exact ⟨.hz1 s, hp, by simp [Matching.sl]⟩
      · rcases hσ with rfl | rfl
        · exact ⟨.r s.1 (s.2 + 1), hp, by simp [Matching.sl, SignedCert.U, SignedCert.V]⟩
        · exact ⟨.r s.1 (s.2 + 2), hp, by simp [Matching.sl, SignedCert.U, SignedCert.V]⟩
    · cases hp : c.pos i
      · exact ⟨.yy i, hp, by fin_cases m <;> simp [Matching.sl]⟩
      · exact ⟨.r i m, hp, by simp [Matching.sl]⟩
    · rw [mem_aSlots_h] at hσ
      cases κ
      · exact ⟨.hz0 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz1 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz2 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz1 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz0 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz2 s, hσ, by simp [Matching.sl]⟩
      · exact ⟨.hz2 s, hσ, by simp [Matching.sl]⟩
    · exact absurd hσ (not_mem_aSlots_pe e)
lemma UV_mu (M : Matching c) {s : Fin c.k × Fin 3} (hs : c.pos s.1 = false) :
    (c.U s = c.U (M.mu s) ∨ c.U s = c.V (M.mu s)) ∧
      (c.V s = c.U (M.mu s) ∨ c.V s = c.V (M.mu s)) ∧
      (c.U (M.mu s) = c.U s ∨ c.U (M.mu s) = c.V s) ∧
      (c.V (M.mu s) = c.U s ∨ c.V (M.mu s) = c.V s) := by
  have h := M.side_mu s hs
  simp only [SignedCert.side, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem biUnion_sl_modeP (M : Matching c) :
    (univ.filter M.inModeP).biUnion M.sl = c.aSlots ∪ P.image Slot.pe := by
  ext σ
  simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_union, mem_image]
  constructor
  · rintro ⟨j, hj, hσ⟩
    rcases j with ⟨i, m⟩ | i | s | s | s | s | s | s | s <;> simp only [Matching.inModeP] at hj <;>
      simp only [Matching.sl, mem_insert, mem_singleton] at hσ <;> rcases hσ with h | h | h <;>
      subst h
    all_goals first
      | exact Or.inr ⟨_, M.unmatched_side_mem hj, rfl⟩
      | (left; simp [mem_aSlots_wv, mem_aSlots_y, mem_aSlots_h, hj, SignedCert.U, SignedCert.V]; done)
      | (left; rw [mem_aSlots_wv]; have := UV_mu M hj; tauto)
  · rintro (hσ | ⟨e, he, rfl⟩)
    · rcases σ with ⟨s, x⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e
      · rw [mem_aSlots_wv] at hσ
        cases hp : c.pos s.1
        · rcases hσ with rfl | rfl
          · exact ⟨.r s.1 (s.2 + 1), hp, by simp [Matching.sl, SignedCert.U, SignedCert.V]⟩
          · exact ⟨.r s.1 (s.2 + 2), hp, by simp [Matching.sl, SignedCert.U, SignedCert.V]⟩
        · by_cases hu : M.Unmatched s
          · refine ⟨.cl s, hu, ?_⟩
            rcases hσ with rfl | rfl <;> simp [Matching.sl]
          · simp only [Matching.Unmatched, hp, true_and, not_forall, not_not] at hu
            obtain ⟨s', hs', rfl⟩ := hu
            have h4 := UV_mu M hs'
            rcases hσ with rfl | rfl
            · rcases h4.2.2.1 with h | h
              · exact ⟨.hp0 s', hs', by simp [Matching.sl, h]⟩
              · exact ⟨.hp1 s', hs', by simp [Matching.sl, h]⟩
            · rcases h4.2.2.2 with h | h
              · exact ⟨.hp0 s', hs', by simp [Matching.sl, h]⟩
              · exact ⟨.hp1 s', hs', by simp [Matching.sl, h]⟩
      · cases hp : c.pos i
        · exact ⟨.r i m, hp, by simp [Matching.sl]⟩
        · exact ⟨.yy i, hp, by fin_cases m <;> simp [Matching.sl]⟩
      · rw [mem_aSlots_h] at hσ
        cases κ
        · exact ⟨.hp0 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp1 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp2 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp2 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp2 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp1 s, hσ, by simp [Matching.sl]⟩
        · exact ⟨.hp0 s, hσ, by simp [Matching.sl]⟩
      · exact absurd hσ (not_mem_aSlots_pe e)
    · obtain ⟨s, hs, rfl⟩ := M.unmatched_surj he
      exact ⟨.cl s, hs, by simp [Matching.sl]⟩

/-- **The absorber `A` is `F`-decomposable** (empty mode). -/
theorem hasDecomp_absorber (M : Matching c) : HasDecomp c.extLabel F M.absorber := by
  have h := isDecomp_of_slots c.extLabel F (univ.filter c.inMode0) M.tri M.sl M.ed
    M.ed_injective (fun j hj => tri_typed M j (Or.inl (mem_filter.mp hj).2))
    (fun j _ => tri_edges M j)
    (fun j hj j' hj' hne => sl_disjoint_mode0 M j j' (mem_filter.mp hj).2 (mem_filter.mp hj').2 hne)
  rw [biUnion_sl_mode0] at h
  exact ⟨_, h⟩

/-- **`A ∪ P` is `F`-decomposable** (mode `P`). -/
theorem hasDecomp_absorber_union (M : Matching c) :
    HasDecomp c.extLabel F (M.absorber ∪ P.image (Sym2.map Sum.inl)) := by
  have h := isDecomp_of_slots c.extLabel F (univ.filter M.inModeP) M.tri M.sl M.ed
    M.ed_injective (fun j hj => tri_typed M j (Or.inr (mem_filter.mp hj).2))
    (fun j _ => tri_edges M j)
    (fun j hj j' hj' hne => sl_disjoint_modeP M j j' (mem_filter.mp hj).2 (mem_filter.mp hj').2 hne)
  rw [biUnion_sl_modeP, image_union, image_image] at h
  exact ⟨_, h⟩

end PaperII.CertAbsorber
