/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseSpec
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoCutHub
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-!
# Every bounded-degree `Y` has a good hub partition

`hasGoodPartition`: for every cyclically tripartite `Y` of maximum degree `≤ 17` with at least
one arc there is a vertex partition `p : V → ZMod 3 × Fin M` (`M = 307 + 290 s`,
`s = ⌊√(2|Y|)⌋ + 1`) such that

* parts are monochromatic (`p v = (c v, g v)`);
* no arc lies inside a part, and the quotient is simple (an arc of `Y` is determined by the
  ordered pair of parts of its endpoints);
* every part contains at most `s` vertices of the support, hence has arc load `≤ 17 s`;
* `|P|^2 ≤ A₀ |Y|` and `load_a^2 ≤ A₀ |Y|` with the absolute constant `A₀ = goodConst`.

Proof: greedy colouring of the support.  A vertex `x` avoids (1) the parts of vertices at
distance `≤ 2`, (2) the parts `g z` of every `z` adjacent to some `w` that shares a part with a
neighbour of `x`, (3) full parts.  These are at most `306 + 289 s + (s - 1) < M` values.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace Greedy

variable {V : Type} [DecidableEq V]

/-- Neighbours of `x` in `Y` (in either direction). -/
def nbr (Y : Finset (V × V)) (x : V) : Finset V :=
  (Y.filter (fun e => e.1 = x)).image Prod.snd ∪ (Y.filter (fun e => e.2 = x)).image Prod.fst

lemma mem_nbr {Y : Finset (V × V)} {x y : V} : y ∈ nbr Y x ↔ (x, y) ∈ Y ∨ (y, x) ∈ Y := by
  simp only [nbr, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨e, ⟨he, rfl⟩, rfl⟩ | ⟨e, ⟨he, rfl⟩, rfl⟩)
    · exact Or.inl he
    · exact Or.inr he
  · rintro (h | h)
    · exact Or.inl ⟨_, ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨_, ⟨h, rfl⟩, rfl⟩

lemma nbr_symm {Y : Finset (V × V)} {x y : V} : y ∈ nbr Y x → x ∈ nbr Y y := by
  rw [mem_nbr, mem_nbr]; tauto

lemma card_nbr_le {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) (x : V) :
    (nbr Y x).card ≤ 17 := by
  have h := hdeg x
  unfold deg inDeg outDeg at h
  unfold nbr
  have h1 := Finset.card_union_le ((Y.filter (fun e => e.1 = x)).image Prod.snd)
    ((Y.filter (fun e => e.2 = x)).image Prod.fst)
  have h2 := Finset.card_image_le (s := Y.filter (fun e => e.1 = x)) (f := Prod.snd)
  have h3 := Finset.card_image_le (s := Y.filter (fun e => e.2 = x)) (f := Prod.fst)
  omega

/-- Vertices at distance `≤ 2` from `x`. -/
def near (Y : Finset (V × V)) (x : V) : Finset V := nbr Y x ∪ (nbr Y x).biUnion (nbr Y)

lemma card_near_le {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17) (x : V) :
    (near Y x).card ≤ 306 := by
  unfold near
  have h1 := Finset.card_union_le (nbr Y x) ((nbr Y x).biUnion (nbr Y))
  have h2 : ((nbr Y x).biUnion (nbr Y)).card ≤ 17 * 17 := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ z ∈ nbr Y x, (nbr Y z).card ≤ ∑ _z ∈ nbr Y x, 17 :=
          Finset.sum_le_sum fun z _ => card_nbr_le hdeg z
      _ = (nbr Y x).card * 17 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 17 * 17 := Nat.mul_le_mul_right _ (card_nbr_le hdeg x)
  have h3 := card_nbr_le hdeg x
  omega

lemma near_symm {Y : Finset (V × V)} {x y : V} (h : y ∈ near Y x) : x ∈ near Y y := by
  unfold near at *
  rcases Finset.mem_union.1 h with h | h
  · exact Finset.mem_union_left _ (nbr_symm h)
  · obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.1 h
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, nbr_symm hyz, nbr_symm hz⟩)

lemma zmod3_ne_succ : ∀ a : ZMod 3, a ≠ a + 1 := by decide

/-- The greedy invariant on a set `T` of placed vertices. -/
def Inv (c : V → ZMod 3) (Y : Finset (V × V)) (s M : ℕ) (T : Finset V) (g : V → Fin M) : Prop :=
  (∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∈ near Y x → c x = c y → g x ≠ g y) ∧
  (∀ a : ZMod 3 × Fin M, (T.filter (fun v => (c v, g v) = a)).card ≤ s) ∧
  (∀ e ∈ Y, ∀ e' ∈ Y, e.1 ∈ T → e.2 ∈ T → e'.1 ∈ T → e'.2 ∈ T →
    (c e.1, g e.1) = (c e'.1, g e'.1) → (c e.2, g e.2) = (c e'.2, g e'.2) → e = e')

lemma greedy_step (c : V → ZMod 3) {Y : Finset (V × V)} (hY : IsCyc c Y)
    (hdeg : MaxDegLE Y 17) (s M : ℕ) (hM : 306 + 289 * s + s < M + 1)
    (T : Finset V) (x : V) (hx : x ∉ T) (hcard : (insert x T).card < s ^ 2)
    (g : V → Fin M) (hg : Inv c Y s M T g) :
    ∃ g' : V → Fin M, Inv c Y s M (insert x T) g' := by
  classical
  obtain ⟨hA, hB, hC⟩ := hg
  have hTs : T.card < s ^ 2 := lt_of_le_of_lt (Finset.card_le_card (Finset.subset_insert _ _)) hcard
  set p : V → ZMod 3 × Fin M := fun v => (c v, g v) with hp
  -- forbidden values
  set F1 : Finset (Fin M) := ((near Y x).filter (· ∈ T)).image g with hF1
  set F2 : Finset (Fin M) := (((nbr Y x).filter (· ∈ T)).biUnion (fun y =>
      (T.filter (fun w => p w = p y)).biUnion (fun w => (nbr Y w).filter (· ∈ T)))).image g
    with hF2
  set fib : Fin M → Finset V := fun j => T.filter (fun v => p v = (c x, j)) with hfib
  set F3 : Finset (Fin M) := Finset.univ.filter (fun j => s ≤ (fib j).card) with hF3
  have c1 : F1.card ≤ 306 :=
    Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (card_near_le hdeg x))
  have c2 : F2.card ≤ 17 * (s * 17) := by
    refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ y ∈ (nbr Y x).filter (· ∈ T), ((T.filter (fun w => p w = p y)).biUnion
          (fun w => (nbr Y w).filter (· ∈ T))).card
        ≤ ∑ _y ∈ (nbr Y x).filter (· ∈ T), s * 17 := by
          refine Finset.sum_le_sum fun y _ => Finset.card_biUnion_le.trans ?_
          calc ∑ w ∈ T.filter (fun w => p w = p y), ((nbr Y w).filter (· ∈ T)).card
              ≤ ∑ _w ∈ T.filter (fun w => p w = p y), 17 :=
                Finset.sum_le_sum fun w _ => (Finset.card_filter_le _ _).trans (card_nbr_le hdeg w)
            _ = (T.filter (fun w => p w = p y)).card * 17 := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ s * 17 := Nat.mul_le_mul_right _ (hB (p y))
      _ = ((nbr Y x).filter (· ∈ T)).card * (s * 17) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 17 * (s * 17) :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (card_nbr_le hdeg x))
  have c3 : F3.card * s ≤ T.card := by
    have hdisj : ∀ i ∈ F3, ∀ j ∈ F3, i ≠ j → Disjoint (fib i) (fib j) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro v hi hj
      simp only [hfib, Finset.mem_filter, hp, Prod.mk.injEq] at hi hj
      exact hij (hi.2.2.symm.trans hj.2.2)
    calc F3.card * s = ∑ _j ∈ F3, s := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j ∈ F3, (fib j).card := Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2
      _ = (F3.biUnion fib).card :=
          (Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)).symm
      _ ≤ T.card := Finset.card_le_card (Finset.biUnion_subset.2 fun j _ =>
          Finset.filter_subset _ _)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at hTs; simp at hTs
    · exact h
  have c3' : F3.card < s := by
    by_contra h
    push_neg at h
    have : s * s ≤ T.card := (Nat.mul_le_mul_right s h).trans c3
    rw [sq] at hTs; omega
  have hcardF : (F1 ∪ F2 ∪ F3).card < (Finset.univ : Finset (Fin M)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have u1 := Finset.card_union_le (F1 ∪ F2) F3
    have u2 := Finset.card_union_le F1 F2
    nlinarith
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardF
  simp only [Finset.mem_union, not_or] at hj
  obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
  -- the update
  refine ⟨Function.update g x j, ?_, ?_, ?_⟩
  · intro u hu v hv huv hnear hc
    have gT : ∀ w ∈ T, Function.update g x j w = g w := fun w hw =>
      Function.update_of_ne (by rintro rfl; exact hx hw) _ _
    rcases Finset.mem_insert.1 hu with hux | hu <;> rcases Finset.mem_insert.1 hv with hvx | hv
    · exact absurd (hux.trans hvx.symm) huv
    · rw [hux, Function.update_self, gT v hv]
      rw [hux] at hnear
      intro h; apply hj1; rw [h]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hnear, hv⟩)
    · rw [hvx, Function.update_self, gT u hu]
      rw [hvx] at hnear
      intro h; apply hj1; rw [← h]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨near_symm hnear, hu⟩)
    · rw [gT u hu, gT v hv]; exact hA u hu v hv huv hnear hc
  · intro a
    have gT : ∀ w ∈ T, Function.update g x j w = g w := fun w hw =>
      Function.update_of_ne (by rintro rfl; exact hx hw) _ _
    rw [Finset.filter_insert]
    have hfilt : T.filter (fun v => (c v, Function.update g x j v) = a) =
        T.filter (fun v => (c v, g v) = a) :=
      Finset.filter_congr fun v hv => by rw [gT v hv]
    split_ifs with ha
    · rw [hfilt]
      refine (Finset.card_insert_le _ _).trans ?_
      rw [Function.update_self] at ha
      have : (T.filter (fun v => (c v, g v) = a)).card < s := by
        rw [← ha]
        by_contra h; push_neg at h
        exact hj3 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      omega
    · rw [hfilt]; exact hB a
  · intro e he e' he' h1 h2 h1' h2' hp1 hp2
    have gT : ∀ w ∈ T, Function.update g x j w = g w := fun w hw =>
      Function.update_of_ne (by rintro rfl; exact hx hw) _ _
    have hne : ∀ f ∈ Y, f.1 ≠ f.2 := fun f hf => Hub.ne_of_cyc c (hY f hf)
    have hgx : Function.update g x j x = j := Function.update_self _ _ _
    -- F2 membership helper
    have hF2mem : ∀ y ∈ T, y ∈ nbr Y x → ∀ w ∈ T, p w = p y → ∀ z ∈ T, z ∈ nbr Y w → g z ∈ F2 :=
      fun y hy hyx w hw hwy z hz hzw => Finset.mem_image_of_mem _ (Finset.mem_biUnion.2
        ⟨y, Finset.mem_filter.2 ⟨hyx, hy⟩, Finset.mem_biUnion.2
          ⟨w, Finset.mem_filter.2 ⟨hw, hwy⟩, Finset.mem_filter.2 ⟨hzw, hz⟩⟩⟩)
    simp only [Prod.mk.injEq] at hp1 hp2
    by_cases hxe : x = e.1 ∨ x = e.2 <;> by_cases hxe' : x = e'.1 ∨ x = e'.2
    · -- `x` is an endpoint of both arcs
      rcases hxe with hx1 | hx2 <;> rcases hxe' with hx1' | hx2'
      · -- e = (x, y), e' = (x, y')
        have hy : e.2 ∈ T := (Finset.mem_insert.1 h2).resolve_left
          (fun h => hne e he (hx1.symm.trans h.symm))
        have hy' : e'.2 ∈ T := (Finset.mem_insert.1 h2').resolve_left
          (fun h => hne e' he' (hx1'.symm.trans h.symm))
        rw [gT _ hy, gT _ hy'] at hp2
        by_contra hee
        have hyy : e.2 ≠ e'.2 := fun h => hee (Prod.ext (hx1.symm.trans hx1') h)
        have hnear : e'.2 ∈ near Y e.2 := by
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, ?_, ?_⟩)
          · rw [mem_nbr, hx1]; exact Or.inr (by simpa using he)
          · rw [mem_nbr, hx1']; exact Or.inl (by simpa using he')
        exact hA _ hy _ hy' hyy hnear hp2.1 hp2.2
      · -- e = (x, y), e' = (y', x): colours clash
        exfalso
        refine zmod3_ne_succ (c e.1) ?_
        calc c e.1 = c x := by rw [hx1]
          _ = c e'.2 := by rw [hx2']
          _ = c e'.1 + 1 := hY e' he'
          _ = c e.1 + 1 := by rw [hp1.1]
      · exfalso
        refine zmod3_ne_succ (c e.2) ?_
        calc c e.2 = c e'.2 := hp2.1
          _ = c e'.1 + 1 := hY e' he'
          _ = c e.2 + 1 := by rw [← hx1', hx2]
      · -- e = (y, x), e' = (y', x)
        have hy : e.1 ∈ T := (Finset.mem_insert.1 h1).resolve_left
          (fun h => hne e he (h.trans hx2))
        have hy' : e'.1 ∈ T := (Finset.mem_insert.1 h1').resolve_left
          (fun h => hne e' he' (h.trans hx2'))
        rw [gT _ hy, gT _ hy'] at hp1
        by_contra hee
        have hyy : e.1 ≠ e'.1 := fun h => hee (Prod.ext h (hx2.symm.trans hx2'))
        have hnear : e'.1 ∈ near Y e.1 := by
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, ?_, ?_⟩)
          · rw [mem_nbr, hx2]; exact Or.inl (by simpa using he)
          · rw [mem_nbr, hx2']; exact Or.inr (by simpa using he')
        exact hA _ hy _ hy' hyy hnear hp1.1 hp1.2
    · -- `x` only in `e`
      exfalso
      push_neg at hxe'
      have hz : e'.1 ∈ T := (Finset.mem_insert.1 h1').resolve_left (fun h => hxe'.1 h.symm)
      have hw : e'.2 ∈ T := (Finset.mem_insert.1 h2').resolve_left (fun h => hxe'.2 h.symm)
      rw [gT _ hz] at hp1; rw [gT _ hw] at hp2
      rcases hxe with hx1 | hx2
      · have hy : e.2 ∈ T := (Finset.mem_insert.1 h2).resolve_left
          (fun h => hne e he (hx1.symm.trans h.symm))
        rw [gT _ hy] at hp2
        rw [← hx1, hgx] at hp1
        apply hj2; rw [hp1.2]
        refine hF2mem e.2 hy ?_ e'.2 hw ?_ e'.1 hz ?_
        · rw [mem_nbr, hx1]; exact Or.inl (by simpa using he)
        · simp only [hp, Prod.mk.injEq]; exact ⟨hp2.1.symm, hp2.2.symm⟩
        · rw [mem_nbr]; exact Or.inr (by simpa using he')
      · have hy : e.1 ∈ T := (Finset.mem_insert.1 h1).resolve_left
          (fun h => hne e he (h.trans hx2))
        rw [gT _ hy] at hp1
        rw [← hx2, hgx] at hp2
        apply hj2; rw [hp2.2]
        refine hF2mem e.1 hy ?_ e'.1 hz ?_ e'.2 hw ?_
        · rw [mem_nbr, hx2]; exact Or.inr (by simpa using he)
        · simp only [hp, Prod.mk.injEq]; exact ⟨hp1.1.symm, hp1.2.symm⟩
        · rw [mem_nbr]; exact Or.inl (by simpa using he')
    · -- `x` only in `e'`
      exfalso
      push_neg at hxe
      have hz : e.1 ∈ T := (Finset.mem_insert.1 h1).resolve_left (fun h => hxe.1 h.symm)
      have hw : e.2 ∈ T := (Finset.mem_insert.1 h2).resolve_left (fun h => hxe.2 h.symm)
      rw [gT _ hz] at hp1; rw [gT _ hw] at hp2
      rcases hxe' with hx1 | hx2
      · have hy : e'.2 ∈ T := (Finset.mem_insert.1 h2').resolve_left
          (fun h => hne e' he' (hx1.symm.trans h.symm))
        rw [gT _ hy] at hp2
        rw [← hx1, hgx] at hp1
        apply hj2; rw [← hp1.2]
        refine hF2mem e'.2 hy ?_ e.2 hw ?_ e.1 hz ?_
        · rw [mem_nbr, hx1]; exact Or.inl (by simpa using he')
        · simp only [hp, Prod.mk.injEq]; exact ⟨hp2.1, hp2.2⟩
        · rw [mem_nbr]; exact Or.inr (by simpa using he)
      · have hy : e'.1 ∈ T := (Finset.mem_insert.1 h1').resolve_left
          (fun h => hne e' he' (h.trans hx2))
        rw [gT _ hy] at hp1
        rw [← hx2, hgx] at hp2
        apply hj2; rw [← hp2.2]
        refine hF2mem e'.1 hy ?_ e.1 hz ?_ e.2 hw ?_
        · rw [mem_nbr, hx2]; exact Or.inr (by simpa using he')
        · simp only [hp, Prod.mk.injEq]; exact ⟨hp1.1, hp1.2⟩
        · rw [mem_nbr]; exact Or.inl (by simpa using he)
    · -- `x` in neither
      push_neg at hxe hxe'
      have a1 : e.1 ∈ T := (Finset.mem_insert.1 h1).resolve_left (fun h => hxe.1 h.symm)
      have a2 : e.2 ∈ T := (Finset.mem_insert.1 h2).resolve_left (fun h => hxe.2 h.symm)
      have a3 : e'.1 ∈ T := (Finset.mem_insert.1 h1').resolve_left (fun h => hxe'.1 h.symm)
      have a4 : e'.2 ∈ T := (Finset.mem_insert.1 h2').resolve_left (fun h => hxe'.2 h.symm)
      rw [gT _ a1, gT _ a3] at hp1; rw [gT _ a2, gT _ a4] at hp2
      exact hC e he e' he' a1 a2 a3 a4 (by rw [hp1.1, hp1.2]) (by rw [hp2.1, hp2.2])

lemma greedy (c : V → ZMod 3) {Y : Finset (V × V)} (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17)
    (s M : ℕ) (hM : 306 + 289 * s + s < M + 1) :
    ∀ T : Finset V, T.card < s ^ 2 → ∃ g : V → Fin M, Inv c Y s M T g := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro hs
    have hM0 : 0 < M := by omega
    exact ⟨fun _ => ⟨0, hM0⟩, by simp, by simp, by simp⟩
  | insert x T hx ih =>
    intro hcard
    have hT : T.card < s ^ 2 :=
      lt_of_le_of_lt (Finset.card_le_card (Finset.subset_insert _ _)) hcard
    obtain ⟨g, hg⟩ := ih hT
    exact greedy_step c hY hdeg s M hM T x hx hcard g hg

/-- The absolute constant of the good partition. -/
def goodConst : ℕ := 9 * 597 ^ 2 * 8

/-- **Every bounded-degree `Y` with an arc has a good hub partition.** -/
theorem hasGoodPartition [Fintype V] (c : V → ZMod 3) (Y : Finset (V × V)) (hY : IsCyc c Y)
    (hdeg : MaxDegLE Y 17) (hne : Y.Nonempty) : HasGoodPartition goodConst c Y := by
  classical
  set m := Y.card with hm
  have hm1 : 1 ≤ m := Finset.card_pos.2 hne
  set S : Finset V := Y.image Prod.fst ∪ Y.image Prod.snd with hS
  have hScard : S.card ≤ 2 * m := by
    rw [hS]
    have := Finset.card_union_le (Y.image Prod.fst) (Y.image Prod.snd)
    have h1 := Finset.card_image_le (s := Y) (f := Prod.fst)
    have h2 := Finset.card_image_le (s := Y) (f := Prod.snd)
    omega
  set s := Nat.sqrt (2 * m) + 1 with hsdef
  have hs2 : 2 * m < s ^ 2 := Nat.lt_succ_sqrt' (2 * m)
  have hsq1 : 1 ≤ Nat.sqrt (2 * m) := Nat.sqrt_pos.2 (by omega)
  have hssq : s ^ 2 ≤ 8 * m := by
    have h1 : s ≤ 2 * Nat.sqrt (2 * m) := by omega
    have h2 : Nat.sqrt (2 * m) ^ 2 ≤ 2 * m := Nat.sqrt_le' (2 * m)
    calc s ^ 2 ≤ (2 * Nat.sqrt (2 * m)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 * Nat.sqrt (2 * m) ^ 2 := by ring
      _ ≤ 4 * (2 * m) := Nat.mul_le_mul_left _ h2
      _ = 8 * m := by ring
  set M := 307 + 290 * s with hMdef
  obtain ⟨g, hA, hB, hC⟩ := greedy c hY hdeg s M (by omega) S (by omega)
  have hmemS1 : ∀ e ∈ Y, e.1 ∈ S := fun e he =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have hmemS2 : ∀ e ∈ Y, e.2 ∈ S := fun e he =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
  refine ⟨ZMod 3 × Fin M, inferInstance, inferInstance, fun v => (c v, g v), Prod.fst,
    fun e _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro e he h
    have := hY e he
    simp only [Prod.mk.injEq] at h
    rw [← h.1] at this
    exact zmod3_ne_succ _ this
  · intro e he e' he' h1 h2
    exact hC e he e' he' (hmemS1 e he) (hmemS2 e he) (hmemS1 e' he') (hmemS2 e' he') h1 h2
  · rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    have hs1 : 1 ≤ s := by omega
    have : 3 * M ≤ 3 * 597 * s := by omega
    calc (3 * M) ^ 2 ≤ (3 * 597 * s) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 9 * 597 ^ 2 * s ^ 2 := by ring
      _ ≤ 9 * 597 ^ 2 * (8 * m) := Nat.mul_le_mul_left _ hssq
      _ = goodConst * m := by unfold goodConst; ring
  · intro a
    have hsub : Y.filter (fun e => (c e.1, g e.1) = a ∨ (c e.2, g e.2) = a) ⊆
        (S.filter (fun v => (c v, g v) = a)).biUnion
          (fun v => Y.filter (fun e => e.2 = v) ∪ Y.filter (fun e => e.1 = v)) := by
      intro e he
      obtain ⟨he, h⟩ := Finset.mem_filter.1 he
      rcases h with h | h
      · exact Finset.mem_biUnion.2 ⟨e.1, Finset.mem_filter.2 ⟨hmemS1 e he, h⟩,
          Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, rfl⟩)⟩
      · exact Finset.mem_biUnion.2 ⟨e.2, Finset.mem_filter.2 ⟨hmemS2 e he, h⟩,
          Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, rfl⟩)⟩
    have hload : (Y.filter (fun e => (c e.1, g e.1) = a ∨ (c e.2, g e.2) = a)).card ≤ s * 17 := by
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ v ∈ S.filter (fun v => (c v, g v) = a),
            (Y.filter (fun e => e.2 = v) ∪ Y.filter (fun e => e.1 = v)).card
          ≤ ∑ _v ∈ S.filter (fun v => (c v, g v) = a), 17 := by
            refine Finset.sum_le_sum fun v _ => (Finset.card_union_le _ _).trans ?_
            have := hdeg v; unfold deg inDeg outDeg at this; exact this
        _ = (S.filter (fun v => (c v, g v) = a)).card * 17 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ s * 17 := Nat.mul_le_mul_right _ (hB a)
    calc (Y.filter (fun e => (c e.1, g e.1) = a ∨ (c e.2, g e.2) = a)).card ^ 2
        ≤ (s * 17) ^ 2 := Nat.pow_le_pow_left hload 2
      _ = 289 * s ^ 2 := by ring
      _ ≤ 289 * (8 * m) := Nat.mul_le_mul_left _ hssq
      _ ≤ goodConst * m := by unfold goodConst; nlinarith

end Greedy

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
