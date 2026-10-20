/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.CycleFun
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The one-hub cycle shortener

A positive control for the reduced target `CycleShortener`: **every** requirement of target A
holds, for every finite cyclically tripartite `Y` (of any maximum degree), *except* the degree
bound at a single new vertex, the hub, whose degree is `2 |Y|`.

Construction. For every arc `e = u → v` of `Y` the reserve contains three private directed paths

* `π_e : v → h_e → u` (length two),
* `O_e : u ⇝ hub` (length `3, 2, 4` for `c u = 0, 1, 2`),
* `I_e : hub ⇝ v` (length `4, 2, 3` for `c v = 1, 2, 0`),

with fresh private internal vertices. For a balanced `L ⊆ Y` choose, at every vertex `v`, a
bijection `β` from the `L`-arcs entering `v` to the `L`-arcs leaving `v`. The partition is

* `e + π_e` (a triangle) for `e ∈ L`,
* `π_e + O_e + I_e` (a cycle of length `≤ 9`) for `e ∈ Y \ L`,
* `I_e + O_{β e}` (a cycle of length `6` through the hub) for `e ∈ L`.

All other vertices have bounded degree: an old vertex `v` gets reserve degree `2 deg_Y v`, and a
private vertex has degree two. Hence the whole difficulty of target A is to replace the single
unbounded hub by bounded-degree structure (see `docs/LATIN_CORE_CYCLE_SHORTENER_20261015.md`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace Hub

variable {V : Type*} [DecidableEq V]

/-- Vertices: old vertices, the hub `inr none`, and seven private vertices per arc. -/
abbrev HV (V : Type*) := V ⊕ Option ((V × V) × Fin 7)

/-- The hub. -/
def hub : HV V := Sum.inr none

/-- The private vertex number `k` of the arc `e`. -/
def pv (e : V × V) (k : Fin 7) : HV V := Sum.inr (some (e, k))

/-- An old vertex. -/
def old (v : V) : HV V := Sum.inl v

/-- Colours of the new vertices. The hub has colour `0`. -/
def hcol (c : V → ZMod 3) : Option ((V × V) × Fin 7) → ZMod 3
  | none => 0
  | some (e, k) => (if k.val ≤ 3 then c e.1 else 0) + ![2, 1, 2, 0, 1, 2, 0] k

variable (c : V → ZMod 3)

/-- `π_e = v → h_e → u`. -/
def piA (e : V × V) : Finset (HV V × HV V) := {(old e.2, pv e 0), (pv e 0, old e.1)}

/-- `O_e : u ⇝ hub`. -/
def OA (e : V × V) : Finset (HV V × HV V) :=
  if c e.1 = 0 then {(old e.1, pv e 1), (pv e 1, pv e 2), (pv e 2, hub)}
  else if c e.1 = 1 then {(old e.1, pv e 1), (pv e 1, hub)}
  else {(old e.1, pv e 1), (pv e 1, pv e 2), (pv e 2, pv e 3), (pv e 3, hub)}

/-- `I_e : hub ⇝ v`. -/
def IA (e : V × V) : Finset (HV V × HV V) :=
  if c e.2 = 1 then {(hub, pv e 4), (pv e 4, pv e 5), (pv e 5, pv e 6), (pv e 6, old e.2)}
  else if c e.2 = 2 then {(hub, pv e 4), (pv e 4, old e.2)}
  else {(hub, pv e 4), (pv e 4, pv e 5), (pv e 5, old e.2)}

/-- The basal cycle of an arc: `π_e + O_e + I_e`. -/
def Ccyc (e : V × V) : Finset (HV V × HV V) := piA e ∪ OA c e ∪ IA c e

/-- The triangle `e + π_e`. -/
def Tcyc (e : V × V) : Finset (HV V × HV V) := insert (old e.1, old e.2) (piA e)

/-- The hub cycle `I_e + O_f`. -/
def Dcyc (e f : V × V) : Finset (HV V × HV V) := IA c e ∪ OA c f

/-- The reserve. -/
def reserve (Y : Finset (V × V)) : Finset (HV V × HV V) := Y.biUnion (Ccyc c)

lemma zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma zmod3_ne : (0 : ZMod 3) ≠ 1 ∧ (0 : ZMod 3) ≠ 2 ∧ (1 : ZMod 3) ≠ 2 ∧
    (1 : ZMod 3) ≠ 0 ∧ (2 : ZMod 3) ≠ 0 ∧ (2 : ZMod 3) ≠ 1 := by decide

section Pieces

variable {e : V × V}

lemma isDirCycle_T (hne : e.1 ≠ e.2) : IsDirCycle (Tcyc e) ∧ (Tcyc e).card ≤ 9 := by
  have h : Tcyc e = cycF ![old e.1, old e.2, pv e 0] := by
    ext a; simp [Tcyc, piA, mem_cycF, Fin.exists_fin_succ, eq_comm]
  have hinj : Function.Injective ![old e.1, old e.2, pv e 0] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [old, pv, eq_comm]
  rw [h]
  exact ⟨isDirCycle_cycF hinj, by rw [card_cycF hinj]; norm_num⟩

omit [DecidableEq V] in
lemma ne_of_cyc (he : c e.2 = c e.1 + 1) : e.1 ≠ e.2 := by
  intro h; rw [h] at he
  have : (1 : ZMod 3) = 0 := by
    have := congrArg (fun x => x - c e.2) he; simpa using this.symm
  exact absurd this (by decide)

/-- The basal cycle in vertex form, according to the colour of the tail. -/
lemma Ccyc_eq (he : c e.2 = c e.1 + 1) :
    ∃ (k : ℕ) (f : Fin (k + 1) → HV V), k + 1 ≤ 9 ∧ Function.Injective f ∧
      Ccyc c e = cycF f ∧ old e.1 ∈ Set.range f ∧ old e.2 ∈ Set.range f ∧
      hub ∈ Set.range f ∧ ∀ x ∈ Set.range f, x = old e.1 ∨ x = old e.2 ∨ x = hub ∨
        ∃ k, x = pv e k := by
  have hne : e.1 ≠ e.2 := ne_of_cyc c he
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  rcases zmod3_cases (c e.1) with h0 | h0 | h0
  · have hv : c e.2 = 1 := by rw [he, h0]; ring
    refine ⟨8, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, hub, pv e 4, pv e 5, pv e 6],
      by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨5, rfl⟩, ?_⟩
    · rw [← List.nodup_ofFn]
      simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
    · ext a
      simp only [Ccyc, piA, OA, IA, h0, hv, if_true, mem_cycF, Fin.exists_fin_succ,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      simp [eq_comm]
      tauto
    · rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
  · have hv : c e.2 = 2 := by rw [he, h0]; ring
    refine ⟨5, ![old e.2, pv e 0, old e.1, pv e 1, hub, pv e 4],
      by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨4, rfl⟩, ?_⟩
    · rw [← List.nodup_ofFn]
      simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
    · ext a
      simp only [Ccyc, piA, OA, IA, h0, hv, if_true, z10, z21, if_false, mem_cycF,
        Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      simp [eq_comm]
      tauto
    · rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
  · have hv : c e.2 = 0 := by rw [he, h0]; decide
    refine ⟨8, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, pv e 3, hub, pv e 4, pv e 5],
      by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨6, rfl⟩, ?_⟩
    · rw [← List.nodup_ofFn]
      simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
    · ext a
      simp only [Ccyc, piA, OA, IA, h0, hv, z20, z21, z01, z02, if_false, mem_cycF,
        Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      simp [eq_comm]
      tauto
    · rintro x ⟨i, rfl⟩
      fin_cases i <;> simp

lemma isDirCycle_D {e f : V × V} (hef : e.2 = f.1) :
    IsDirCycle (Dcyc c e f) ∧ (Dcyc c e f).card ≤ 9 := by
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  have key : ∃ (k : ℕ) (g : Fin (k + 1) → HV V), k + 1 ≤ 9 ∧ Function.Injective g ∧
      Dcyc c e f = cycF g := by
    rcases zmod3_cases (c e.2) with h0 | h0 | h0
    · have h0' : c f.1 = 0 := hef ▸ h0
      refine ⟨5, ![hub, pv e 4, pv e 5, old e.2, pv f 1, pv f 2], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z01, z02, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef]
        tauto
    · have h0' : c f.1 = 1 := hef ▸ h0
      refine ⟨5, ![hub, pv e 4, pv e 5, pv e 6, old e.2, pv f 1], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z10, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef]
        tauto
    · have h0' : c f.1 = 2 := hef ▸ h0
      refine ⟨5, ![hub, pv e 4, old e.2, pv f 1, pv f 2, pv f 3], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z20, z21, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef]
        tauto
  obtain ⟨k, g, hk, hg, hD⟩ := key
  rw [hD]
  exact ⟨isDirCycle_cycF hg, by rw [card_cycF hg]; exact hk⟩

lemma isCyc_Ccyc {e : V × V} (he : c e.2 = c e.1 + 1) :
    IsCyc (Sum.elim c (hcol c)) (Ccyc c e) := by
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  intro a ha
  rcases zmod3_cases (c e.1) with h0 | h0 | h0
  · have hv : c e.2 = 1 := by rw [he, h0]; ring
    simp only [Ccyc, piA, OA, IA, h0, hv, if_true, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with ((rfl | rfl) | rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;>
      simp [old, pv, hub, hcol, h0, hv] <;> decide
  · have hv : c e.2 = 2 := by rw [he, h0]; ring
    simp only [Ccyc, piA, OA, IA, h0, hv, if_true, z10, z21, if_false, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ((rfl | rfl) | rfl | rfl) | rfl | rfl <;>
      simp [old, pv, hub, hcol, h0, hv] <;> decide
  · have hv : c e.2 = 0 := by rw [he, h0]; decide
    simp only [Ccyc, piA, OA, IA, h0, hv, z20, z21, z01, z02, if_false,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ((rfl | rfl) | rfl | rfl | rfl | rfl) | rfl | rfl | rfl <;>
      simp [old, pv, hub, hcol, h0, hv] <;> decide

/-- Which of the three private paths of an arc a private index belongs to. -/
def part (k : Fin 7) : Fin 3 := if k = 0 then 0 else if k.val ≤ 3 then 1 else 2

/-- Tag of a vertex: the owning arc and path, for private vertices. -/
def vtag : HV V → Option ((V × V) × Fin 3) :=
  Sum.elim (fun _ => none) (Option.map (fun t => (t.1, part t.2)))

/-- Tag of an arc: the tag of its tail if private, otherwise that of its head. -/
def tag (a : HV V × HV V) : Option ((V × V) × Fin 3) := (vtag a.1).or (vtag a.2)

lemma tag_piA {e : V × V} {a : HV V × HV V} (ha : a ∈ piA e) : tag a = some (e, 0) := by
  simp only [piA, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> simp [tag, vtag, old, pv, part]

lemma tag_OA {e : V × V} {a : HV V × HV V} (ha : a ∈ OA c e) : tag a = some (e, 1) := by
  unfold OA at ha
  split_ifs at ha <;> simp only [Finset.mem_insert, Finset.mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, part]

lemma tag_IA {e : V × V} {a : HV V × HV V} (ha : a ∈ IA c e) : tag a = some (e, 2) := by
  unfold IA at ha
  split_ifs at ha <;> simp only [Finset.mem_insert, Finset.mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, part]

omit [DecidableEq V] in
lemma tag_old (u v : V) : tag ((old u, old v) : HV V × HV V) = none := by
  simp [tag, vtag, old]

omit [DecidableEq V] in
lemma card_fiber {L : Finset (V × V)} [DecidableEq V] (k : V × V → V) (v : V) :
    Fintype.card {a : {e // e ∈ L} // k a.1 = v} = (L.filter (fun e => k e = v)).card := by
  rw [← Fintype.card_coe (L.filter (fun e => k e = v))]
  refine Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ L) (k · = v)).trans
    (Equiv.subtypeEquivRight ?_))
  intro x
  simp

/-- At every vertex, pair the entering `L`-arcs bijectively with the leaving ones. -/
lemma exists_pairing (L : Finset (V × V)) (hL : Balanced L) :
    ∃ β : V × V → V × V, (∀ e ∈ L, β e ∈ L ∧ (β e).1 = e.2) ∧
      (∀ e₁ ∈ L, ∀ e₂ ∈ L, β e₁ = β e₂ → e₁ = e₂) ∧ (∀ f ∈ L, ∃ e ∈ L, β e = f) := by
  classical
  have hfib : ∀ v, {a : {e // e ∈ L} // a.1.2 = v} ≃ {a : {e // e ∈ L} // a.1.1 = v} := by
    intro v
    refine Fintype.equivOfCardEq ?_
    rw [card_fiber (fun e => e.2) v, card_fiber (fun e => e.1) v]
    exact hL v
  set σ : {e // e ∈ L} ≃ {e // e ∈ L} := Equiv.ofFiberEquiv hfib with hσ
  have hσmap : ∀ x, (σ x).1.1 = x.1.2 := fun x => Equiv.ofFiberEquiv_map hfib x
  refine ⟨fun e => if h : e ∈ L then (σ ⟨e, h⟩).1 else e, ?_, ?_, ?_⟩
  · intro e he
    simp only [he, dif_pos]
    exact ⟨(σ ⟨e, he⟩).2, hσmap ⟨e, he⟩⟩
  · intro e₁ h₁ e₂ h₂ h
    simp only [h₁, h₂, dif_pos] at h
    have := σ.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro f hf
    obtain ⟨⟨e, he⟩, hx⟩ := σ.surjective ⟨f, hf⟩
    exact ⟨e, he, by simp [he, hx]⟩

lemma mem_Ccyc {e : V × V} {a : HV V × HV V} :
    a ∈ Ccyc c e ↔ a ∈ piA e ∨ a ∈ OA c e ∨ a ∈ IA c e := by
  simp [Ccyc]

lemma tag_Ccyc {e : V × V} {a : HV V × HV V} (ha : a ∈ Ccyc c e) :
    tag a = some (e, 0) ∨ tag a = some (e, 1) ∨ tag a = some (e, 2) := by
  rcases (mem_Ccyc c).1 ha with h | h | h
  · exact Or.inl (tag_piA h)
  · exact Or.inr (Or.inl (tag_OA c h))
  · exact Or.inr (Or.inr (tag_IA c h))

lemma Ccyc_disjoint {e f : V × V} (hef : e ≠ f) : Disjoint (Ccyc c e) (Ccyc c f) := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  rcases tag_Ccyc c h1 with t1 | t1 | t1 <;> rcases tag_Ccyc c h2 with t2 | t2 | t2 <;>
    rw [t1] at t2 <;> simp at t2 <;> exact hef t2

lemma old_not_mem_Ccyc (u v : V) (e : V × V) : ((old u, old v) : HV V × HV V) ∉ Ccyc c e := by
  intro h
  rcases tag_Ccyc c h with t | t | t <;> rw [tag_old] at t <;> simp at t

omit [DecidableEq V] in
lemma deg_biUnion {ι W : Type*} [DecidableEq W] [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset (W × W)) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j)) (x : W) :
    deg (s.biUnion t) x = ∑ i ∈ s, deg (t i) x := by
  unfold deg inDeg outDeg
  rw [Finset.filter_biUnion, Finset.filter_biUnion, Finset.card_biUnion, Finset.card_biUnion,
    ← Finset.sum_add_distrib]
  · intro i hi j hj hij
    exact Disjoint.mono (filter_subset _ _) (filter_subset _ _) (h i hi j hj hij)
  · intro i hi j hj hij
    exact Disjoint.mono (filter_subset _ _) (filter_subset _ _) (h i hi j hj hij)

lemma deg_Ccyc_old {e : V × V} (he : c e.2 = c e.1 + 1) (v : V) :
    deg (Ccyc c e) (old v) = if e.2 = v then 2 else if e.1 = v then 2 else 0 := by
  obtain ⟨k, f, -, hf, hC, h1, h2, -, hr⟩ := Ccyc_eq c he
  rw [hC, deg_cycF hf]
  by_cases hv2 : e.2 = v
  · subst hv2; simp [h2]
  · by_cases hv1 : e.1 = v
    · subst hv1; simp [h1, hv2]
    · rw [if_neg, if_neg hv2, if_neg hv1]
      intro hm
      rcases hr _ hm with h | h | h | ⟨k, h⟩ <;> simp [old, hub, pv] at h
      · exact hv1 h.symm
      · exact hv2 h.symm

lemma deg_Ccyc_hub {e : V × V} (he : c e.2 = c e.1 + 1) :
    deg (Ccyc c e) (Sum.inr none) = 2 := by
  obtain ⟨k, f, -, hf, hC, -, -, h3, -⟩ := Ccyc_eq c he
  rw [hC, deg_cycF hf, if_pos (show Sum.inr none ∈ Set.range f from h3)]

lemma deg_Ccyc_pv {e : V × V} (he : c e.2 = c e.1 + 1) (x : (V × V) × Fin 7) :
    deg (Ccyc c e) (Sum.inr (some x)) ≤ if x.1 = e then 2 else 0 := by
  obtain ⟨k, f, -, hf, hC, -, -, -, hr⟩ := Ccyc_eq c he
  rw [hC, deg_cycF hf]
  split_ifs with h1 h2 <;> try omega
  rcases hr _ h1 with h | h | h | ⟨k, h⟩ <;> simp [old, hub, pv] at h
  exact absurd (by rw [h]) h2

end Pieces

/-- Where an arc `a` of a piece `q` can come from, recorded through its tag. -/
def PieceClass (Y L : Finset (V × V)) (β : V × V → V × V) (q : Finset (HV V × HV V))
    (a : HV V × HV V) : Prop :=
  (∃ e ∈ L, q = Tcyc e ∧ ((tag a = none ∧ a = (old e.1, old e.2)) ∨ tag a = some (e, 0))) ∨
  (∃ f ∈ Y, f ∉ L ∧ q = Ccyc c f ∧
    (tag a = some (f, 0) ∨ tag a = some (f, 1) ∨ tag a = some (f, 2))) ∨
  (∃ e ∈ L, q = Dcyc c e (β e) ∧ (tag a = some (e, 2) ∨ tag a = some (β e, 1)))

lemma pieceClass_eq {Y L : Finset (V × V)} {β : V × V → V × V}
    (hβinj : ∀ e₁ ∈ L, ∀ e₂ ∈ L, β e₁ = β e₂ → e₁ = e₂) (hβL : ∀ e ∈ L, β e ∈ L)
    {q₁ q₂ : Finset (HV V × HV V)} {a : HV V × HV V}
    (h₁ : PieceClass c Y L β q₁ a) (h₂ : PieceClass c Y L β q₂ a) : q₁ = q₂ := by
  rcases h₁ with ⟨e₁, he₁, rfl, t₁⟩ | ⟨f₁, -, hf₁L, rfl, t₁⟩ | ⟨e₁, he₁, rfl, t₁⟩ <;>
    rcases h₂ with ⟨e₂, he₂, rfl, t₂⟩ | ⟨f₂, -, hf₂L, rfl, t₂⟩ | ⟨e₂, he₂, rfl, t₂⟩
  · rcases t₁ with ⟨t₁, rfl⟩ | t₁ <;> rcases t₂ with ⟨t₂, h₂'⟩ | t₂
    · simp only [old, Prod.mk.injEq, Sum.inl.injEq] at h₂'
      rw [Prod.ext h₂'.1 h₂'.2]
    · rw [t₁] at t₂; simp at t₂
    · rw [t₁] at t₂; simp at t₂
    · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂; rw [t₂.1]
  · rcases t₁ with ⟨t₁, -⟩ | t₁ <;> rcases t₂ with t₂ | t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at t₂ <;>
      obtain ⟨rfl, -⟩ := t₂ <;> exact absurd he₁ hf₂L
  · rcases t₁ with ⟨t₁, -⟩ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp at t₂
  · rcases t₂ with ⟨t₂, -⟩ | t₂ <;> rcases t₁ with t₁ | t₁ | t₁ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at t₂ <;>
      obtain ⟨rfl, -⟩ := t₂ <;> exact absurd he₂ hf₁L
  · rcases t₁ with t₁ | t₁ | t₁ <;> rcases t₂ with t₂ | t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;>
      rw [t₂.1]
  · rcases t₁ with t₁ | t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;>
      obtain ⟨rfl, -⟩ := t₂ <;>
      first | exact absurd he₂ hf₁L | exact absurd (hβL _ he₂) hf₁L
  · rcases t₂ with ⟨t₂, -⟩ | t₂ <;> rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;> simp at t₂
  · rcases t₂ with t₂ | t₂ | t₂ <;> rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;>
      obtain ⟨rfl, -⟩ := t₂ <;>
      first | exact absurd he₁ hf₂L | exact absurd (hβL _ he₁) hf₂L
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂
    · rw [t₂.1]
    · simp at t₂
    · simp at t₂
    · rw [hβinj e₁ he₁ e₂ he₂ t₂.1]

section Main

variable (V : Type*) [DecidableEq V]

/-- **The one-hub shortener.** For every finite cyclically tripartite `Y` there is a reserve `R`,
fixed before the demand, such that `R` is cyclically tripartite and arc-disjoint from `Y`,
`|R| ≤ 9 |Y|`, every old vertex has reserve degree `2 deg_Y`, every private vertex has degree at
most two, the hub has degree `2 |Y|`, and for every balanced `L ⊆ Y` the graph `R ∪ L` partitions
into directed simple cycles of length at most `9`.

So target A holds verbatim except for the degree bound at the single vertex `Sum.inr none`. -/
theorem hub_shortener (c : V → ZMod 3) (Y : Finset (V × V)) (hY : IsCyc c Y) :
    ∃ R : Finset (HV V × HV V),
      IsCyc (Sum.elim c (hcol c)) R ∧ Disjoint R (Y.map (liftArc V _)) ∧
      R.card ≤ 9 * Y.card ∧
      (∀ v, deg R (Sum.inl v) = 2 * deg Y v) ∧
      (∀ x, deg R (Sum.inr (some x)) ≤ 2) ∧
      deg R (Sum.inr none) = 2 * Y.card ∧
      ∀ L ⊆ Y, Balanced L →
        ∃ P : Finset (Finset (HV V × HV V)), IsCyclePartition 9 P (R ∪ L.map (liftArc V _)) := by
  classical
  have hdisjY : ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → Disjoint (Ccyc c i) (Ccyc c j) :=
    fun i _ j _ hij => Ccyc_disjoint c hij
  have hliftmem : ∀ {a : HV V × HV V} {L : Finset (V × V)},
      a ∈ L.map (liftArc V (Option ((V × V) × Fin 7))) ↔ ∃ e ∈ L, a = (old e.1, old e.2) := by
    intro a L
    simp only [Finset.mem_map, liftArc, Function.Embedding.coeFn_mk, old]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩
  refine ⟨reserve c Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    exact isCyc_Ccyc c (hY e he) a hae
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    obtain ⟨f, -, rfl⟩ := hliftmem.1 hb
    exact old_not_mem_Ccyc c _ _ e hae
  · unfold reserve
    rw [Finset.card_biUnion hdisjY, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨k, f, hk, hf, hC, -⟩ := Ccyc_eq c (hY e he)
    rw [hC, card_cycF hf]; exact hk
  · intro v
    have h := deg_biUnion Y (Ccyc c) hdisjY (old v)
    unfold reserve
    rw [show (Sum.inl v : HV V) = old v from rfl, h]
    rw [Finset.sum_congr rfl fun e he => deg_Ccyc_old c (hY e he) v]
    unfold deg inDeg outDeg
    rw [Finset.card_filter, Finset.card_filter, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hne := ne_of_cyc c (hY e he)
    by_cases h2 : e.2 = v
    · have h1 : e.1 ≠ v := fun h1 => hne (h1.trans h2.symm)
      simp [h1, h2]
    · simp [h2]
  · intro x
    unfold reserve
    rw [deg_biUnion Y (Ccyc c) hdisjY]
    calc ∑ e ∈ Y, deg (Ccyc c e) (Sum.inr (some x))
        ≤ ∑ e ∈ Y, (if x.1 = e then 2 else 0) :=
          Finset.sum_le_sum fun e he => deg_Ccyc_pv c (hY e he) x
      _ ≤ 2 := by
          rw [Finset.sum_ite_eq]
          split_ifs <;> omega
  · unfold reserve
    rw [deg_biUnion Y (Ccyc c) hdisjY]
    rw [Finset.sum_congr rfl fun e he => deg_Ccyc_hub c (hY e he)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro L hLY hLb
    obtain ⟨β, hβ, hβinj, hβsurj⟩ := exists_pairing L hLb
    refine ⟨L.image Tcyc ∪ (Y \ L).image (Ccyc c) ∪ L.image (fun e => Dcyc c e (β e)),
      ?_, ?_, ?_⟩
    · intro q hq
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
      rcases hq with (⟨e, he, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩) | ⟨e, he, rfl⟩
      · exact isDirCycle_T (ne_of_cyc c (hY e (hLY he)))
      · obtain ⟨k, f, hk, hf, hC, -⟩ := Ccyc_eq c (hY e he)
        rw [hC]; exact ⟨isDirCycle_cycF hf, by rw [card_cycF hf]; exact hk⟩
      · exact isDirCycle_D c (hβ e he).2.symm
    · have hclass : ∀ q ∈ L.image Tcyc ∪ (Y \ L).image (Ccyc c) ∪
          L.image (fun e => Dcyc c e (β e)), ∀ a ∈ q, PieceClass c Y L β q a := by
        intro q hq a ha
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
        rcases hq with (⟨e, he, rfl⟩ | ⟨f, ⟨hf, hfL⟩, rfl⟩) | ⟨e, he, rfl⟩
        · refine Or.inl ⟨e, he, rfl, ?_⟩
          simp only [Tcyc, Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · exact Or.inl ⟨tag_old _ _, rfl⟩
          · exact Or.inr (tag_piA ha)
        · exact Or.inr (Or.inl ⟨f, hf, hfL, rfl, tag_Ccyc c ha⟩)
        · refine Or.inr (Or.inr ⟨e, he, rfl, ?_⟩)
          simp only [Dcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (tag_IA c ha)
          · exact Or.inr (tag_OA c ha)
      intro q₁ hq₁ q₂ hq₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a h₁ h₂
      exact hne (pieceClass_eq c hβinj (fun e he => (hβ e he).1) (hclass q₁ hq₁ a h₁)
        (hclass q₂ hq₂ a h₂))
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
        id_eq]
      constructor
      · rintro ⟨q, (⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | ⟨e, he, rfl⟩, ha⟩
        · simp only [Tcyc, Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · exact Or.inr (hliftmem.2 ⟨e, he, rfl⟩)
          · exact Or.inl (Finset.mem_biUnion.2 ⟨e, hLY he, (mem_Ccyc c).2 (Or.inl ha)⟩)
        · exact Or.inl (Finset.mem_biUnion.2 ⟨f, hf, ha⟩)
        · simp only [Dcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (Finset.mem_biUnion.2 ⟨e, hLY he, (mem_Ccyc c).2 (Or.inr (Or.inr ha))⟩)
          · exact Or.inl (Finset.mem_biUnion.2
              ⟨β e, hLY (hβ e he).1, (mem_Ccyc c).2 (Or.inr (Or.inl ha))⟩)
      · rintro (ha | ha)
        · obtain ⟨f, hf, haf⟩ := Finset.mem_biUnion.1 ha
          by_cases hfL : f ∈ L
          · rcases (mem_Ccyc c).1 haf with h | h | h
            · exact ⟨Tcyc f, Or.inl (Or.inl ⟨f, hfL, rfl⟩), Finset.mem_insert_of_mem h⟩
            · obtain ⟨e, he, rfl⟩ := hβsurj f hfL
              exact ⟨Dcyc c e (β e), Or.inr ⟨e, he, rfl⟩,
                Finset.mem_union_right _ h⟩
            · exact ⟨Dcyc c f (β f), Or.inr ⟨f, hfL, rfl⟩, Finset.mem_union_left _ h⟩
          · exact ⟨Ccyc c f, Or.inl (Or.inr ⟨f, ⟨hf, hfL⟩, rfl⟩), haf⟩
        · obtain ⟨e, he, rfl⟩ := hliftmem.1 ha
          exact ⟨Tcyc e, Or.inl (Or.inl ⟨e, he, rfl⟩), Finset.mem_insert_self _ _⟩

end Main

end Hub

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
