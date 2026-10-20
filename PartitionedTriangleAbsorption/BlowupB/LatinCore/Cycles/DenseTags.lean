/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseLevel1

@[expose] public section

/-!
# Bookkeeping for the dense reduction: tags, hub-level arcs, degrees
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace DenseRed

variable {V P U' : Type*} [DecidableEq V] [DecidableEq P] [DecidableEq U'] (p : V → P)

/-- Which private path a private vertex belongs to: `0 = π`, `1 = O`, `2 = I`. -/
def kpart (k : Fin 5) : Fin 3 := if k = 0 then 0 else if k.val ≤ 2 then 1 else 2

def vtag : TV V P U' → Option ((V × V) × Fin 3)
  | Sum.inr (Sum.inr (Sum.inl (e, k))) => some (e, kpart k)
  | _ => none

def tag (a : TV V P U' × TV V P U') : Option ((V × V) × Fin 3) := (vtag a.1).or (vtag a.2)

lemma tag_piA {e : V × V} {a : TV V P U' × TV V P U'} (ha : a ∈ piA e) : tag a = some (e, 0) := by
  simp only [piA, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> simp [tag, vtag, old, pv, kpart]

lemma tag_OA {e : V × V} {a : TV V P U' × TV V P U'} (ha : a ∈ OA p e) : tag a = some (e, 1) := by
  simp only [OA, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, kpart]

lemma tag_IA {e : V × V} {a : TV V P U' × TV V P U'} (ha : a ∈ IA p e) : tag a = some (e, 2) := by
  simp only [IA, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, kpart]

lemma tag_old (u v : V) : tag ((old u, old v) : TV V P U' × TV V P U') = none := by
  simp [tag, vtag, old]

lemma tag_arcE (x : (P ⊕ U') × (P ⊕ U')) : tag (arcE (V := V) x) = none := by
  rcases x with ⟨a | a, b | b⟩ <;> simp [tag, vtag, arcE_apply, ι, hub, ext]

lemma old_ne_arcE (u v : V) (x : (P ⊕ U') × (P ⊕ U')) :
    arcE x ≠ ((old u, old v) : TV V P U' × TV V P U') := by
  rcases x with ⟨a | a, b | b⟩ <;> simp [arcE_apply, ι, hub, ext, old]

lemma QA_eq_arcE (e : V × V) :
    QA (U' := U') p e = {arcE (liftArc P U' (p e.1, p e.2))} := rfl

lemma mem_Ccyc {e : V × V} {a : TV V P U' × TV V P U'} :
    a ∈ Ccyc p e ↔ a ∈ piA e ∨ a ∈ OA p e ∨ a ∈ QA p e ∨ a ∈ IA p e := by
  simp [Ccyc, or_assoc]

/-- An arc of a basal piece is either tagged by its arc, or is the hub arc `Q_e`. -/
lemma Ccyc_cases {e : V × V} {a : TV V P U' × TV V P U'} (ha : a ∈ Ccyc p e) :
    (∃ k, tag a = some (e, k)) ∨ a = (hub (p e.1), hub (p e.2)) := by
  rcases (mem_Ccyc p).1 ha with h | h | h | h
  · exact Or.inl ⟨0, tag_piA h⟩
  · exact Or.inl ⟨1, tag_OA p h⟩
  · simp only [QA, Finset.mem_singleton] at h; exact Or.inr h
  · exact Or.inl ⟨2, tag_IA p h⟩

lemma tag_hub (a b : P) : tag ((hub a, hub b) : TV V P U' × TV V P U') = none := by
  simp [tag, vtag, hub]

lemma Ccyc_disjoint {e f : V × V} (hef : e ≠ f)
    (hq : ¬ (p e.1 = p f.1 ∧ p e.2 = p f.2)) :
    Disjoint (Ccyc (U' := U') p e) (Ccyc p f) := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  rcases Ccyc_cases p h1 with ⟨k, t1⟩ | r1 <;> rcases Ccyc_cases p h2 with ⟨k', t2⟩ | r2
  · rw [t1] at t2; simp only [Option.some.injEq, Prod.mk.injEq] at t2; exact hef t2.1
  · rw [r2, tag_hub] at t1; simp at t1
  · rw [r1, tag_hub] at t2; simp at t2
  · rw [r1] at r2
    simp only [hub, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at r2
    exact hq r2

lemma old_not_mem_Ccyc (e : V × V) (u v : V) :
    ((old u, old v) : TV V P U' × TV V P U') ∉ Ccyc p e := by
  intro h
  rcases Ccyc_cases p h with ⟨k, t⟩ | r
  · rw [tag_old] at t; simp at t
  · simp [old, hub] at r

lemma arcE_not_mem_tagged {a : TV V P U' × TV V P U'} {e : V × V} {k : Fin 3}
    (ht : tag a = some (e, k)) (x : (P ⊕ U') × (P ⊕ U')) : arcE x ≠ a := by
  rintro rfl; rw [tag_arcE] at ht; simp at ht

/-! ### Degrees -/

lemma deg_map_arcE (E : Finset ((P ⊕ U') × (P ⊕ U'))) (x : P ⊕ U') :
    deg (E.map (arcE (V := V))) (ι x) = deg E x := by
  unfold deg inDeg outDeg
  rw [Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
  congr 2
  · ext y; simp [arcE_apply, ι_injective.eq_iff]
  · ext y; simp [arcE_apply, ι_injective.eq_iff]

lemma deg_map_arcE_of_not_range (E : Finset ((P ⊕ U') × (P ⊕ U'))) (w : TV V P U')
    (hw : ∀ x, ι x ≠ w) : deg (E.map (arcE (V := V))) w = 0 := by
  unfold deg inDeg outDeg
  rw [Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
  have h1 : E.filter ((fun e => e.2 = w) ∘ arcE (V := V)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro y _ h; exact hw _ h
  have h2 : E.filter ((fun e => e.1 = w) ∘ arcE (V := V)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro y _ h; exact hw _ h
  rw [h1, h2]; rfl

lemma deg_Ccyc_eq {e : V × V} (hne : e.1 ≠ e.2) (hp : p e.1 ≠ p e.2) (w : TV V P U') :
    deg (Ccyc p e) w = if w ∈ Set.range (f9 p e) then 2 else 0 := by
  rw [Ccyc_eq, deg_cycF (f9_injective p hne hp)]

lemma mem_range_f9 {e : V × V} {w : TV V P U'} (h : w ∈ Set.range (f9 p e)) :
    w = old e.1 ∨ w = old e.2 ∨ w = hub (p e.1) ∨ w = hub (p e.2) ∨ ∃ k, w = pv e k := by
  obtain ⟨i, rfl⟩ := h
  fin_cases i <;> simp [f9]

end DenseRed

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
