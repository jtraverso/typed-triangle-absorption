/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.HubShortener

@[expose] public section

/-!
# Distributed hubs along cuts

A distributed version of the one-hub shortener (`HubShortener.lean`). The single hub is replaced
by one hub per part of a partition `p : V → P` of the old vertices. For an arc `e = u → v` of `Y`
the reserve contains the private paths

* `π_e : v → x → u`,
* `O_e : u ⇝ hub (p u)` and `I_e : hub (p v) ⇝ v` (as in the one-hub construction, but to the
  hub of the part of the endpoint),
* if `p u ≠ p v`, a private *connector* `Q_e : hub (p u) → y → z → hub (p v)`.

The basal piece of `e` is `π_e + O_e + Q_e + I_e`. For a balanced `L ⊆ Y` we use

* the triangle `e + π_e` for `e ∈ L`,
* the basal piece for `e ∈ Y \ L`,
* the cycle `I_e + O_{β e}` through `hub (p v)` for `e ∈ L` entering `v` (`β` pairs the `L`-arcs
  entering and leaving each vertex, so both paths use the same hub),
* the residual connectors `Q_e` of the crossing arcs of `L`. They form a balanced arc set on the
  hubs (the *residual circulation on the clones*). In general its cycles can be long.

**Cut hypothesis** (`CutPartition`). For every arc `e` of `Y` between two different parts there is
a vertex set `S` such that the arcs of `Y` leaving `S` are exactly those from part `p e.1` to part
`p e.2`, and the arcs entering `S` are exactly those from `p e.2` to `p e.1`. (This holds, for
example, when the quotient of `Y` by `p` is a forest: take for `S` one side of the quotient edge.)
Then a balanced `L` crosses every such cut equally often in both directions, so the residual
connectors pair up into antiparallel pairs `Q_e + Q_f`, which are directed `6`-cycles. The residual
circulation is then decomposed into short cycles.

`cutHub_shortener` proves that this gives a fixed reserve with `|R| ≤ 12 |Y|` and cycle pieces of
length `≤ 12` for every balanced `L`. Old vertices have reserve degree `2 deg_Y`, private
vertices degree `≤ 2`, and the hub of part `a` has degree exactly `2 #{e ∈ Y : p e.1 = a ∨ p e.2 = a}`.
So the reserve has bounded degree whenever the parts have bounded arc load.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace CutHub

variable {V P : Type*} [DecidableEq V] [DecidableEq P]

/-- Vertices: old vertices, one hub per part, and nine private vertices per arc. -/
abbrev CV (V P : Type*) := V ⊕ (P ⊕ ((V × V) × Fin 9))

instance instDecEqCV : DecidableEq (CV V P) :=
  inferInstanceAs (DecidableEq (V ⊕ (P ⊕ ((V × V) × Fin 9))))

/-- The hub of the part `a`. -/
def hub (a : P) : CV V P := Sum.inr (Sum.inl a)

/-- The private vertex number `k` of the arc `e`. -/
def pv (e : V × V) (k : Fin 9) : CV V P := Sum.inr (Sum.inr (e, k))

/-- An old vertex. -/
def old (v : V) : CV V P := Sum.inl v

/-- Colours of the new vertices. Hubs have colour `0`. -/
def hcol (c : V → ZMod 3) : P ⊕ ((V × V) × Fin 9) → ZMod 3
  | Sum.inl _ => 0
  | Sum.inr (e, k) => (if k.val ≤ 3 then c e.1 else 0) + ![2, 1, 2, 0, 1, 2, 0, 1, 2] k

variable (c : V → ZMod 3) (p : V → P)

/-- `π_e = v → x_e → u`. -/
def piA (e : V × V) : Finset (CV V P × CV V P) := {(old (P := P) e.2, pv (P := P) e 0), (pv (P := P) e 0, old (P := P) e.1)}

/-- `O_e : u ⇝ hub (p u)`. -/
def OA (e : V × V) : Finset (CV V P × CV V P) :=
  if c e.1 = 0 then {(old (P := P) e.1, pv (P := P) e 1), (pv (P := P) e 1, pv (P := P) e 2), (pv (P := P) e 2, hub (p e.1))}
  else if c e.1 = 1 then {(old (P := P) e.1, pv (P := P) e 1), (pv (P := P) e 1, hub (p e.1))}
  else {(old (P := P) e.1, pv (P := P) e 1), (pv (P := P) e 1, pv (P := P) e 2), (pv (P := P) e 2, pv (P := P) e 3), (pv (P := P) e 3, hub (p e.1))}

/-- `I_e : hub (p v) ⇝ v`. -/
def IA (e : V × V) : Finset (CV V P × CV V P) :=
  if c e.2 = 1 then
    {(hub (p e.2), pv (P := P) e 4), (pv (P := P) e 4, pv (P := P) e 5), (pv (P := P) e 5, pv (P := P) e 6), (pv (P := P) e 6, old (P := P) e.2)}
  else if c e.2 = 2 then {(hub (p e.2), pv (P := P) e 4), (pv (P := P) e 4, old (P := P) e.2)}
  else {(hub (p e.2), pv (P := P) e 4), (pv (P := P) e 4, pv (P := P) e 5), (pv (P := P) e 5, old (P := P) e.2)}

/-- The connector `Q_e : hub (p u) → y_e → z_e → hub (p v)` (empty inside a part). -/
def QA (e : V × V) : Finset (CV V P × CV V P) :=
  if p e.1 = p e.2 then ∅
  else {(hub (p e.1), pv (P := P) e 7), (pv (P := P) e 7, pv (P := P) e 8), (pv (P := P) e 8, hub (p e.2))}

/-- The basal piece `π_e + O_e + Q_e + I_e`. -/
def Ccyc (e : V × V) : Finset (CV V P × CV V P) := piA e ∪ OA c p e ∪ QA p e ∪ IA c p e

/-- The triangle `e + π_e`. -/
def Tcyc (e : V × V) : Finset (CV V P × CV V P) := insert (old e.1, old e.2) (piA e)

/-- The transition cycle `I_e + O_f` (through the hub of the common vertex). -/
def Dcyc (e f : V × V) : Finset (CV V P × CV V P) := IA c p e ∪ OA c p f

/-- The antiparallel connector pair `Q_e + Q_f`. -/
def Pcyc (e f : V × V) : Finset (CV V P × CV V P) := QA p e ∪ QA p f

/-- The reserve. -/
def reserve (Y : Finset (V × V)) : Finset (CV V P × CV V P) := Y.biUnion (Ccyc c p)

open Hub (zmod3_cases zmod3_ne ne_of_cyc deg_biUnion)

section Pieces

variable {e : V × V}

lemma isDirCycle_T (hne : e.1 ≠ e.2) : IsDirCycle (Tcyc (P := P) e) ∧ (Tcyc (P := P) e).card ≤ 12 := by
  have h : Tcyc (P := P) e = cycF ![old e.1, old e.2, pv e 0] := by
    ext a; simp [Tcyc, piA, mem_cycF, Fin.exists_fin_succ, eq_comm]
  have hinj : Function.Injective (![old e.1, old e.2, pv e 0] : Fin 3 → CV V P) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [old, pv, eq_comm]
  rw [h]
  exact ⟨isDirCycle_cycF hinj, by rw [card_cycF hinj]; norm_num⟩

set_option maxHeartbeats 1000000 in
/-- The basal piece in vertex form. -/
lemma Ccyc_eq (he : c e.2 = c e.1 + 1) :
    ∃ (k : ℕ) (f : Fin (k + 1) → CV V P), k + 1 ≤ 12 ∧ Function.Injective f ∧
      Ccyc c p e = cycF f ∧ old e.1 ∈ Set.range f ∧ old e.2 ∈ Set.range f ∧
      hub (p e.1) ∈ Set.range f ∧ hub (p e.2) ∈ Set.range f ∧
      ∀ x ∈ Set.range f, x = old e.1 ∨ x = old e.2 ∨ x = hub (p e.1) ∨ x = hub (p e.2) ∨
        ∃ k, x = pv e k := by
  have hne : e.1 ≠ e.2 := ne_of_cyc c he
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  by_cases hp : p e.1 = p e.2
  · have hQ : QA p e = (∅ : Finset (CV V P × CV V P)) := by simp [QA, hp]
    rcases zmod3_cases (c e.1) with h0 | h0 | h0
    · have hv : c e.2 = 1 := by rw [he, h0]; ring
      refine ⟨8, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, hub (p e.1), pv e 4, pv e 5,
        pv e 6], by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨5, rfl⟩, ⟨5, by simp [hp]⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, hp, if_true, mem_cycF, Fin.exists_fin_succ,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
    · have hv : c e.2 = 2 := by rw [he, h0]; ring
      refine ⟨5, ![old e.2, pv e 0, old e.1, pv e 1, hub (p e.1), pv e 4],
        by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨4, rfl⟩, ⟨4, by simp [hp]⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, hp, if_true, z10, z21, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
    · have hv : c e.2 = 0 := by rw [he, h0]; decide
      refine ⟨8, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, pv e 3, hub (p e.1), pv e 4,
        pv e 5], by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨6, rfl⟩, ⟨6, by simp [hp]⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, hp, z20, z21, z01, z02, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
  · have hQ : QA p e = ({(hub (p e.1), pv e 7), (pv e 7, pv e 8), (pv e 8, hub (p e.2))} :
        Finset (CV V P × CV V P)) := by simp [QA, hp]
    rcases zmod3_cases (c e.1) with h0 | h0 | h0
    · have hv : c e.2 = 1 := by rw [he, h0]; ring
      refine ⟨11, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, hub (p e.1), pv e 7, pv e 8,
        hub (p e.2), pv e 4, pv e 5, pv e 6], by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩,
        ⟨5, rfl⟩, ⟨8, rfl⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne, hp]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, if_true, mem_cycF, Fin.exists_fin_succ,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
    · have hv : c e.2 = 2 := by rw [he, h0]; ring
      refine ⟨8, ![old e.2, pv e 0, old e.1, pv e 1, hub (p e.1), pv e 7, pv e 8, hub (p e.2),
        pv e 4], by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨4, rfl⟩, ⟨7, rfl⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne, hp]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, if_true, z10, z21, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
    · have hv : c e.2 = 0 := by rw [he, h0]; decide
      refine ⟨11, ![old e.2, pv e 0, old e.1, pv e 1, pv e 2, pv e 3, hub (p e.1), pv e 7,
        pv e 8, hub (p e.2), pv e 4, pv e 5], by norm_num, ?_, ?_, ⟨2, rfl⟩, ⟨0, rfl⟩,
        ⟨6, rfl⟩, ⟨9, rfl⟩, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub, Ne.symm hne, hp]
      · ext a
        simp only [Ccyc, hQ, piA, OA, IA, h0, hv, z20, z21, z01, z02, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, or_assoc]
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp

lemma isDirCycle_D {e f : V × V} (hef : e.2 = f.1) :
    IsDirCycle (Dcyc c p e f) ∧ (Dcyc c p e f).card ≤ 12 := by
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  have key : ∃ (k : ℕ) (g : Fin (k + 1) → CV V P), k + 1 ≤ 12 ∧ Function.Injective g ∧
      Dcyc c p e f = cycF g := by
    rcases zmod3_cases (c e.2) with h0 | h0 | h0
    · have h0' : c f.1 = 0 := hef ▸ h0
      refine ⟨5, ![hub (p e.2), pv e 4, pv e 5, old e.2, pv f 1, pv f 2], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z01, z02, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef, or_assoc]
    · have h0' : c f.1 = 1 := hef ▸ h0
      refine ⟨5, ![hub (p e.2), pv e 4, pv e 5, pv e 6, old e.2, pv f 1], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z10, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef, or_assoc]
    · have h0' : c f.1 = 2 := hef ▸ h0
      refine ⟨5, ![hub (p e.2), pv e 4, old e.2, pv f 1, pv f 2, pv f 3], by norm_num, ?_, ?_⟩
      · rw [← List.nodup_ofFn]
        simp [List.ofFn_succ, old, pv, hub]
      · ext a
        simp only [Dcyc, OA, IA, h0, h0', if_true, z20, z21, if_false, mem_cycF,
          Fin.exists_fin_succ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp [eq_comm, hef, or_assoc]
  obtain ⟨k, g, hk, hg, hD⟩ := key
  rw [hD]
  exact ⟨isDirCycle_cycF hg, by rw [card_cycF hg]; exact hk⟩

/-- An antiparallel pair of connectors is a directed `6`-cycle. -/
lemma isDirCycle_P {e f : V × V} (hp : p e.1 ≠ p e.2) (h1 : p f.1 = p e.2)
    (h2 : p f.2 = p e.1) : IsDirCycle (Pcyc p e f) ∧ (Pcyc p e f).card ≤ 12 := by
  have hpf : p f.1 ≠ p f.2 := by rw [h1, h2]; exact Ne.symm hp
  have hef : e ≠ f := by rintro rfl; exact hp h2.symm
  have hD : Pcyc p e f = cycF ![hub (p e.1), pv e 7, pv e 8, hub (p e.2), pv f 7, pv f 8] := by
    ext a
    simp only [Pcyc, QA, hp, Ne.symm hp, if_false, h1, h2, mem_cycF, Fin.exists_fin_succ,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    simp [eq_comm, or_assoc]
  have hg : Function.Injective
      (![hub (p e.1), pv e 7, pv e 8, hub (p e.2), pv f 7, pv f 8] : Fin 6 → CV V P) := by
    rw [← List.nodup_ofFn]
    simp [List.ofFn_succ, pv, hub, hp, hef]
  rw [hD]
  exact ⟨isDirCycle_cycF hg, by rw [card_cycF hg]; norm_num⟩

lemma isCyc_Ccyc {e : V × V} (he : c e.2 = c e.1 + 1) :
    IsCyc (Sum.elim c (hcol c)) (Ccyc c p e) := by
  obtain ⟨z01, z02, z12, z10, z20, z21⟩ := zmod3_ne
  intro a ha
  have hQ : ∀ a ∈ QA p e, (Sum.elim c (hcol c)) a.2 = (Sum.elim c (hcol c)) a.1 + 1 := by
    intro a ha
    unfold QA at ha
    split_ifs at ha
    · simp at ha
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [pv, hub, hcol] <;> decide
  simp only [Ccyc, Finset.mem_union] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · simp only [piA, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp [old, pv, hcol, he]; ring
    · simp only [old, pv, hcol, Sum.elim_inl, Sum.elim_inr]
      simp only [Fin.isValue, Fin.val_zero, zero_le, if_true, Matrix.cons_val_zero]
      rw [add_assoc, show (2 : ZMod 3) + 1 = 0 from rfl, add_zero]
  · rcases zmod3_cases (c e.1) with h0 | h0 | h0
    · simp only [OA, h0, if_true, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide
    · simp only [OA, h0, z10, if_false, if_true, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide
    · simp only [OA, h0, z20, z21, if_false, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide
  · exact hQ a ha
  · rcases zmod3_cases (c e.2) with h0 | h0 | h0
    · simp only [IA, h0, z01, z02, if_false, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide
    · simp only [IA, h0, if_true, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide
    · simp only [IA, h0, z21, if_false, if_true, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [old, pv, hub, hcol, h0] <;> decide

/-- Which private path of an arc a private index belongs to. -/
def part (k : Fin 9) : Fin 4 :=
  if k = 0 then 0 else if k.val ≤ 3 then 1 else if k.val ≤ 6 then 2 else 3

/-- Tag of a vertex: the owning arc and path, for private vertices. -/
def vtag : CV V P → Option ((V × V) × Fin 4) :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (fun t => some (t.1, part t.2)))

/-- Tag of an arc: the tag of its tail if private, otherwise that of its head. -/
def tag (a : CV V P × CV V P) : Option ((V × V) × Fin 4) := (vtag a.1).or (vtag a.2)

lemma tag_piA {a : CV V P × CV V P} (ha : a ∈ piA e) : tag a = some (e, 0) := by
  simp only [piA, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> simp [tag, vtag, old, pv, part]

lemma tag_OA {a : CV V P × CV V P} (ha : a ∈ OA c p e) : tag a = some (e, 1) := by
  unfold OA at ha
  split_ifs at ha <;> simp only [Finset.mem_insert, Finset.mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, part]

lemma tag_IA {a : CV V P × CV V P} (ha : a ∈ IA c p e) : tag a = some (e, 2) := by
  unfold IA at ha
  split_ifs at ha <;> simp only [Finset.mem_insert, Finset.mem_singleton] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl <;> simp [tag, vtag, old, pv, hub, part]

lemma tag_QA {a : CV V P × CV V P} (ha : a ∈ QA p e) : tag a = some (e, 3) := by
  unfold QA at ha
  split_ifs at ha
  · simp at ha
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [tag, vtag, pv, hub, part]

omit [DecidableEq V] [DecidableEq P] in
lemma tag_old (u v : V) : tag ((old u, old v) : CV V P × CV V P) = none := by
  simp [tag, vtag, old]

lemma mem_Ccyc {a : CV V P × CV V P} :
    a ∈ Ccyc c p e ↔ a ∈ piA e ∨ a ∈ OA c p e ∨ a ∈ QA p e ∨ a ∈ IA c p e := by
  simp [Ccyc]

lemma tag_Ccyc {a : CV V P × CV V P} (ha : a ∈ Ccyc c p e) :
    tag a = some (e, 0) ∨ tag a = some (e, 1) ∨ tag a = some (e, 2) ∨ tag a = some (e, 3) := by
  rcases (mem_Ccyc c p).1 ha with h | h | h | h
  · exact Or.inl (tag_piA h)
  · exact Or.inr (Or.inl (tag_OA c p h))
  · exact Or.inr (Or.inr (Or.inr (tag_QA p h)))
  · exact Or.inr (Or.inr (Or.inl (tag_IA c p h)))

lemma Ccyc_disjoint {f : V × V} (hef : e ≠ f) : Disjoint (Ccyc c p e) (Ccyc c p f) := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  rcases tag_Ccyc c p h1 with t1 | t1 | t1 | t1 <;>
    rcases tag_Ccyc c p h2 with t2 | t2 | t2 | t2 <;>
    rw [t1] at t2 <;> simp at t2 <;> exact hef t2

lemma old_not_mem_Ccyc (u v : V) : ((old u, old v) : CV V P × CV V P) ∉ Ccyc c p e := by
  intro h
  rcases tag_Ccyc c p h with t | t | t | t <;> rw [tag_old] at t <;> simp at t

lemma deg_Ccyc_old (he : c e.2 = c e.1 + 1) (v : V) :
    deg (Ccyc c p e) (old v) = if e.2 = v then 2 else if e.1 = v then 2 else 0 := by
  obtain ⟨k, f, -, hf, hC, h1, h2, -, -, hr⟩ := Ccyc_eq c p he
  rw [hC, deg_cycF hf]
  by_cases hv2 : e.2 = v
  · subst hv2; simp [h2]
  · by_cases hv1 : e.1 = v
    · subst hv1; simp [h1, hv2]
    · rw [if_neg, if_neg hv2, if_neg hv1]
      intro hm
      rcases hr _ hm with h | h | h | h | ⟨k, h⟩ <;> simp [old, hub, pv] at h
      · exact hv1 h.symm
      · exact hv2 h.symm

lemma deg_Ccyc_hub (he : c e.2 = c e.1 + 1) (a : P) :
    deg (Ccyc c p e) (hub a) = if p e.1 = a ∨ p e.2 = a then 2 else 0 := by
  obtain ⟨k, f, -, hf, hC, -, -, h3, h4, hr⟩ := Ccyc_eq c p he
  rw [hC, deg_cycF hf]
  by_cases h : p e.1 = a ∨ p e.2 = a
  · rw [if_pos h, if_pos]
    rcases h with h | h
    · exact h ▸ h3
    · exact h ▸ h4
  · rw [if_neg h, if_neg]
    intro hm
    rcases hr _ hm with h' | h' | h' | h' | ⟨k, h'⟩ <;> simp [old, hub, pv] at h'
    · exact h (Or.inl h'.symm)
    · exact h (Or.inr h'.symm)

lemma deg_Ccyc_pv (he : c e.2 = c e.1 + 1) (x : (V × V) × Fin 9) :
    deg (Ccyc c p e) (Sum.inr (Sum.inr x)) ≤ if x.1 = e then 2 else 0 := by
  obtain ⟨k, f, -, hf, hC, -, -, -, -, hr⟩ := Ccyc_eq c p he
  rw [hC, deg_cycF hf]
  split_ifs with h1 h2 <;> try omega
  rcases hr _ h1 with h | h | h | h | ⟨k, h⟩ <;> simp [old, hub, pv] at h
  exact absurd (by rw [h]) h2

end Pieces

/-! ### Cuts and the pairing of residual connectors -/

/-- **Cut hypothesis.** For every arc `e` of `Y` between different parts there is a vertex set `S`
whose leaving arcs (in `Y`) are exactly the arcs from part `p e.1` to part `p e.2`, and whose
entering arcs are exactly the arcs from part `p e.2` to part `p e.1`. -/
def CutPartition (Y : Finset (V × V)) (p : V → P) : Prop :=
  ∀ e ∈ Y, p e.1 ≠ p e.2 → ∃ S : Finset V, ∀ f ∈ Y,
    ((f.1 ∈ S ∧ f.2 ∉ S) ↔ (p f.1 = p e.1 ∧ p f.2 = p e.2)) ∧
    ((f.1 ∉ S ∧ f.2 ∈ S) ↔ (p f.1 = p e.2 ∧ p f.2 = p e.1))

omit [DecidableEq P] in
/-- A balanced arc set leaves every vertex set as often as it enters it. -/
lemma card_leave_eq_card_enter {L : Finset (V × V)} (hL : Balanced L) (S : Finset V) :
    (L.filter (fun f => f.1 ∈ S ∧ f.2 ∉ S)).card =
      (L.filter (fun f => f.1 ∉ S ∧ f.2 ∈ S)).card := by
  have hout : (L.filter (fun f => f.1 ∈ S)).card = ∑ v ∈ S, outDeg L v := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := L.filter (fun f => f.1 ∈ S))
      (t := S) (fun x hx => (Finset.mem_filter.1 hx).2)]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold outDeg
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, h' ▸ hv⟩, h'⟩
  have hin : (L.filter (fun f => f.2 ∈ S)).card = ∑ v ∈ S, inDeg L v := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := L.filter (fun f => f.2 ∈ S))
      (t := S) (fun x hx => (Finset.mem_filter.1 hx).2)]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold inDeg
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, h' ▸ hv⟩, h'⟩
  have hsum : ∑ v ∈ S, inDeg L v = ∑ v ∈ S, outDeg L v := Finset.sum_congr rfl fun v _ => hL v
  have h1 := Finset.card_filter_add_card_filter_not (s := L.filter (fun f => f.1 ∈ S))
    (fun f => f.2 ∈ S)
  have h2 := Finset.card_filter_add_card_filter_not (s := L.filter (fun f => f.2 ∈ S))
    (fun f => f.1 ∈ S)
  simp only [Finset.filter_filter] at h1 h2
  have e1 : (L.filter (fun f => f.1 ∈ S ∧ f.2 ∈ S)) = L.filter (fun f => f.2 ∈ S ∧ f.1 ∈ S) := by
    ext x; simp [and_comm]
  have e2 : (L.filter (fun f => f.2 ∈ S ∧ f.1 ∉ S)) = L.filter (fun f => f.1 ∉ S ∧ f.2 ∈ S) := by
    ext x; simp [and_comm]
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- Between two parts, a balanced `L ⊆ Y` has as many arcs in each direction. -/
lemma card_dir_eq {Y L : Finset (V × V)} (hcut : CutPartition Y p) (hLY : L ⊆ Y)
    (hL : Balanced L) (a b : P) (hab : a ≠ b) :
    (L.filter (fun f => p f.1 = a ∧ p f.2 = b)).card =
      (L.filter (fun f => p f.1 = b ∧ p f.2 = a)).card := by
  by_cases h1 : ∃ e ∈ Y, p e.1 = a ∧ p e.2 = b
  · obtain ⟨e, he, rfl, rfl⟩ := h1
    obtain ⟨S, hS⟩ := hcut e he hab
    have := card_leave_eq_card_enter hL S
    rw [Finset.filter_congr (fun f hf => (hS f (hLY hf)).1),
      Finset.filter_congr (fun f hf => (hS f (hLY hf)).2)] at this
    exact this
  · by_cases h2 : ∃ e ∈ Y, p e.1 = b ∧ p e.2 = a
    · obtain ⟨e, he, rfl, rfl⟩ := h2
      obtain ⟨S, hS⟩ := hcut e he (Ne.symm hab)
      have := card_leave_eq_card_enter hL S
      rw [Finset.filter_congr (fun f hf => (hS f (hLY hf)).1),
        Finset.filter_congr (fun f hf => (hS f (hLY hf)).2)] at this
      exact this.symm
    · push_neg at h1 h2
      rw [Finset.filter_eq_empty_iff.2 (fun f hf h => h1 f (hLY hf) h.1 h.2),
        Finset.filter_eq_empty_iff.2 (fun f hf h => h2 f (hLY hf) h.1 h.2)]

omit [DecidableEq V] [DecidableEq P] in
lemma card_fiber' {α β : Type*} [DecidableEq β] (s : Finset α) (k : α → β) (b : β) :
    Fintype.card {a : {x // x ∈ s} // k a.1 = b} = (s.filter (fun x => k x = b)).card := by
  classical
  rw [← Fintype.card_coe (s.filter (fun x => k x = b))]
  refine Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (k · = b)).trans
    (Equiv.subtypeEquivRight ?_))
  intro x
  simp

/-- **Pairing of the residual connectors.** Every crossing arc of `L` going up in the rank order
is matched bijectively with a crossing arc of `L` going down between the same two parts. -/
lemma exists_cross_pairing {Y L : Finset (V × V)} (hcut : CutPartition Y p) (hLY : L ⊆ Y)
    (hL : Balanced L) (rk : P → ℕ) :
    ∃ τ : V × V → V × V,
      (∀ x ∈ L, rk (p x.1) < rk (p x.2) →
        τ x ∈ L ∧ p (τ x).1 = p x.2 ∧ p (τ x).2 = p x.1) ∧
      (∀ x₁ ∈ L, rk (p x₁.1) < rk (p x₁.2) → ∀ x₂ ∈ L, rk (p x₂.1) < rk (p x₂.2) →
        τ x₁ = τ x₂ → x₁ = x₂) ∧
      (∀ y ∈ L, rk (p y.2) < rk (p y.1) → ∃ x ∈ L, rk (p x.1) < rk (p x.2) ∧ τ x = y) := by
  classical
  set F := L.filter (fun x => rk (p x.1) < rk (p x.2)) with hF
  set B := L.filter (fun y => rk (p y.2) < rk (p y.1)) with hB
  have hfib : ∀ ab : P × P, {x : {x // x ∈ F} // (p x.1.1, p x.1.2) = ab} ≃
      {y : {y // y ∈ B} // (p y.1.2, p y.1.1) = ab} := by
    rintro ⟨a, b⟩
    refine Fintype.equivOfCardEq ?_
    rw [card_fiber' F (fun x => (p x.1, p x.2)) (a, b),
      card_fiber' B (fun y => (p y.2, p y.1)) (a, b)]
    by_cases hab : rk a < rk b
    · have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
      have e1 : F.filter (fun x => (p x.1, p x.2) = (a, b)) =
          L.filter (fun f => p f.1 = a ∧ p f.2 = b) := by
        ext x
        simp only [hF, Finset.mem_filter, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h1, h2⟩; exact ⟨⟨h, by rw [h1, h2]; exact hab⟩, h1, h2⟩
      have e2 : B.filter (fun y => (p y.2, p y.1) = (a, b)) =
          L.filter (fun f => p f.1 = b ∧ p f.2 = a) := by
        ext x
        simp only [hB, Finset.mem_filter, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨h, -⟩, h1, h2⟩; exact ⟨h, h2, h1⟩
        · rintro ⟨h, h1, h2⟩; exact ⟨⟨h, by rw [h1, h2]; exact hab⟩, h2, h1⟩
      rw [e1, e2]
      exact card_dir_eq p hcut hLY hL a b hne
    · have e1 : F.filter (fun x => (p x.1, p x.2) = (a, b)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx h
        simp only [Prod.mk.injEq] at h
        have := (Finset.mem_filter.1 hx).2
        rw [h.1, h.2] at this
        exact hab this
      have e2 : B.filter (fun y => (p y.2, p y.1) = (a, b)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx h
        simp only [Prod.mk.injEq] at h
        have := (Finset.mem_filter.1 hx).2
        rw [h.1, h.2] at this
        exact hab this
      rw [e1, e2]
  set σ : {x // x ∈ F} ≃ {y // y ∈ B} := Equiv.ofFiberEquiv hfib with hσ
  have hσmap : ∀ x, (p (σ x).1.2, p (σ x).1.1) = (p x.1.1, p x.1.2) :=
    fun x => Equiv.ofFiberEquiv_map hfib x
  refine ⟨fun e => if h : e ∈ F then (σ ⟨e, h⟩).1 else e, ?_, ?_, ?_⟩
  · intro x hx hlt
    have hxF : x ∈ F := Finset.mem_filter.2 ⟨hx, hlt⟩
    simp only [hxF, dif_pos]
    have hm := hσmap ⟨x, hxF⟩
    simp only [Prod.mk.injEq] at hm
    exact ⟨(Finset.mem_filter.1 (σ ⟨x, hxF⟩).2).1, hm.2, hm.1⟩
  · intro x₁ h₁ l₁ x₂ h₂ l₂ h
    have hx₁ : x₁ ∈ F := Finset.mem_filter.2 ⟨h₁, l₁⟩
    have hx₂ : x₂ ∈ F := Finset.mem_filter.2 ⟨h₂, l₂⟩
    simp only [hx₁, hx₂, dif_pos] at h
    have := σ.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro y hy hlt
    have hyB : y ∈ B := Finset.mem_filter.2 ⟨hy, hlt⟩
    obtain ⟨⟨x, hx⟩, hxy⟩ := σ.surjective ⟨y, hyB⟩
    refine ⟨x, (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2, ?_⟩
    simp [hx, hxy]

/-- Where an arc `a` of a piece `q` can come from, recorded through its tag. -/
def PieceClass (Y L : Finset (V × V)) (rk : P → ℕ) (β τ : V × V → V × V)
    (q : Finset (CV V P × CV V P)) (a : CV V P × CV V P) : Prop :=
  (∃ e ∈ L, q = Tcyc e ∧ ((tag a = none ∧ a = (old e.1, old e.2)) ∨ tag a = some (e, 0))) ∨
  (∃ f ∈ Y, f ∉ L ∧ q = Ccyc c p f ∧ ∃ k, tag a = some (f, k)) ∨
  (∃ e ∈ L, q = Dcyc c p e (β e) ∧ (tag a = some (e, 2) ∨ tag a = some (β e, 1))) ∨
  (∃ x ∈ L, rk (p x.1) < rk (p x.2) ∧ q = Pcyc p x (τ x) ∧
    (tag a = some (x, 3) ∨ tag a = some (τ x, 3)))

lemma pieceClass_eq {Y L : Finset (V × V)} {rk : P → ℕ} {β τ : V × V → V × V}
    (hβinj : ∀ e₁ ∈ L, ∀ e₂ ∈ L, β e₁ = β e₂ → e₁ = e₂) (hβL : ∀ e ∈ L, β e ∈ L)
    (hτ : ∀ x ∈ L, rk (p x.1) < rk (p x.2) → τ x ∈ L ∧ p (τ x).1 = p x.2 ∧ p (τ x).2 = p x.1)
    (hτinj : ∀ x₁ ∈ L, rk (p x₁.1) < rk (p x₁.2) → ∀ x₂ ∈ L, rk (p x₂.1) < rk (p x₂.2) →
        τ x₁ = τ x₂ → x₁ = x₂)
    {q₁ q₂ : Finset (CV V P × CV V P)} {a : CV V P × CV V P}
    (h₁ : PieceClass c p Y L rk β τ q₁ a) (h₂ : PieceClass c p Y L rk β τ q₂ a) : q₁ = q₂ := by
  rcases h₁ with ⟨e₁, he₁, rfl, t₁⟩ | ⟨f₁, -, hf₁L, rfl, k₁, t₁⟩ | ⟨e₁, he₁, rfl, t₁⟩ |
      ⟨x₁, hx₁, l₁, rfl, t₁⟩ <;>
    rcases h₂ with ⟨e₂, he₂, rfl, t₂⟩ | ⟨f₂, -, hf₂L, rfl, k₂, t₂⟩ | ⟨e₂, he₂, rfl, t₂⟩ |
      ⟨x₂, hx₂, l₂, rfl, t₂⟩
  -- T, T
  · rcases t₁ with ⟨t₁, rfl⟩ | t₁ <;> rcases t₂ with ⟨t₂, h₂'⟩ | t₂
    · simp only [old, Prod.mk.injEq, Sum.inl.injEq] at h₂'
      rw [Prod.ext h₂'.1 h₂'.2]
    · rw [t₁] at t₂; simp at t₂
    · rw [t₁] at t₂; simp at t₂
    · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂; rw [t₂.1]
  -- T, C
  · rcases t₁ with ⟨t₁, -⟩ | t₁ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at t₂
    obtain ⟨rfl, -⟩ := t₂; exact absurd he₁ hf₂L
  -- T, D
  · rcases t₁ with ⟨t₁, -⟩ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;> simp at t₂
  -- T, P
  · rcases t₁ with ⟨t₁, -⟩ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;> simp at t₂
  -- C, T
  · rcases t₂ with ⟨t₂, -⟩ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at t₂
    obtain ⟨rfl, -⟩ := t₂; exact absurd he₂ hf₁L
  -- C, C
  · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂; rw [t₂.1]
  -- C, D
  · rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;> obtain ⟨rfl, -⟩ := t₂
    · exact absurd he₂ hf₁L
    · exact absurd (hβL _ he₂) hf₁L
  -- C, P
  · rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;> obtain ⟨rfl, -⟩ := t₂
    · exact absurd hx₂ hf₁L
    · exact absurd (hτ _ hx₂ l₂).1 hf₁L
  -- D, T
  · rcases t₂ with ⟨t₂, -⟩ | t₂ <;> rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;> simp at t₂
  -- D, C
  · rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;> obtain ⟨rfl, -⟩ := t₂
    · exact absurd he₁ hf₂L
    · exact absurd (hβL _ he₁) hf₂L
  -- D, D
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂
    · rw [t₂.1]
    · simp at t₂
    · simp at t₂
    · rw [hβinj e₁ he₁ e₂ he₂ t₂.1]
  -- D, P
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;> simp at t₂
  -- P, T
  · rcases t₂ with ⟨t₂, -⟩ | t₂ <;> rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;> simp at t₂
  -- P, C
  · rcases t₁ with t₁ | t₁ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂ <;> obtain ⟨rfl, -⟩ := t₂
    · exact absurd hx₁ hf₂L
    · exact absurd (hτ _ hx₁ l₁).1 hf₂L
  -- P, D
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;> simp at t₂
  -- P, P
  · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at t₂
    · rw [t₂.1]
    · exfalso
      obtain ⟨-, h1, h2⟩ := hτ _ hx₂ l₂
      have h := l₁
      rw [t₂.1, h1, h2] at h
      omega
    · exfalso
      obtain ⟨-, h1, h2⟩ := hτ _ hx₁ l₁
      have h := l₂
      rw [← t₂.1, h1, h2] at h
      omega
    · rw [hτinj x₁ hx₁ l₁ x₂ hx₂ l₂ t₂.1]

section Main

variable (V P) in
/-- **The cut-hub shortener.** Let `p : V → P` be a partition of the vertices of a cyclically
tripartite `Y` satisfying the cut hypothesis, and `rk : P → ℕ` any injective ranking of the parts.
There is a reserve `R`, fixed before the demand, such that `R` is cyclically tripartite and
arc-disjoint from `Y`, `|R| ≤ 12 |Y|`, every old vertex has reserve degree `2 deg_Y`, every
private vertex has degree at most two, the hub of part `a` has degree
`2 #{e ∈ Y : p e.1 = a ∨ p e.2 = a}`, and for **every** balanced `L ⊆ Y` the graph `R ∪ L`
partitions into directed simple cycles of length at most `12`. -/
theorem cutHub_shortener (c : V → ZMod 3) (p : V → P) (rk : P → ℕ)
    (hrk : Function.Injective rk) (Y : Finset (V × V)) (hY : IsCyc c Y)
    (hcut : CutPartition Y p) :
    ∃ R : Finset (CV V P × CV V P),
      IsCyc (Sum.elim c (hcol c)) R ∧ Disjoint R (Y.map (liftArc V _)) ∧
      R.card ≤ 12 * Y.card ∧
      (∀ v, deg R (Sum.inl v) = 2 * deg Y v) ∧
      (∀ x, deg R (Sum.inr (Sum.inr x)) ≤ 2) ∧
      (∀ a, deg R (Sum.inr (Sum.inl a)) =
        2 * (Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card) ∧
      ∀ L ⊆ Y, Balanced L →
        ∃ Q : Finset (Finset (CV V P × CV V P)),
          IsCyclePartition 12 Q (R ∪ L.map (liftArc V _)) := by
  classical
  have hdisjY : ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → Disjoint (Ccyc c p i) (Ccyc c p j) :=
    fun i _ j _ hij => Ccyc_disjoint c p hij
  have hliftmem : ∀ {a : CV V P × CV V P} {L : Finset (V × V)},
      a ∈ L.map (liftArc V (P ⊕ ((V × V) × Fin 9))) ↔ ∃ e ∈ L, a = (old e.1, old e.2) := by
    intro a L
    simp only [Finset.mem_map, liftArc, Function.Embedding.coeFn_mk, old]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩
  refine ⟨reserve c p Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    exact isCyc_Ccyc c p (hY e he) a hae
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 ha
    obtain ⟨f, -, rfl⟩ := hliftmem.1 hb
    exact old_not_mem_Ccyc c p _ _ hae
  · unfold reserve
    rw [Finset.card_biUnion hdisjY, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨k, f, hk, hf, hC, -⟩ := Ccyc_eq c p (hY e he)
    rw [hC, card_cycF hf]; exact hk
  · intro v
    have h := deg_biUnion Y (Ccyc c p) hdisjY (old v)
    unfold reserve
    rw [show (Sum.inl v : CV V P) = old v from rfl, h]
    rw [Finset.sum_congr rfl fun e he => deg_Ccyc_old c p (hY e he) v]
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
    rw [deg_biUnion Y (Ccyc c p) hdisjY]
    calc ∑ e ∈ Y, deg (Ccyc c p e) (Sum.inr (Sum.inr x))
        ≤ ∑ e ∈ Y, (if x.1 = e then 2 else 0) :=
          Finset.sum_le_sum fun e he => deg_Ccyc_pv c p (hY e he) x
      _ ≤ 2 := by
          rw [Finset.sum_ite_eq]
          split_ifs <;> omega
  · intro a
    unfold reserve
    rw [deg_biUnion Y (Ccyc c p) hdisjY]
    rw [show (Sum.inr (Sum.inl a) : CV V P) = hub a from rfl]
    rw [Finset.sum_congr rfl fun e he => deg_Ccyc_hub c p (hY e he) a]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
      mul_comm]
  · intro L hLY hLb
    obtain ⟨β, hβ, hβinj, hβsurj⟩ := Hub.exists_pairing L hLb
    obtain ⟨τ, hτ, hτinj, hτsurj⟩ := exists_cross_pairing p hcut hLY hLb rk
    set F := L.filter (fun x => rk (p x.1) < rk (p x.2)) with hF
    have hcross : ∀ f : V × V, p f.1 ≠ p f.2 → rk (p f.1) < rk (p f.2) ∨ rk (p f.2) < rk (p f.1) := by
      intro f hf
      rcases lt_trichotomy (rk (p f.1)) (rk (p f.2)) with h | h | h
      · exact Or.inl h
      · exact absurd (hrk h) hf
      · exact Or.inr h
    refine ⟨L.image Tcyc ∪ (Y \ L).image (Ccyc c p) ∪ L.image (fun e => Dcyc c p e (β e)) ∪
      F.image (fun x => Pcyc p x (τ x)), ?_, ?_, ?_⟩
    · intro q hq
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
      rcases hq with ((⟨e, he, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩
      · exact isDirCycle_T (ne_of_cyc c (hY e (hLY he)))
      · obtain ⟨k, f, hk, hf, hC, -⟩ := Ccyc_eq c p (hY e he)
        rw [hC]; exact ⟨isDirCycle_cycF hf, by rw [card_cycF hf]; exact hk⟩
      · exact isDirCycle_D c p (hβ e he).2.symm
      · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
        obtain ⟨-, h1, h2⟩ := hτ x hxL hlt
        exact isDirCycle_P p (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt) h1 h2
    · have hclass : ∀ q ∈ L.image Tcyc ∪ (Y \ L).image (Ccyc c p) ∪
          L.image (fun e => Dcyc c p e (β e)) ∪ F.image (fun x => Pcyc p x (τ x)),
          ∀ a ∈ q, PieceClass c p Y L rk β τ q a := by
        intro q hq a ha
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
        rcases hq with ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, hfL⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩
        · refine Or.inl ⟨e, he, rfl, ?_⟩
          simp only [Tcyc, Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · exact Or.inl ⟨tag_old _ _, rfl⟩
          · exact Or.inr (tag_piA ha)
        · refine Or.inr (Or.inl ⟨f, hf, hfL, rfl, ?_⟩)
          rcases tag_Ccyc c p ha with t | t | t | t <;> exact ⟨_, t⟩
        · refine Or.inr (Or.inr (Or.inl ⟨e, he, rfl, ?_⟩))
          simp only [Dcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (tag_IA c p ha)
          · exact Or.inr (tag_OA c p ha)
        · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
          refine Or.inr (Or.inr (Or.inr ⟨x, hxL, hlt, rfl, ?_⟩))
          simp only [Pcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (tag_QA p ha)
          · exact Or.inr (tag_QA p ha)
      intro q₁ hq₁ q₂ hq₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a h₁ h₂
      exact hne (pieceClass_eq c p hβinj (fun e he => (hβ e he).1) hτ hτinj
        (hclass q₁ hq₁ a h₁) (hclass q₂ hq₂ a h₂))
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
        id_eq]
      constructor
      · rintro ⟨q, ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩, ha⟩
        · simp only [Tcyc, Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · exact Or.inr (hliftmem.2 ⟨e, he, rfl⟩)
          · exact Or.inl (Finset.mem_biUnion.2 ⟨e, hLY he, (mem_Ccyc c p).2 (Or.inl ha)⟩)
        · exact Or.inl (Finset.mem_biUnion.2 ⟨f, hf, ha⟩)
        · simp only [Dcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (Finset.mem_biUnion.2
              ⟨e, hLY he, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inr ha)))⟩)
          · exact Or.inl (Finset.mem_biUnion.2
              ⟨β e, hLY (hβ e he).1, (mem_Ccyc c p).2 (Or.inr (Or.inl ha))⟩)
        · obtain ⟨hxL, hlt⟩ := Finset.mem_filter.1 hx
          simp only [Pcyc, Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact Or.inl (Finset.mem_biUnion.2
              ⟨x, hLY hxL, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha)))⟩)
          · exact Or.inl (Finset.mem_biUnion.2
              ⟨τ x, hLY (hτ x hxL hlt).1, (mem_Ccyc c p).2 (Or.inr (Or.inr (Or.inl ha)))⟩)
      · rintro (ha | ha)
        · obtain ⟨f, hf, haf⟩ := Finset.mem_biUnion.1 ha
          by_cases hfL : f ∈ L
          · rcases (mem_Ccyc c p).1 haf with h | h | h | h
            · exact ⟨Tcyc f, Or.inl (Or.inl (Or.inl ⟨f, hfL, rfl⟩)), Finset.mem_insert_of_mem h⟩
            · obtain ⟨e, he, rfl⟩ := hβsurj f hfL
              exact ⟨Dcyc c p e (β e), Or.inl (Or.inr ⟨e, he, rfl⟩),
                Finset.mem_union_right _ h⟩
            · have hpf : p f.1 ≠ p f.2 := by
                intro hpf; simp [QA, hpf] at h
              rcases hcross f hpf with hlt | hlt
              · exact ⟨Pcyc p f (τ f), Or.inr ⟨f, Finset.mem_filter.2 ⟨hfL, hlt⟩, rfl⟩,
                  Finset.mem_union_left _ h⟩
              · obtain ⟨x, hxL, hxlt, rfl⟩ := hτsurj f hfL hlt
                exact ⟨Pcyc p x (τ x), Or.inr ⟨x, Finset.mem_filter.2 ⟨hxL, hxlt⟩, rfl⟩,
                  Finset.mem_union_right _ h⟩
            · exact ⟨Dcyc c p f (β f), Or.inl (Or.inr ⟨f, hfL, rfl⟩),
                Finset.mem_union_left _ h⟩
          · exact ⟨Ccyc c p f, Or.inl (Or.inl (Or.inr ⟨f, ⟨hf, hfL⟩, rfl⟩)), haf⟩
        · obtain ⟨e, he, rfl⟩ := hliftmem.1 ha
          exact ⟨Tcyc e, Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩)), Finset.mem_insert_self _ _⟩

/-- `Y` admits a cut partition (`CutPartition`) into parts of arc load at most `B`, with a finite
set of parts. -/
def CutShortenable {V : Type*} [DecidableEq V] (B : ℕ) (Y : Finset (V × V)) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (p : V → P), CutPartition Y p ∧
    ∀ a, (Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card ≤ B

/-- **Target A on the cut-shortenable class.** If `Y` (cyclically tripartite, maximum degree
`≤ 17`) admits a cut partition with part loads `≤ B`, then the conclusion of
`CycleShortenerWith (max 34 (2 B)) 12` holds for `Y`: a fixed reserve of size `≤ 12 |Y|` and
maximum degree `≤ max 34 (2B)` such that `R ∪ L` splits into directed cycles of length `≤ 12`
for every balanced `L ⊆ Y`. -/
theorem cycleShortener_of_cutShortenable (V : Type) [Fintype V] [DecidableEq V]
    (c : V → ZMod 3) (Y : Finset (V × V)) (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17) (B : ℕ)
    (hB : CutShortenable B Y) :
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset ((V ⊕ U) × (V ⊕ U))),
      IsCyc (Sum.elim c cU) R ∧ Disjoint R (Y.map (liftArc V U)) ∧
      R.card ≤ 12 * Y.card ∧ MaxDegLE R (max 34 (2 * B)) ∧
      ∀ L ⊆ Y, Balanced L →
        ∃ Q : Finset (Finset ((V ⊕ U) × (V ⊕ U))),
          IsCyclePartition 12 Q (R ∪ L.map (liftArc V U)) := by
  obtain ⟨P, hPf, hPd, p, hcut, hload⟩ := hB
  obtain ⟨R, hRc, hRd, hRcard, hold, hpv, hhub, hpart⟩ :=
    cutHub_shortener V P c p (fun a => (Fintype.equivFin P a).val)
      (fun a b h => (Fintype.equivFin P).injective (Fin.ext h)) Y hY hcut
  refine ⟨P ⊕ ((V × V) × Fin 9), inferInstance, inferInstance, hcol c, R, hRc, hRd, hRcard,
    ?_, hpart⟩
  rintro (v | a | x)
  · rw [hold v]; have := hdeg v; omega
  · rw [hhub a]; have := hload a; omega
  · have := hpv x; omega

end Main

end CutHub

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.CutHub.cutHub_shortener
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.CutHub.cycleShortener_of_cutShortenable
