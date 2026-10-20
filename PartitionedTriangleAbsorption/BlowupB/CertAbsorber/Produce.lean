/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Cert

/-! # Producing explicit certificates

* `BdRep p F n f`: the function `f : Sym2 W → ℤ` is the integer boundary of an explicit list of
  at most `n` signed occurrences of allowed triangles (distinct corners, type in `F`).  It is
  closed under sums, negation and integer multiples, with additive control of the length.
* `exists_signedCert_of_bdRep`: such a list with boundary `𝟙_P` **is** a `SignedCert p F P`
  of length `≤ n`.
* `exists_signedCert_of_rep` / `rep_of_signedCert` / `inTriLattice_iff`: a certificate of `P`
  exists iff `𝟙_P` lies in the integer lattice spanned by the edge indicators of the allowed
  triangles on `W` (physical lattice membership, `InTriLattice`); the length of the produced
  certificate is exactly the `ℓ¹`-norm of the coefficient vector.
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption

variable {W : Type*} [DecidableEq W] {t : ℕ}

/-- A signed occurrence: a sign (`true` = `+1`) and three corners. -/
abbrev Occ (W : Type*) := Bool × (Fin 3 → W)

/-- The integer value of a sign. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- Integer boundary of one signed occurrence. -/
def occBd (o : Occ W) (e : Sym2 W) : ℤ :=
  sgn o.1 * if e ∈ triEdges (univ.image o.2) then 1 else 0

/-- Integer boundary of a list of signed occurrences. -/
def listBd (l : List (Occ W)) (e : Sym2 W) : ℤ := (l.map fun o => occBd o e).sum

/-- A valid occurrence: distinct corners, type in `F`. -/
def ValidOcc (p : W → Fin t) (F : Finset (Multiset (Fin t))) (o : Occ W) : Prop :=
  Function.Injective o.2 ∧ ({p (o.2 0), p (o.2 1), p (o.2 2)} : Multiset (Fin t)) ∈ F

/-- `f` is the integer boundary of an explicit list of at most `n` valid occurrences. -/
def BdRep (p : W → Fin t) (F : Finset (Multiset (Fin t))) (n : ℕ) (f : Sym2 W → ℤ) : Prop :=
  ∃ l : List (Occ W), (∀ o ∈ l, ValidOcc p F o) ∧ l.length ≤ n ∧ ∀ e, listBd l e = f e

namespace BdRep

variable {p : W → Fin t} {F : Finset (Multiset (Fin t))}

lemma zero : BdRep p F 0 0 := ⟨[], by simp, by simp, by simp [listBd]⟩

lemma mono {n m : ℕ} {f : Sym2 W → ℤ} (h : BdRep p F n f) (hnm : n ≤ m) : BdRep p F m f := by
  obtain ⟨l, hv, hl, hb⟩ := h
  exact ⟨l, hv, hl.trans hnm, hb⟩

lemma congr {n : ℕ} {f g : Sym2 W → ℤ} (h : BdRep p F n f) (hfg : f = g) : BdRep p F n g :=
  hfg ▸ h

lemma add {n m : ℕ} {f g : Sym2 W → ℤ} (hf : BdRep p F n f) (hg : BdRep p F m g) :
    BdRep p F (n + m) (f + g) := by
  obtain ⟨l, hv, hl, hb⟩ := hf
  obtain ⟨l', hv', hl', hb'⟩ := hg
  refine ⟨l ++ l', fun o ho => ?_, by simp; omega, fun e => ?_⟩
  · rcases List.mem_append.mp ho with h | h
    · exact hv o h
    · exact hv' o h
  · simp [listBd] at hb hb' ⊢
    rw [hb, hb']

lemma neg {n : ℕ} {f : Sym2 W → ℤ} (hf : BdRep p F n f) : BdRep p F n (-f) := by
  obtain ⟨l, hv, hl, hb⟩ := hf
  refine ⟨l.map fun o => (!o.1, o.2), fun o ho => ?_, by simpa using hl, fun e => ?_⟩
  · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hv o' ho'
  · have : ∀ o : Occ W, occBd ((!o.1, o.2) : Occ W) e = - occBd o e := by
      rintro ⟨b, v⟩; cases b <;> simp [occBd, sgn] <;> split_ifs <;> simp
    have hneg : ∀ l' : List (Occ W), (l'.map fun o => - occBd o e).sum =
        - (l'.map fun o => occBd o e).sum := by
      intro l'; induction l' with
      | nil => simp
      | cons a l' ih => simp [ih]; ring
    simp only [listBd, List.map_map, Function.comp_def, this, Pi.neg_apply] at hb ⊢
    rw [hneg, hb]

lemma sub {n m : ℕ} {f g : Sym2 W → ℤ} (hf : BdRep p F n f) (hg : BdRep p F m g) :
    BdRep p F (n + m) (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma nsmul {n : ℕ} {f : Sym2 W → ℤ} (hf : BdRep p F n f) (k : ℕ) :
    BdRep p F (k * n) (k • f) := by
  induction k with
  | zero => simpa using (zero : BdRep p F 0 0)
  | succ k ih => exact (ih.add hf).congr (by rw [succ_nsmul]) |>.mono (by rw [Nat.succ_mul])

lemma zsmul {n : ℕ} {f : Sym2 W → ℤ} (hf : BdRep p F n f) (z : ℤ) :
    BdRep p F (z.natAbs * n) (z • f) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · refine (hf.nsmul m).congr ?_
    funext e; simp
  · refine ((hf.nsmul m).neg).mono (by simp) |>.congr ?_
    funext e; simp

lemma sum {ι : Type*} (S : Finset ι) (n : ι → ℕ) (f : ι → Sym2 W → ℤ)
    (h : ∀ i ∈ S, BdRep p F (n i) (f i)) : BdRep p F (∑ i ∈ S, n i) (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero : BdRep p F 0 0)
  | insert j S hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (h j (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma occ {o : Occ W} (ho : ValidOcc p F o) : BdRep p F 1 (occBd o) :=
  ⟨[o], by simpa using ho, by simp, fun e => by simp [listBd]⟩

end BdRep

/-- **From an explicit list to a certificate.**  A valid list of at most `n` signed
occurrences whose boundary is `𝟙_P` is a signed certificate of `P` of length `≤ n`. -/
theorem exists_signedCert_of_bdRep {p : W → Fin t} {F : Finset (Multiset (Fin t))}
    {P : Finset (Sym2 W)} {n : ℕ} (h : BdRep p F n fun e => if e ∈ P then 1 else 0) :
    ∃ c : SignedCert p F P, c.k ≤ n := by
  obtain ⟨l, hv, hl, hb⟩ := h
  refine ⟨SignedCert.mk l.length (fun i => (l.get i).2) (fun i => (l.get i).1)
    (fun i => (hv _ (List.get_mem l i)).1) (fun i => (hv _ (List.get_mem l i)).2)
    (fun e => ?_), hl⟩
  have hbe := hb e
  simp only at hbe
  rw [← hbe, listBd, ← Fin.sum_univ_fun_getElem l (fun o => occBd o e)]
  refine sum_congr rfl fun i _ => ?_
  simp [occBd, sgn]

/-! ### Physical lattice membership -/

section Lattice

variable [Fintype W] (p : W → Fin t) (F : Finset (Multiset (Fin t)))

/-- The allowed triangles on `W`: three-element vertex sets whose type is in `F`. -/
noncomputable def typedTris : Finset (Finset W) := by
  classical exact (univ : Finset (Finset W)).filter fun s => IsTypedTri p F s

/-- Integer boundary of a coefficient vector on the allowed triangles. -/
noncomputable def triBd (z : Finset W → ℤ) (e : Sym2 W) : ℤ :=
  ∑ s ∈ typedTris p F, z s * if e ∈ triEdges s then 1 else 0

/-- `ℓ¹`-norm of a coefficient vector on the allowed triangles. -/
noncomputable def l1Norm (z : Finset W → ℤ) : ℕ := ∑ s ∈ typedTris p F, (z s).natAbs

/-- **Physical lattice membership**: `𝟙_P` is an integer combination of the edge indicators of
the allowed triangles on `W`. -/
def InTriLattice (P : Finset (Sym2 W)) : Prop :=
  ∃ z : Finset W → ℤ, ∀ e, triBd p F z e = if e ∈ P then 1 else 0

variable {p F}

omit [DecidableEq W] in
lemma mem_typedTris {s : Finset W} : s ∈ typedTris p F ↔ IsTypedTri p F s := by
  simp [typedTris]

omit [Fintype W] in
/-- An allowed triangle, written with ordered corners, is a valid occurrence. -/
lemma exists_validOcc_of_typed {s : Finset W} (hs : IsTypedTri p F s) :
    ∃ v : Fin 3 → W, Function.Injective v ∧ univ.image v = s ∧
      ({p (v 0), p (v 1), p (v 2)} : Multiset (Fin t)) ∈ F := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs.1
  refine ⟨![a, b, c], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · ext x; simp [Fin.exists_fin_succ, eq_comm]
  · have := hs.2
    rw [map_three p hab hac hbc] at this
    simpa using this

/-- **Certificate from a lattice representation**, of length equal to the `ℓ¹`-norm. -/
theorem exists_signedCert_of_rep {P : Finset (Sym2 W)} (z : Finset W → ℤ)
    (hz : ∀ e, triBd p F z e = if e ∈ P then 1 else 0) :
    ∃ c : SignedCert p F P, c.k ≤ l1Norm p F z := by
  classical
  have hv : ∀ s ∈ typedTris p F, ∃ v : Fin 3 → W, Function.Injective v ∧ univ.image v = s ∧
      ({p (v 0), p (v 1), p (v 2)} : Multiset (Fin t)) ∈ F :=
    fun s hs => exists_validOcc_of_typed (mem_typedTris.mp hs)
  choose v hvinj hvimg hvtyp using hv
  refine exists_signedCert_of_bdRep ?_
  have h := BdRep.sum (p := p) (F := F) (typedTris p F).attach (fun x => (z x.1).natAbs * 1)
    (fun x => z x.1 • occBd ((true, v x.1 x.2) : Occ W))
    (fun x _ => (BdRep.occ ⟨hvinj x.1 x.2, hvtyp x.1 x.2⟩).zsmul (z x.1))
  simp only [mul_one] at h
  rw [sum_attach (typedTris p F) (fun s => (z s).natAbs)] at h
  refine h.congr ?_
  funext e
  rw [← hz e, triBd, Finset.sum_apply, ← sum_attach (typedTris p F)]
  refine sum_congr rfl fun x _ => ?_
  simp [occBd, sgn, hvimg x.1 x.2]

lemma natAbs_sum_le' {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ S, f i).natAbs ≤ ∑ i ∈ S, (f i).natAbs := by
  have h : ((∑ i ∈ S, f i).natAbs : ℤ) ≤ ((∑ i ∈ S, (f i).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; push_cast
    simpa [Int.natCast_natAbs] using Finset.abs_sum_le_sum_abs f S
  exact_mod_cast h

/-- **Lattice representation from a certificate**, with `ℓ¹`-norm at most the length. -/
theorem rep_of_signedCert {P : Finset (Sym2 W)} (c : SignedCert p F P) :
    ∃ z : Finset W → ℤ, (∀ e, triBd p F z e = if e ∈ P then 1 else 0) ∧
      l1Norm p F z ≤ c.k := by
  classical
  set T : Fin c.k → Finset W := fun i => univ.image (c.vtx i) with hT
  have hTt : ∀ i, T i ∈ typedTris p F := by
    intro i
    refine mem_typedTris.mpr ⟨?_, ?_⟩
    · rw [hT, card_image_of_injective _ (c.inj i)]; simp
    · have himg : T i = {c.vtx i 0, c.vtx i 1, c.vtx i 2} := by
        ext x; simp [hT, Fin.exists_fin_succ, eq_comm]
      have h01 : c.vtx i 0 ≠ c.vtx i 1 := fun h => by simpa using c.inj i h
      have h02 : c.vtx i 0 ≠ c.vtx i 2 := fun h => by simpa using c.inj i h
      have h12 : c.vtx i 1 ≠ c.vtx i 2 := fun h => by simpa using c.inj i h
      rw [himg, map_three p h01 h02 h12]
      exact c.typed i
  refine ⟨fun s => ∑ i ∈ univ.filter (fun i => T i = s), sgn (c.pos i), fun e => ?_, ?_⟩
  · rw [← c.boundary e, triBd]
    simp only [sum_mul]
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := typedTris p F) (g := T)
      (fun i _ => hTt i)]
    refine sum_congr rfl fun s _ => sum_congr rfl fun i hi => ?_
    rw [(mem_filter.mp hi).2.symm]
    simp [sgn, hT]
  · unfold l1Norm
    calc ∑ s ∈ typedTris p F, (∑ i ∈ univ.filter (fun i => T i = s), sgn (c.pos i)).natAbs
        ≤ ∑ s ∈ typedTris p F, ∑ i ∈ univ.filter (fun i => T i = s), (sgn (c.pos i)).natAbs :=
          sum_le_sum fun s _ => natAbs_sum_le' _ _
      _ = ∑ s ∈ typedTris p F, ∑ i ∈ univ.filter (fun i => T i = s), 1 := by
          refine sum_congr rfl fun s _ => sum_congr rfl fun i _ => ?_
          cases c.pos i <;> rfl
      _ = ∑ i : Fin c.k, 1 := sum_fiberwise_of_maps_to (fun i _ => hTt i) _
      _ = c.k := by simp

/-- **A certificate exists iff the residue is in the physical triangle lattice.** -/
theorem inTriLattice_iff {P : Finset (Sym2 W)} :
    InTriLattice p F P ↔ Nonempty (SignedCert p F P) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, -⟩ := exists_signedCert_of_rep z hz
    exact ⟨c⟩
  · rintro ⟨c⟩
    obtain ⟨z, hz, -⟩ := rep_of_signedCert c
    exact ⟨z, hz⟩

end Lattice

end PaperII.CertAbsorber
