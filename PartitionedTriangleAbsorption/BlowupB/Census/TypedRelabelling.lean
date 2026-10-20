/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPerm
public import PartitionedTriangleAbsorption.BlowupB.Census.Uniqueness

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

open Finset

theorem permFam_eq_image {t : ℕ} (s : Equiv.Perm (Fin t))
    (F : Finset (Multiset (Fin t))) : permFam s F = F.image (Multiset.map s) := by
  ext τ
  simp [permFam]

section Transport

variable {t : ℕ} (s : Equiv.Perm (Fin t))
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thirdsT_relabel (p : V → Fin t) (G : Finset (Sym2 V))
    (u v : V) (τ : Multiset (Fin t)) :
    thirdsT (s.symm ∘ p) G u v τ = thirdsT p G u v (τ.map s) := by
  ext w
  simp only [thirdsT, mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,h₂,h₃,h₄, ?_⟩
    simpa using congrArg (Multiset.map s) h₅
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,h₂,h₃,h₄, ?_⟩
    simpa [Multiset.map_map] using congrArg (Multiset.map s.symm) h₅

theorem triRegular_relabel {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : Finset (Sym2 V)} {ω c : ℝ} (h : TriRegular p (permFam s F) G ω c) :
    TriRegular (s.symm ∘ p) F G ω c := by
  obtain ⟨y, hy, he⟩ := h
  refine ⟨y, ?_, ?_⟩
  · intro S hS hG
    apply hy S ⟨hS.1, ?_⟩ hG
    have hmap : S.val.map p = (S.val.map (s.symm ∘ p)).map s := by
      rw [Multiset.map_map]
      simp
    rw [hmap]
    exact (mem_permFam s).mpr hS.2
  · intro u v huv
    have hh := he u v huv
    unfold permFam at hh
    rw [sum_map] at hh
    simpa only [Function.Embedding.coeFn_mk, ← thirdsT_relabel] using hh

theorem cnExt_relabel {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : Finset (Sym2 V)} {ω : ℝ} {h : ℕ} (he : CNExt p (permFam s F) G ω h) :
    CNExt (s.symm ∘ p) F G ω h := by
  intro S A i hS hA hallow
  have hh := he S A (s i) hS hA (fun a ha => by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      allowed_perm' s (hallow a ha))
  simpa only [Function.comp_apply, Equiv.symm_apply_eq] using hh

end Transport

/-- Relabelling changes the label function, not any physical graph or budget. -/
theorem keevashTypedSpec_relabel {t : ℕ} (s : Equiv.Perm (Fin t))
    {F : Finset (Multiset (Fin t))} (hF : KeevashTypedSpec F) :
    KeevashTypedSpec (permFam s F) := by
  intro γ hγ
  obtain ⟨h, ω₀, hω₀, hrest⟩ := hF γ hγ
  refine ⟨h, ω₀, hω₀, ?_⟩
  intro ω hω hωmax
  obtain ⟨c, hc, n₀, hn₀⟩ := hrest ω hω hωmax
  refine ⟨c, hc, n₀, ?_⟩
  intro V _ _ p G hn hcls hloop hadj hreg hext hdiv
  apply hasDecomp_perm s
  apply hn₀ (s.symm ∘ p) G hn
  · intro i
    rw [classCard_perm]
    exact hcls (s i)
  · exact hloop
  · intro u v huv
    exact allowed_perm s (hadj u v huv)
  · exact triRegular_relabel s hreg
  · exact cnExt_relabel s hext
  · exact isIntDiv_perm s hdiv

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.keevashTypedSpec_relabel
