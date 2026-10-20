/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.CompL

@[expose] public section

/-! Larger flexible exponents impose a smaller input reserve. This monotonicity
lets finitely many independently constructed component certificates share one scale. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open PaddedGeneral.RealInverse BalFixer

theorem flexScales_mono {L L' : ℕ} (hLL : L ≤ L')
    {ω δ ρ n : ℝ} (h : FlexScalesL L' ω δ ρ n) :
    FlexScalesL L ω δ ρ n := by
  refine ⟨h.ω_pos, h.ω_le, h.δ_pos, h.δ_le, h.ρ_sq.trans ?_, h.n_nonneg, h.ρn⟩
  have hp : (2 : ℝ) ^ L ≤ 2 ^ L' := pow_le_pow_right₀ (by norm_num) hLL
  have hz : 0 ≤ ω ^ 2 * δ := mul_nonneg (sq_nonneg _) h.δ_pos.le
  have hd : ω ^ 2 * δ / 2 ^ L' ≤ ω ^ 2 * δ / 2 ^ L :=
    div_le_div_of_nonneg_left hz (by positivity) hp
  exact pow_le_pow_left₀ (by positivity) hd 2

theorem componentCertificate_mono {t L L' : ℕ}
    {F : Finset (Multiset (Fin t))} {c : Fin t → Fin t} {k : Fin t}
    (hLL : L ≤ L') (h : ComponentCertFlexTL F c k L) :
    ComponentCertFlexTL F c k L' := by
  intro V _ _ p G _ ω δ ρ hsc
  exact h V p G ω δ ρ (flexScales_mono hLL hsc)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.flexScales_mono
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.componentCertificate_mono

