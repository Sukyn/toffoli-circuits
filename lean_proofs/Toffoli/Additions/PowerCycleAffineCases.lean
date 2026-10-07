import Toffoli.Additions.PowerCycleFixedPoint

namespace Toffoli

/-- The only admissible affine maps are nonidentity multipliers or nonzero
translations. A shifted multiplier has a forbidden nonzero fixed point. -/
theorem power_cycle_affine_cases {K : Type*} [Field K]
    (a b μ : K) (ha : a ≠ 0) (d : ℕ) (hμ : μ ≠ 0)
    (hadm : PowerCycleAdmissible a b μ ha d) :
    (b = 0 ∧ a ≠ 1) ∨ (a = 1 ∧ b ≠ 0) := by
  by_cases hone : a = 1
  · refine Or.inr ⟨hone, ?_⟩
    intro hb
    have hz := power_cycle_fixed_point a b μ ha d hμ hadm 1 (by simp [hone, hb])
    exact one_ne_zero hz
  · refine Or.inl ⟨?_, hone⟩
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hone)
    have hfix : a * (b / (1 - a)) + b = b / (1 - a) := by
      field_simp [hden]
      ring
    have hz := power_cycle_fixed_point a b μ ha d hμ hadm (b / (1 - a)) hfix
    exact (div_eq_zero_iff.mp hz).resolve_right hden

end Toffoli
