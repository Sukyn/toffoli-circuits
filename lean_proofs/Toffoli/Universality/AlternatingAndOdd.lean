import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace Toffoli
open scoped Classical

/-- Once every even permutation is available, one odd permutation suffices.
Multiplying any odd permutation by the supplied one's inverse makes it even. -/
theorem alternating_and_odd {X : Type*} [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hAlt : alternatingGroup X ≤ G)
    (τ : Equiv.Perm X) (hτ : τ ∈ G) (hodd : Equiv.Perm.sign τ = -1) :
    G = ⊤ := by
  apply top_unique
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · exact hAlt (Equiv.Perm.mem_alternatingGroup.mpr hσ)
  · have heven : σ * τ⁻¹ ∈ alternatingGroup X := by
      apply Equiv.Perm.mem_alternatingGroup.mpr
      simp [map_mul, hσ, hodd]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using G.mul_mem (hAlt heven) hτ

end Toffoli
