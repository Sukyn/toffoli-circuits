import Toffoli.Universality.CoordinatePermutationModel

namespace Toffoli
open scoped Classical

/-- The chosen coordinate is relabelled; all other coordinates retain their values. -/
theorem coordinate_permutation_apply {I A : Type*} (i : I) (σ : Equiv.Perm A)
    (x : I → A) (j : I) :
    coordinatePermutation i σ x j = if j = i then σ (x j) else x j := by
  change ((Pi.mulSingle i σ : I → Equiv.Perm A) j) (x j) = _
  by_cases h : j = i
  · subst j; simp
  · simp [h]

end Toffoli
