import Toffoli.Universality.CoordinatePermutationApply
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Pi

namespace Toffoli

/-- Embedding a one-wire affine map gives an affine map of the register:
its linear part acts on that wire and is the identity on the others. -/
theorem coordinate_permutation_affine {R I : Type*} [Ring R]
    (i : I) (e : R ≃ᵃ[R] R) :
    ∃ lift : (I → R) ≃ᵃ[R] (I → R),
      lift.toEquiv = coordinatePermutation i e.toEquiv := by
  classical
  refine ⟨{
    toEquiv := coordinatePermutation i e.toEquiv
    linear := LinearEquiv.piCongrRight (fun j =>
      if j = i then e.linear else LinearEquiv.refl R R)
    map_vadd' := ?_ }, rfl⟩
  intro x v
  funext j
  by_cases h : j = i
  · simpa [coordinate_permutation_apply, LinearEquiv.piCongrRight_apply, h] using
      e.map_vadd (x j) (v j)
  · simp [coordinate_permutation_apply, LinearEquiv.piCongrRight_apply, h]

end Toffoli
