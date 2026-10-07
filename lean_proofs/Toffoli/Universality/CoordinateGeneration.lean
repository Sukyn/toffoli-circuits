import Toffoli.Universality.AffineSwapLiftMem
import Toffoli.Universality.CoordinatePermutationAffine

namespace Toffoli

/-- If affine maps and τ generate every one-wire permutation, then a register
with τ on one fixed wire can apply any label permutation on any wire.
First exchange wires to move τ; then lift the one-wire generation argument. -/
theorem coordinate_generation {R I : Type*} [CommRing R]
    (origin i : I) (τ σ : Equiv.Perm R) (h : affineSwapGroup R τ = ⊤) :
    coordinatePermutation i σ ∈ affineSwapGroup R (coordinatePermutation origin τ) := by
  classical
  let G := affineSwapGroup R (coordinatePermutation origin τ)
  have affine_mem (e : (I → R) ≃ᵃ[R] (I → R)) : e.toEquiv ∈ G :=
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)
  have original_mem : coordinatePermutation origin τ ∈ G :=
    Subgroup.subset_closure (Or.inr rfl)

  -- Conjugating by the affine wire exchange places the fixed gate at i.
  let s := Equiv.swap origin i
  let e := (LinearEquiv.funCongrLeft R R s).toAffineEquiv
  have conjugacy : e.toEquiv * coordinatePermutation origin τ * e.toEquiv⁻¹ =
      coordinatePermutation i τ := by
    ext x j
    change coordinatePermutation origin τ (fun k => x (s k)) (s j) =
      coordinatePermutation i τ x j
    simp [coordinate_permutation_apply, s, Equiv.swap_apply_eq_iff]
  have fixed_mem : coordinatePermutation i τ ∈ G := by
    rw [← conjugacy]
    exact G.mul_mem (G.mul_mem (affine_mem e) original_mem) (G.inv_mem (affine_mem e))

  -- Lift the one-wire generators: affine maps stay affine, and τ is available at i.
  apply affine_swap_lift_mem τ h (coordinatePermutation i) G ?_ fixed_mem σ
  intro a
  obtain ⟨lift, hlift⟩ := coordinate_permutation_affine i a
  rw [← hlift]
  exact affine_mem lift

end Toffoli
