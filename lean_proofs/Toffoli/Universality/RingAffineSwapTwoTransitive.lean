import Toffoli.Universality.CoordinateGeneration
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Transvection.Basic

namespace Toffoli

/-- One-wire universality makes the register action doubly transitive,
even over a ring. Normalize one nonzero coordinate to one, clear the
remaining coordinates by a transvection, and move that wire to `origin`.
Translating first applies this normalization to any pair of distinct states. -/
theorem ring_affine_swap_two_pretransitive {R I : Type*} [CommRing R]
    [Nontrivial R] [DecidableEq R] (origin : I)
    (hone : affineSwapGroup R (Equiv.swap (0 : R) 1) = ⊤) :
    MulAction.IsMultiplyPretransitive
      (affineSwapGroup R (coordinatePermutation origin (Equiv.swap (0 : R) 1)))
      (I → R) 2 := by
  classical
  let G := affineSwapGroup R (coordinatePermutation origin (Equiv.swap (0 : R) 1))
  have affine_mem (e : (I → R) ≃ᵃ[R] (I → R)) : e.toEquiv ∈ G :=
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)

  have normalize (x : I → R) (hx : x ≠ 0) :
      ∃ g ∈ G, g 0 = 0 ∧ g x = Pi.single origin (1 : R) := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    let σ := coordinatePermutation i (Equiv.swap (x i) 1)
    have hσ : σ ∈ G := coordinate_generation origin i _ _ hone
    have hσ0 : σ 0 = 0 := by
      funext j
      simp [σ, coordinate_permutation_apply,
        Equiv.swap_apply_of_ne_of_ne hi.symm zero_ne_one]
    let z := σ x
    have hzi : z i = 1 := by simp [z, σ, coordinate_permutation_apply]

    -- Its correction has zero i-coordinate, so the transvection is invertible.
    let v := Pi.single i (1 : R) - z
    have hvi : (LinearMap.proj i : (I → R) →ₗ[R] R) v = 0 := by
      simp [v, hzi]
    let e := (LinearEquiv.transvection hvi).toAffineEquiv
    have hez : e z = Pi.single i (1 : R) := by
      change z + z i • (Pi.single i (1 : R) - z) = _
      simp [hzi]
    let w := (LinearEquiv.funCongrLeft R R (Equiv.swap origin i)).toAffineEquiv
    have hw : w (Pi.single i (1 : R)) = Pi.single origin (1 : R) := by
      funext j
      change (Pi.single i (1 : R) : I → R) (Equiv.swap origin i j) =
        (Pi.single origin (1 : R) : I → R) j
      simp [Pi.single_apply, Equiv.swap_apply_eq_iff]
    refine ⟨w.toEquiv * e.toEquiv * σ,
      G.mul_mem (G.mul_mem (affine_mem w) (affine_mem e)) hσ, ?_, ?_⟩
    · simp [Equiv.Perm.mul_apply, hσ0, e, w]
    · change w (e z) = Pi.single origin (1 : R)
      rw [hez, hw]

  have normalize_pair (a b : I → R) (hab : a ≠ b) :
      ∃ g ∈ G, g a = 0 ∧ g b = Pi.single origin (1 : R) := by
    obtain ⟨g, hg, hg0, hgb⟩ := normalize (b - a) (sub_ne_zero.mpr hab.symm)
    let t := (AffineEquiv.vaddConst R a).symm
    refine ⟨g * t.toEquiv, G.mul_mem hg (affine_mem t), ?_, ?_⟩
    · change g (a - a) = 0
      simpa only [sub_self] using hg0
    · change g (b - a) = Pi.single origin (1 : R)
      exact hgb

  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hg, hga, hgb⟩ := normalize_pair a b hab
  obtain ⟨h, hh, hhc, hhd⟩ := normalize_pair c d hcd
  refine ⟨⟨h⁻¹ * g, G.mul_mem (G.inv_mem hh) hg⟩, ?_, ?_⟩
  · change h.symm (g a) = c
    rw [hga, ← hhc, h.symm_apply_apply]
  · change h.symm (g b) = d
    rw [hgb, ← hhd, h.symm_apply_apply]

end Toffoli
