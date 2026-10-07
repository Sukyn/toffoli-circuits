import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.GroupTheory.Perm.Basic

/-! `lem:local-swap-conjugacy`, valid over any field. -/
namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The affine map taking 0 to a and 1 to b; distinct endpoints make it invertible. -/
noncomputable def affineRelabel (a b : K) (hab : a ≠ b) : K ≃ᵃ[K] K :=
  (LinearEquiv.smulOfNeZero K K (b - a) (sub_ne_zero.mpr hab.symm)).toAffineEquiv.trans
    (AffineEquiv.vaddConst K a)

/-- Conjugating the fixed swap by the affine relabelling exchanges any two labels.
Permutation multiplication composes from right to left. -/
theorem localSwap_conjugacy (a b : K) (hab : a ≠ b) :
    Equiv.swap a b =
      (affineRelabel a b hab).toEquiv * Equiv.swap 0 1 *
        (affineRelabel a b hab).toEquiv⁻¹ := by
  classical
  simpa [affineRelabel] using
    Equiv.swap_apply_apply (affineRelabel a b hab).toEquiv (0 : K) 1

end Toffoli
