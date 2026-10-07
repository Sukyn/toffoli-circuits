import Toffoli.Foundations.MultiControlModel
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Transvection.Basic

namespace Toffoli

/-- A scaled SUM between two distinct controls is an affine control gate.
Mathlib's transvection supplies its inverse by negating the coefficient. -/
noncomputable def coordinateShear {K : Type*} [Field K] {n : ℕ}
    (source target : Fin n) (coefficient : K) (hne : source ≠ target) :
    Controls K n ≃ᵃ[K] Controls K n :=
  (LinearEquiv.transvection
    (f := (LinearMap.proj source : Controls K n →ₗ[K] K))
    (v := Pi.single target coefficient) (by simp [hne.symm])).toAffineEquiv

end Toffoli
