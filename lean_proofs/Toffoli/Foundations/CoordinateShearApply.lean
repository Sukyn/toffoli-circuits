import Toffoli.Foundations.CoordinateShearModel

namespace Toffoli

/-- The shear updates only its target control. Its source and all other
controls, including any dirty workspace, keep their previous values. -/
theorem coordinate_shear_apply {K : Type*} [Field K] {n : ℕ}
    (source target : Fin n) (coefficient : K) (hne : source ≠ target)
    (x : Controls K n) :
    coordinateShear source target coefficient hne x =
      Function.update x target (x target + coefficient * x source) := by
  funext i
  by_cases h : i = target <;> subst_vars <;>
    simp [coordinateShear, LinearMap.transvection.apply, smul_eq_mul, mul_comm, *]

end Toffoli
