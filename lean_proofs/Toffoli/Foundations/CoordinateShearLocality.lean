import Toffoli.Foundations.AccumulatorLocalityModel
import Toffoli.Foundations.CoordinateShearApply

namespace Toffoli

/-- A shear changes only its target and reads only its source and target.
Both wires are therefore included in its control-affine locality pool. -/
theorem coordinate_shear_locality {K : Type*} [Field K] {n : ℕ}
    (source target : Fin n) (coefficient : K) (hne : source ≠ target) :
    AffineLocal {source, target} (coordinateShear source target coefficient hne) := by
  constructor
  · intro x i hi
    have hitarget : i ≠ target := fun hit => hi (by simp [hit])
    rw [coordinate_shear_apply, Function.update_of_ne hitarget]
  · intro x y hxy i hi
    have hsource : x source = y source := hxy source (by simp)
    have htarget : x target = y target := hxy target (by simp)
    simp only [coordinate_shear_apply, Function.update_apply,
      hsource, htarget, hxy i hi]

end Toffoli
