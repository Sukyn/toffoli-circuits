import Toffoli.Foundations.CoordinateShearApply

namespace Toffoli

/-- A shear gate adds a scaled source value to one control and preserves the output. -/
theorem coordinate_shear_eval {K : Type*} [Field K] {n : ℕ}
    (source target : Fin n) (coefficient : K) (hne : source ≠ target)
    (x : Controls K n) (t : K) :
    MultiCircuit.eval [MultiGate.affine (coordinateShear source target coefficient hne)]
      (x, t) = (Function.update x target (x target + coefficient * x source), t) := by
  simp [MultiCircuit.eval, MultiGate.eval, MultiGate.control,
    MultiGate.increment, coordinate_shear_apply]

end Toffoli
