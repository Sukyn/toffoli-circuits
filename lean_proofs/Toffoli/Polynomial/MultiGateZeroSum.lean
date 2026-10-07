import Toffoli.Foundations.MultiControlModel
import Toffoli.Polynomial.ControlCoordinateSum

namespace Toffoli

/-- A control gate contributes zero; a SUM contributes a multiple of one
coordinate, whose sum over the full control register is zero. -/
theorem multi_gate_zero_sum {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) {n : ℕ} (g : MultiGate K n) :
    (∑ x, g.increment x) = 0 := by
  cases g with
  | affine e => simp [MultiGate.increment]
  | swap i a b => simp [MultiGate.increment]
  | sum i coefficient =>
    simp only [MultiGate.increment, ← Finset.mul_sum, control_coordinate_sum hcard, mul_zero]

end Toffoli
