import Toffoli.Polarization.TwoSquareModel

namespace Toffoli

/-- The three shears are affine; the exact cost is that of the two squares. -/
theorem two_square_cost {K : Type*} [Field K] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (positive negative : MultiCircuit K n) :
    (twoSquareCircuit i j hij positive negative).cost = positive.cost + negative.cost := by
  simp [twoSquareCircuit, MultiCircuit.cost, MultiGate.cost]

end Toffoli
