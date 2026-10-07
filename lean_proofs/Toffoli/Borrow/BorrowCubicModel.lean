import Toffoli.Foundations.CoordinateShearApply

namespace Toffoli

/-- Borrow's three-control trace, with `i` serving as temporary workspace.
The internal calls move `y` through `y + x_i*x_j`, `y - x_i*x_j`, and
back to its initial value. Each pair of target calls adds a scaled square
of the current `y`, cancelling the unknown value borrowed from `i`. -/
noncomputable def borrowCubicCircuit {K : Type*} [Field K] {n : ℕ}
    (i y : Fin n) (hiy : i ≠ y)
    (prepare middle positive negative : MultiCircuit K n) : MultiCircuit K n :=
  prepare ++ [.affine (coordinateShear y i 1 hiy.symm)] ++ positive ++
    [.affine (coordinateShear y i (-1) hiy.symm)] ++ negative ++ middle ++
    [.affine (coordinateShear y i 1 hiy.symm)] ++ negative ++
    [.affine (coordinateShear y i (-1) hiy.symm)] ++ positive ++ prepare

end Toffoli
