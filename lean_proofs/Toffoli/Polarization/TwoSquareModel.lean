import Toffoli.Foundations.CoordinateShearApply

namespace Toffoli

/-- Prepare x_i+x_j, then x_i-x_j, and finally restore x_i.
The supplied circuits add the positive and negative scaled squares.
There are three preparations, exactly as in the paper's two-square circuit. -/
noncomputable def twoSquareCircuit {K : Type*} [Field K] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (positive negative : MultiCircuit K n) :
    MultiCircuit K n :=
  [.affine (coordinateShear j i 1 hij.symm)] ++ positive ++
    [.affine (coordinateShear j i (-2) hij.symm)] ++ negative ++
    [.affine (coordinateShear j i 1 hij.symm)]

end Toffoli
