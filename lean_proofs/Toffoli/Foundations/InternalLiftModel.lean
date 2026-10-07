import Toffoli.Foundations.CoordinateLiftModel
import Toffoli.Foundations.CoordinateShearModel

namespace Toffoli
variable {K : Type*} [Field K] {n : ℕ}

/-- Place a two-wire gate entirely inside the control register. Its SUM
becomes an affine shear, so the outer circuit's target is never involved. -/
noncomputable def Gate.internalLift (i j : Fin n) (hij : i ≠ j) : Gate K → MultiGate K n
  | .affine a b ha => .affine (coordinateAffine i a b ha)
  | .swap a b => .swap i a b
  | .sum coefficient => .affine (coordinateShear i j coefficient hij)

noncomputable def Circuit.internalLift (c : Circuit K) (i j : Fin n) (hij : i ≠ j) :
    MultiCircuit K n := c.map (Gate.internalLift i j hij)

end Toffoli
