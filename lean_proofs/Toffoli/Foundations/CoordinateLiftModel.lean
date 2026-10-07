import Toffoli.Foundations.MultiControlModel
import Mathlib.LinearAlgebra.Pi

namespace Toffoli
variable {K : Type*} [Field K] {n : ℕ}

/-- Scale and translate one coordinate, leaving all other controls alone. -/
noncomputable def coordinateAffine (i : Fin n) (a b : K) (ha : a ≠ 0) :
    Controls K n ≃ᵃ[K] Controls K n :=
  (LinearEquiv.piCongrRight (fun j : Fin n =>
    if j = i then LinearEquiv.smulOfNeZero K K a ha else LinearEquiv.refl K K)).toAffineEquiv.trans
      (AffineEquiv.constVAdd K (Controls K n) (Pi.single i b))

/-- Embed an existing two-wire gate on control `i` and the shared target. -/
noncomputable def Gate.lift (i : Fin n) : Gate K → MultiGate K n
  | .affine a b ha => .affine (coordinateAffine i a b ha)
  | .swap a b => .swap i a b
  | .sum coefficient => .sum i coefficient

noncomputable def Circuit.lift (c : Circuit K) (i : Fin n) : MultiCircuit K n :=
  c.map (Gate.lift i)

end Toffoli
