import Toffoli.Foundations.InternalLiftModel
import Toffoli.Foundations.CoordinateLiftGate
import Toffoli.Foundations.CoordinateShearApply

namespace Toffoli

/-- An internal lift reproduces the original gate on the selected pair.
All other controls and the outer target are unchanged. -/
theorem internal_lift_gate {K : Type*} [Field K] {n : ℕ}
    (g : Gate K) (i j : Fin n) (hij : i ≠ j) (x : Controls K n) (t : K) :
    (g.internalLift i j hij).eval (x, t) =
      (Function.update (Function.update x i (g.eval (x i, x j)).1)
        j (g.eval (x i, x j)).2, t) := by
  classical
  cases g with
  | affine a b ha =>
    -- Moving the target leaves source-only gates unchanged.
    simpa [Gate.internalLift, Gate.lift, Gate.eval, Function.update_comm hij] using
      coordinate_lift_gate (.affine a b ha) i x t
  | swap a b =>
    simpa [Gate.internalLift, Gate.lift, Gate.eval, Function.update_comm hij] using
      coordinate_lift_gate (.swap a b) i x t
  | sum coefficient =>
    simp [Gate.internalLift, MultiGate.eval, MultiGate.control, MultiGate.increment,
      coordinate_shear_apply, Gate.eval]

end Toffoli
