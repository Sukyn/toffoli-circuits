import Toffoli.Foundations.CoordinateLiftModel

namespace Toffoli

/-- A lifted gate has the original two-wire action at the selected control;
every other control value is preserved, even when it is dirty workspace. -/
theorem coordinate_lift_gate {K : Type*} [Field K] {n : ℕ}
    (g : Gate K) (i : Fin n) (x : Controls K n) (t : K) :
    (g.lift i).eval (x, t) =
      (Function.update x i (g.eval (x i, t)).1, (g.eval (x i, t)).2) := by
  classical
  cases g with
  | affine a b ha =>
    apply Prod.ext
    · funext j
      by_cases h : j = i <;> subst_vars <;>
        simp [Gate.lift, MultiGate.eval, MultiGate.control, coordinateAffine,
          Gate.eval, smul_eq_mul, add_comm, *]
    · simp [Gate.lift, MultiGate.eval, MultiGate.increment, Gate.eval]
  | swap a b =>
    apply Prod.ext
    · funext j
      by_cases h : j = i <;> subst_vars <;>
        simp [Gate.lift, MultiGate.eval, MultiGate.control, Gate.eval, *]
    · simp [Gate.lift, MultiGate.eval, MultiGate.increment, Gate.eval]
  | sum coefficient =>
    simp [Gate.lift, MultiGate.eval, MultiGate.control, MultiGate.increment, Gate.eval]

end Toffoli
