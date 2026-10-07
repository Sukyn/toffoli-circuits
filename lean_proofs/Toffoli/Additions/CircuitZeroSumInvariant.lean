import Toffoli.Foundations.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Toffoli
open scoped BigOperators

/-- Start with any permutation of the control inputs and any target table.
Each gate preserves the sum of that table: control gates only relabel inputs,
and a SUM contributes a scalar multiple of the zero control sum. -/
theorem circuit_preserves_target_sum {K : Type*} [Field K] [Fintype K]
    (hzero : (∑ x : K, x) = 0) (c : Circuit K)
    (control : K ≃ K) (target : K → K) :
    (∑ x, (c.eval (control x, target x)).2) = ∑ x, target x := by
  classical
  induction c generalizing control target with
  | nil => rfl
  | cons gate rest ih =>
    cases gate with
    | affine a b ha =>
      simpa only [Circuit.eval, List.foldl_cons, Gate.eval, Equiv.trans_apply,
        Equiv.mulLeft₀_apply, Equiv.coe_addRight] using
        ih (control.trans ((Equiv.mulLeft₀ a ha).trans (Equiv.addRight b))) target
    | swap a b =>
      simpa only [Circuit.eval, List.foldl_cons, Gate.eval, Equiv.trans_apply] using
        ih (control.trans (Equiv.swap a b)) target
    | sum coefficient =>
      have hc : (∑ x, control x) = 0 := (control.sum_comp id).trans hzero
      simpa only [Circuit.eval, List.foldl_cons, Gate.eval] using
        (ih control (fun x => target x + coefficient * control x)).trans (by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc, mul_zero, add_zero])

end Toffoli
