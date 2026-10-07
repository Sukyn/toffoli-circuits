import Toffoli.Schedules.GroupedScheduleAdmissible
import Mathlib.Algebra.Group.Pi.Lemmas

namespace Toffoli
open scoped BigOperators

/-- Updating one coefficient adds exactly the chosen scaled group product
to the register function. This identifies coefficient traces with the calls
allowed in the paper's preparation schedules. -/
theorem grouped_schedule_step {K W : Type*} [CommSemiring K] {n : ℕ}
    (groups : Fin n → Finset W) (base : (W → K) → K) (state : Fin n → K)
    (i : Fin n) (a : K) (x : W → K) :
    groupScheduleValue groups base (scheduleStep state (i, a)) x =
      groupScheduleValue groups base state x + a * ∏ j ∈ groups i, x j := by
  -- The coefficient vector changes by a single supported increment.
  have hstep : scheduleStep state (i, a) = state + Pi.single i a := by
    simpa only [scheduleStep, Pi.single, add_zero, Function.update_eq_self] using
      Function.update_add state (0 : Fin n → K) i (state i) a
  simp [groupScheduleValue, hstep, add_mul, Finset.sum_add_distrib,
    Pi.single_apply, ite_mul, add_assoc]

end Toffoli
