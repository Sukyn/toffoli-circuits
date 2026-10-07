import Toffoli.Schedules.ScheduleModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- The count of calls to a prefix is the sum of the individual group counts. -/
theorem schedule_prefix_counts {K : Type*} {n : ℕ} (j : ℕ)
    (calls : List (ScheduleCall K n)) :
    schedulePrefixCalls j calls =
      ∑ i ∈ Finset.range j, (calls.map (fun call => call.1.val)).count i := by
  induction calls with
  | nil => simp [schedulePrefixCalls]
  | cons call calls ih =>
    simp only [schedulePrefixCalls, List.countP_cons, List.map_cons, List.count_cons,
      Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    simp only [beq_iff_eq, Finset.sum_ite_eq, Finset.mem_range, decide_eq_true_eq]

end Toffoli
