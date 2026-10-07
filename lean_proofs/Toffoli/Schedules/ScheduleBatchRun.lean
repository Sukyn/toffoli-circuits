import Toffoli.Schedules.ScheduleModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Tuple.Basic

namespace Toffoli

/-- Calling every group once adds the supplied coefficient vector. This is
both the initial preparation and the final restoration of Gray order. -/
theorem schedule_batch_run {K : Type*} [AddCommMonoid K] {n : ℕ}
    (initial increments : Fin n → K) :
    (List.ofFn (fun i => (i, increments i))).foldl scheduleStep initial =
      initial + increments := by
  -- Each call adds one supported vector; summing all of them gives `increments`.
  have hstep : scheduleStep (K := K) (n := n) =
      fun state call => state + Pi.single call.1 call.2 := by
    funext state call
    simpa only [scheduleStep, Pi.single, add_zero, Function.update_eq_self] using
      Function.update_add state (0 : Fin n → K) call.1 (state call.1) call.2
  rw [hstep, ← List.foldl_map, List.foldl_eq_apply_foldr (init := (0 : Fin n → K))]
  simp [List.map_ofFn, ← List.sum_eq_foldr, List.sum_ofFn, Finset.univ_sum_single]

end Toffoli
