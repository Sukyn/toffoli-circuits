import Toffoli.Schedules.ScheduleModel
import Toffoli.Schedules.ObservedScanBound
import Mathlib.Data.Fintype.Basic

namespace Toffoli

/-- Projecting any scalar-update trace onto j groups gives at most one more
distinct coefficient vector than the number of calls to those groups. -/
theorem schedule_projection_bound {K : Type*} [Add K] [DecidableEq K] {n j : ℕ}
    (hj : j ≤ n) (calls : List (ScheduleCall K n)) (initial : Fin n → K) :
    ((calls.scanl scheduleStep initial).map (fun state => state ∘ Fin.castLE hj)).toFinset.card ≤
      schedulePrefixCalls j calls + 1 := by
  apply observed_scan_bound
  intro state call hirrelevant
  funext i
  have hcall : j ≤ call.1.val := Nat.le_of_not_gt (of_decide_eq_false hirrelevant)
  have hi : Fin.castLE hj i ≠ call.1 :=
    Fin.ne_of_val_ne (ne_of_lt (i.isLt.trans_le hcall))
  exact Function.update_of_ne hi _ _

end Toffoli
