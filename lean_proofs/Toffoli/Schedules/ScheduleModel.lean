import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Algebra.Group.Pi.Basic

namespace Toffoli

/-- A paid call adds an arbitrary scalar multiple of one chosen group.
Coefficients need not stay in {−1, 1}, and calls may repeat or add zero. -/
abbrev ScheduleCall (K : Type*) (n : ℕ) := Fin n × K

def scheduleStep {K : Type*} [Add K] {n : ℕ}
    (state : Fin n → K) (call : ScheduleCall K n) : Fin n → K :=
  Function.update state call.1 (state call.1 + call.2)

/-- The first j coordinates are the j most expensive groups. -/
def schedulePrefixCalls {K : Type*} {n : ℕ} (j : ℕ)
    (calls : List (ScheduleCall K n)) : ℕ :=
  calls.countP (fun call => decide (call.1.val < j))

end Toffoli
