import Toffoli.Schedules.ScheduleModel
import Toffoli.Polarization.PolarizationExecutionModel

namespace Toffoli

/-- Keep the group updates of the existing circuit. Power calls evaluate
the accumulator but do not change its coefficient vector. -/
def polarizationSchedule {K : Type*} {n : ℕ}
    (calls : List (PolarizationCall K n)) : List (ScheduleCall K n) :=
  calls.filterMap (fun call => match call with
    | .group i a => some (i, a)
    | .power _ => none)

end Toffoli
