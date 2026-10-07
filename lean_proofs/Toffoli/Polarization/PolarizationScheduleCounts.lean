import Toffoli.Polarization.PolarizationScheduleModel
import Toffoli.Polarization.PolarizationCircuitCalls

namespace Toffoli

/-- The coefficient schedule retains the exact call counts of the existing
circuit. Hence its additive cost attains the schedule lower bound. -/
theorem polarization_schedule_counts {K : Type*} [CommRing K] {n : ℕ}
    (normalization : K) (i : Fin n) :
    ((polarizationSchedule (polarizationCircuit (n := n) normalization)).map
      (fun call => call.1.val)).count i.val = 2 + 2 ^ i.val := by
  have hmap (calls : List (PolarizationCall K n)) :
      (polarizationSchedule calls).map (fun call => call.1.val) =
        (polarizationGroupCalls calls).map Fin.val := by
    -- Both projections discard power calls and retain the same group index.
    simp only [polarizationSchedule, polarizationGroupCalls, List.map_filterMap]
    apply List.filterMap_congr
    intro call _
    cases call <;> rfl
  rw [hmap, List.count_map_of_injective _ _ Fin.val_injective]
  exact (polarization_circuit_calls normalization).2 i

end Toffoli
