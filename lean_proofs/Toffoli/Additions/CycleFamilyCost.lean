import Toffoli.Additions.CycleFamily
import Toffoli.Additions.CycleTransfersCost

namespace Toffoli

/-- One transposition for each cycle label after its anchor. -/
theorem cycleFamily_cost {K : Type*} [Field K] [DecidableEq K]
    (cycles : List (List K)) (f : K → K) :
    (cycleFamilyCircuit cycles f).cost =
      (cycles.map (fun labels => labels.length - 1)).sum := by
  -- Summing all gate costs is the same as summing the cost of each cycle.
  rw [cycleFamilyCircuit, Circuit.cost, List.map_flatMap,
    List.flatMap_def, List.sum_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro labels _
  change (cycleCircuit labels f).cost = labels.length - 1
  cases labels with
  | nil => rfl
  | cons a rest => exact cycleTransfers_cost a rest f

end Toffoli
