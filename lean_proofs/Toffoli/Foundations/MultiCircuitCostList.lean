import Toffoli.Foundations.MultiControlModel

namespace Toffoli

/-- Flattening a list of circuits adds their individual transposition counts. -/
theorem multi_circuit_cost_list {K I : Type*} [Field K] {n : ℕ}
    (l : List I) (c : I → MultiCircuit K n) :
    MultiCircuit.cost (l.flatMap c) = (l.map (fun a => (c a).cost)).sum := by
  simp [MultiCircuit.cost, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]

end Toffoli
