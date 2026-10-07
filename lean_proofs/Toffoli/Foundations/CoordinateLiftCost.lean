import Toffoli.Foundations.CoordinateLiftModel

namespace Toffoli

/-- Embedding changes neither the number of gates nor their transposition cost. -/
theorem coordinate_lift_cost {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i : Fin n) : (c.lift i).cost = c.cost := by
  have hgate (g : Gate K) : (g.lift i).cost = g.cost := by
    cases g <;> rfl
  simp only [Circuit.lift, MultiCircuit.cost, Circuit.cost, List.map_map, Function.comp_def, hgate]

end Toffoli
