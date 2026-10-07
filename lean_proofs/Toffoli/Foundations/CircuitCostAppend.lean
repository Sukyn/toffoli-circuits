import Toffoli.Foundations.Basic

namespace Toffoli

/-- The cost of a concatenated gate list is the sum of its two costs. -/
theorem circuit_cost_append {K : Type*} [Field K] (c d : Circuit K) :
    (c ++ d).cost = c.cost + d.cost := by
  simp [Circuit.cost, List.map_append, List.sum_append]

end Toffoli
