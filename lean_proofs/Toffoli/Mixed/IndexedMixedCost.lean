import Toffoli.Mixed.IndexedMixedFamily
import Toffoli.Foundations.ProductConstructionModel

namespace Toffoli

/-- Compile every mixed cost tree on any pool with its prescribed workspace.
The recursive branches use the exact child budgets from the recurrence;
execution, cost, and protection of excluded wires belong to one circuit. -/
theorem indexed_mixed_cost {p d b cost : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (tree : MixedCost p hp d b cost) :
    ProductConstruction (ZMod p) d b cost := by
  intro n controls pool hsubset hcard hpool target htarget μ
  exact (indexed_mixed_family hp tree controls pool hsubset hcard hpool target htarget μ).imp
    (fun _ h => h.2)

end Toffoli
