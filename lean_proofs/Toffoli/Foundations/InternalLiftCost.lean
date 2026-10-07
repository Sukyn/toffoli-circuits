import Toffoli.Foundations.InternalLiftModel

namespace Toffoli

/-- Moving the inner target to a control wire preserves the exact
transposition count: SUMs become free affine shears, and swaps stay swaps. -/
theorem internal_lift_cost {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i j : Fin n) (hij : i ≠ j) :
    (c.internalLift i j hij).cost = c.cost := by
  have hgate (g : Gate K) : (g.internalLift i j hij).cost = g.cost := by
    cases g <;> rfl
  simp only [Circuit.internalLift, MultiCircuit.cost, Circuit.cost,
    List.map_map, Function.comp_def, hgate]

end Toffoli
