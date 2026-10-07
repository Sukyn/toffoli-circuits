import Toffoli.Additions.IndexedPowerCircuitFamilyAttains

namespace Toffoli

/-- Lift the least-order power circuit without enlarging its source pool.
The same witness has the exact cycle count and uses the selected target
only as an accumulator, including when the coefficient is zero. -/
theorem indexed_power {p n : ℕ} [Fact p.Prime]
    (i : Fin n) (target : IndexedTarget n) (hti : target ≠ some i)
    (μ : ZMod p) (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) = indexedTargetAdd target (μ * x i ^ d) (x, t)) ∧
      c.cost = (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound ∧
      c.AccumulatorLocal {i} target := by
  exact (indexed_power_circuit_family_attains i target hti μ d hd hbound).imp
    (fun _ h => h.2)

end Toffoli
