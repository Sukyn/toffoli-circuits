import Toffoli.Additions.PowerCircuitFamilyModel
import Toffoli.Additions.OptimalPowerCycles

namespace Toffoli

/-- Every admissible power leaf pays at least the least-order cycle cost.
The nonzero coefficient is essential: the zero function has cheaper choices. -/
theorem power_circuit_family_lower {p : ℕ} [Fact p.Prime]
    {μ : ZMod p} {d : ℕ} {c : Circuit (ZMod p)}
    (member : PowerCircuitFamily μ d c) (hμ : μ ≠ 0)
    (hd : 0 < d) (hbound : d < p - 1) :
    (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound ≤ c.cost := by
  obtain ⟨a, b, ha, hadm, rfl⟩ := member
  rw [(power_cycle_synthesis a b μ ha d hadm).2]
  exact (optimal_power_cycles μ hμ d hd hbound).2.2.1 a b ha hadm

end Toffoli
