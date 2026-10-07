import Toffoli.Additions.PowerCircuitFamilyLower
import Toffoli.Foundations.CoordinateLiftCost
import Toffoli.Foundations.InternalLiftCost

namespace Toffoli

/-- Embedding a power leaf on either kind of target preserves its lower bound. -/
theorem indexed_power_circuit_family_lower {p n : ℕ} [Fact p.Prime]
    {i : Fin n} {target : IndexedTarget n} {μ : ZMod p} {d : ℕ}
    {c : MultiCircuit (ZMod p) n}
    (member : IndexedPowerCircuitFamily i target μ d c) (hμ : μ ≠ 0)
    (hd : 0 < d) (hbound : d < p - 1) :
    (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound ≤ c.cost := by
  cases member with
  | external h =>
    rw [coordinate_lift_cost]
    exact power_circuit_family_lower h hμ hd hbound
  | internal j hij h =>
    rw [internal_lift_cost]
    exact power_circuit_family_lower h hμ hd hbound

end Toffoli
