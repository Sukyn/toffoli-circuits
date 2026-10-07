import Toffoli.Additions.OptimalPowerCycles
import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- A scaled square uses the paper's optimal cycle cost. Keeping the
one-control circuit available lets it be embedded at any later target. -/
theorem optimal_square_addition {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (μ : ZMod p) (hμ : μ ≠ 0) :
    ∃ c : Circuit (ZMod p), c.Realizes (fun x => μ * x ^ 2) ∧
      c.cost = optimalSquareCost p hp := by
  obtain ⟨⟨a, ha⟩, hcircuits, _, _⟩ :=
    optimal_power_cycles μ hμ 2 (by decide) (by omega)
  exact ⟨_, hcircuits a ha⟩

end Toffoli
