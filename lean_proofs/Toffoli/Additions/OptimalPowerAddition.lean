import Toffoli.Additions.PowerCircuitFamilyAttains

namespace Toffoli

/-- Choose a least-order multiplier and retain its full cycle circuit for
every coefficient, including zero. The exact count is therefore independent
of the coefficient; this does not assert optimality for the zero function. -/
theorem optimal_power_addition {p : ℕ} [Fact p.Prime]
    (μ : ZMod p) (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    ∃ c : Circuit (ZMod p), c.Realizes (fun x => μ * x ^ d) ∧
      c.cost = (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound := by
  exact (power_circuit_family_attains μ d hd hbound).imp (fun _ h => h.2)

end Toffoli
