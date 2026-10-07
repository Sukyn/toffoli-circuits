import Toffoli.Additions.PowerCircuitFamilyModel
import Toffoli.Additions.OptimalPowerCycles

namespace Toffoli

/-- A least-order multiplier supplies a family member at the stated count.
The construction also works for zero coefficients, retaining its full list. -/
theorem power_circuit_family_attains {p : ℕ} [Fact p.Prime]
    (μ : ZMod p) (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    ∃ c : Circuit (ZMod p), PowerCircuitFamily μ d c ∧
      c.Realizes (fun x => μ * x ^ d) ∧
      c.cost = (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound := by
  classical
  obtain ⟨⟨a, horder⟩, _, _, _⟩ :=
    optimal_power_cycles (1 : ZMod p) one_ne_zero d hd hbound
  have hnot : ¬orderOf a ∣ d := by
    rw [horder]
    exact (least_admissible_order_spec (p - 1) d hd hbound).1.2.2
  have heq : affineControl (a : ZMod p) 0 a.ne_zero =
      Equiv.mulLeft₀ (a : ZMod p) a.ne_zero := by
    ext x
    simp [affineControl]
  have hadm : PowerCycleAdmissible (a : ZMod p) 0 μ a.ne_zero d := by
    intro C hC
    exact power_cycles_by_order a μ d hnot C (by simpa only [heq] using hC)
  obtain ⟨hrun, hcost⟩ := power_cycle_synthesis (a : ZMod p) 0 μ a.ne_zero d hadm
  refine ⟨powerCycleCircuit (a : ZMod p) 0 μ a.ne_zero d,
    ⟨a, 0, a.ne_zero, hadm, rfl⟩, hrun, ?_⟩
  rw [hcost, multiplier_cycle_count, ZMod.card, horder]

end Toffoli
