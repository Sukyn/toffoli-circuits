import Toffoli.Additions.PowerCircuitFamilyAttains
import Toffoli.Foundations.CoordinateLiftRealizes
import Toffoli.Foundations.CoordinateLiftCost
import Toffoli.Foundations.CoordinateLiftLocality
import Toffoli.Foundations.InternalLiftRealizes
import Toffoli.Foundations.InternalLiftCost
import Toffoli.Foundations.InternalLiftLocality

namespace Toffoli

/-- Compile an attaining power leaf, keeping its family derivation, behavior,
exact count, and protected-wire guarantee on the same primitive list. -/
theorem indexed_power_circuit_family_attains {p n : ℕ} [Fact p.Prime]
    (i : Fin n) (target : IndexedTarget n) (hti : target ≠ some i)
    (μ : ZMod p) (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    ∃ c : MultiCircuit (ZMod p) n, IndexedPowerCircuitFamily i target μ d c ∧
      (∀ x t, c.eval (x, t) = indexedTargetAdd target (μ * x i ^ d) (x, t)) ∧
      c.cost = (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound ∧
      c.AccumulatorLocal {i} target := by
  obtain ⟨c, member, hc, hcost⟩ := power_circuit_family_attains μ d hd hbound
  cases target with
  | none =>
    refine ⟨c.lift i, .external member, coordinate_lift_realizes c _ hc i,
      ?_, coordinate_lift_locality c i⟩
    rw [coordinate_lift_cost, hcost]
  | some j =>
    have hij : i ≠ j := by simpa [ne_comm] using hti
    refine ⟨c.internalLift i j hij, .internal j hij member,
      internal_lift_realizes c _ hc i j hij, ?_, internal_lift_locality c i j hij⟩
    rw [internal_lift_cost, hcost]

end Toffoli
