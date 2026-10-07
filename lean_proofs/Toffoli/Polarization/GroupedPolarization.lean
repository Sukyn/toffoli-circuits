import Toffoli.Polarization.PolarizationCircuitExecution
import Toffoli.Polarization.PolarizationCircuitCalls
import Toffoli.Polarization.FischerPolarization
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Factorial

namespace Toffoli

/-- The paper's grouped construction: restore the first control, add the
product, and count the calls from that same executable trace. Here n=k-1,
so Lean index i corresponds to paper group i+1. Group and power calls are
the accumulator subcircuits chosen in the construction. -/
theorem grouped_polarization {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (n : ℕ) (hdegree : n + 1 ≤ p - 2) (factors : Fin n → ZMod p) (x t : ZMod p) :
    let calls := polarizationCircuit (n := n)
      (((2 : ZMod p) ^ n * ((n + 1).factorial : ZMod p))⁻¹)
    runPolarization factors calls (x, t) = (x, t + x * ∏ i, factors i) ∧
      polarizationPowerCalls calls = 2 ^ n ∧
      ∀ i : Fin n, (polarizationGroupCalls calls).count i = 2 + 2 ^ i.val := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have hfactorial : ((n + 1).factorial : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
    omega
  have hden := mul_ne_zero (pow_ne_zero n h2) hfactorial
  refine ⟨?_, polarization_circuit_calls _⟩
  rw [polarization_circuit_run, fischer_polarization h2]
  congr 1
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]

end Toffoli
