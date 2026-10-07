import Toffoli.Polynomial.MultiCircuitZeroSumInvariant

namespace Toffoli

/-- The necessary direction of the paper's accumulator characterization for
any number of controls. Starting all targets at zero makes the final target
table equal to the requested function, so its total sum must vanish. -/
theorem multi_control_zero_sum_necessary {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) {n : ℕ} (c : MultiCircuit K n)
    (f : Controls K n → K) (hrealizes : c.Realizes f) : (∑ x, f x) = 0 := by
  unfold MultiCircuit.Realizes at hrealizes
  have h := multi_circuit_preserves_target_sum hcard c (Equiv.refl _) (fun _ => 0)
  simpa only [Equiv.refl_apply, hrealizes, zero_add, Finset.sum_const_zero] using h

end Toffoli
