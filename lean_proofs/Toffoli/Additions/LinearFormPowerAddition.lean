import Toffoli.Additions.LinearFormPreparation
import Toffoli.Additions.PowerAddition
import Toffoli.Foundations.CoordinateLiftRealizes
import Toffoli.Foundations.MultiCircuitConjugation

namespace Toffoli
open scoped BigOperators

/-- Compile a scaled power of a nonzero linear form by the paper's construction:
prepare the form on one wire, run the checked one-control power circuit there,
then undo the preparation. Every control is restored. -/
theorem linear_form_power_addition {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (μ : K) (b : Fin n → K) (hb : ∃ i, b i ≠ 0)
    (d : ℕ) (hd : d ≠ 0) (hbound : d < Nat.card K - 1) :
    ∃ c : MultiCircuit K n, c.Realizes (fun x => μ * (∑ i, b i * x i) ^ d) := by
  obtain ⟨i, hi⟩ := hb
  obtain ⟨e, he, _⟩ := linear_form_preparation b i hi
  obtain ⟨c, hc⟩ := power_addition μ d hd hbound
  refine ⟨[.affine e] ++ c.lift i ++ [.affine e.symm], ?_⟩
  simpa only [he] using multi_circuit_conjugation (c.lift i)
    (fun x => μ * x i ^ d) (coordinate_lift_realizes c _ hc i) e

end Toffoli
