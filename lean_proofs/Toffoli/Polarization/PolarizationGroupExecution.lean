import Toffoli.Polarization.PolarizationExecutionModel

namespace Toffoli

/-- A list of scaled group calls adds its increments and leaves the target alone. -/
theorem polarization_groups_run {K : Type*} [CommRing K] {n : ℕ}
    (factors coefficients : Fin n → K) (indices : List (Fin n)) (x t : K) :
    runPolarization factors (indices.map (fun i => .group i (coefficients i))) (x, t) =
      (x + (indices.map (fun i => coefficients i * factors i)).sum, t) := by
  induction indices generalizing x with
  | nil => simp [runPolarization]
  | cons i rest ih =>
    simpa [runPolarization, PolarizationCall.eval, add_assoc] using
      ih (x + coefficients i * factors i)

end Toffoli
