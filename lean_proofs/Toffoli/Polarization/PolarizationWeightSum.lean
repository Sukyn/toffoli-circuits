import Toffoli.Polarization.PolarizationExecutionModel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- Charge a preparation to its group and a power addition to the power cost.
The coefficient does not affect the assigned price. -/
def PolarizationCall.weight {K : Type*} {m : ℕ} (q : Fin m → ℕ) (r : ℕ) :
    PolarizationCall K m → ℕ
  | .group i _ => q i
  | .power _ => r

/-- Add the prices of a trace by counting the occurrences of each kind of call.
This identity depends only on the trace, not on its circuit implementations. -/
theorem polarization_weight_sum {K : Type*} {m : ℕ}
    (calls : List (PolarizationCall K m)) (q : Fin m → ℕ) (r : ℕ) :
    (calls.map (PolarizationCall.weight q r)).sum = polarizationPowerCalls calls * r +
      ∑ i : Fin m, (polarizationGroupCalls calls).count i * q i := by
  classical
  induction calls with
  | nil => simp [polarizationPowerCalls, polarizationGroupCalls]
  | cons call calls ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases call <;>
      simp [PolarizationCall.weight, polarizationPowerCalls, polarizationGroupCalls,
        List.count_cons, add_mul, Finset.sum_add_distrib, ite_mul,
        add_assoc, add_left_comm, add_comm]

end Toffoli
