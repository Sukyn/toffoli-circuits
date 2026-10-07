import Toffoli.Polarization.PolarizationGroupExecution
import Toffoli.Polarization.PolarizationWalkExecution
import Toffoli.Schedules.GraySum
import Toffoli.Schedules.GrayScan
import Mathlib.Algebra.BigOperators.Fin

namespace Toffoli

/-- The full trace restores the preparation wire and adds the signed numerator.
The group values can be arbitrary: no independence is needed for correctness. -/
theorem polarization_circuit_run {K : Type*} [CommRing K] {n : ℕ}
    (factors : Fin n → K) (normalization x t : K) :
    runPolarization factors (polarizationCircuit normalization) (x, t) =
      (x, t + normalization * ∑ word : GrayWord n,
        polarizationWeight word * (x + polarizationSum factors word) ^ (n + 1)) := by
  have hgroups (coefficients : Fin n → K) (u v : K) :
      runPolarization factors
        (List.ofFn (fun i => PolarizationCall.group i (coefficients i))) (u, v) =
        (u + ∑ i, coefficients i * factors i, v) := by
    rw [List.ofFn_eq_map, polarization_groups_run, ← List.ofFn_eq_map, Fin.sum_ofFn]
  let start : GrayWord n := fun _ => false
  let last := (grayFlips n).foldl grayFlip start
  have hstart : (∑ i, (1 : K) * factors i) = polarizationSum factors start := by
    simp [polarizationSum, polarizationSign, start]
  have hend : (∑ i, -polarizationSign (last i) * factors i) =
      -polarizationSum factors last := by
    simp [polarizationSum, Finset.sum_neg_distrib]
  have happend (cs ds : List (PolarizationCall K n)) (state : K × K) :
      runPolarization factors (cs ++ ds) state =
        runPolarization factors ds (runPolarization factors cs state) := List.foldl_append
  rw [polarizationCircuit, happend, happend]
  rw [hgroups (fun _ => 1) x t, hstart, polarization_walk_run, hgroups, hend]
  simp only [last, start, add_neg_cancel_right]
  rw [gray_scan, gray_sum]

end Toffoli
