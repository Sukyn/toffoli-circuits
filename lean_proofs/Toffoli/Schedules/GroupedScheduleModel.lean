import Toffoli.Polarization.PolarizationScheduleModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Toffoli

/-- A schedule is cut at its first and last evaluated signed sums. Before
the first evaluation it prepares `first`; between those evaluations it visits
every sign vector; after the last it restores zero. Any order of evaluations
admits these cuts. There is no restriction on the intervening coefficients,
repeated evaluations, or number of calls. -/
def ScheduleAdmissible {K : Type*} [CommRing K] {n : ℕ}
    (prepare traverse restore : List (ScheduleCall K n))
    (first last : GrayWord n) : Prop :=
  prepare.foldl scheduleStep 0 = (fun i => polarizationSign (first i)) ∧
    traverse.foldl scheduleStep (fun i => polarizationSign (first i)) =
      (fun i => polarizationSign (last i)) ∧
    restore.foldl scheduleStep
      (traverse.foldl scheduleStep (fun i => polarizationSign (first i))) = 0 ∧
    ∀ word : GrayWord n, (fun i => polarizationSign (word i)) ∈
      traverse.scanl scheduleStep (fun i => polarizationSign (first i))

/-- Additive preparation cost: the number of calls to each chosen group
multiplied by the transposition count of that group's subcircuit. -/
def scheduleCost {K : Type*} {n : ℕ} (cost : ℕ → ℕ)
    (calls : List (ScheduleCall K n)) : ℕ :=
  ∑ i ∈ Finset.range n, (calls.map (fun call => call.1.val)).count i * cost i

end Toffoli
