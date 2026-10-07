import Toffoli.Schedules.GroupedScheduleModel
import Toffoli.Schedules.GroupedScheduleStep
import Toffoli.Schedules.ScheduleCostBound
import Toffoli.Polarization.PolarizationScheduleCorrect
import Toffoli.Polarization.PolarizationScheduleCounts

namespace Toffoli

/-- Reflected Gray order attains the least additive preparation cost among
all scalar-update schedules. Index zero is the most expensive group, so
the paper's coefficient 2+2^(i−1) becomes 2+2^i here. The witness is extracted
from the existing polarization circuit, including preparation/restoration. -/
theorem grouped_schedule {K : Type*} [CommRing K] [Nontrivial K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {n : ℕ} (normalization : K)
    (cost : ℕ → ℕ) (hcost : ∀ i, i + 1 < n → cost (i + 1) ≤ cost i) :
    (∃ prepare traverse restore first last,
      polarizationSchedule (polarizationCircuit (n := n) normalization) =
        prepare ++ traverse ++ restore ∧
      ScheduleAdmissible prepare traverse restore first last) ∧
    scheduleCost cost (polarizationSchedule (polarizationCircuit (n := n) normalization)) =
      (∑ i ∈ Finset.range n, (2 + 2 ^ i) * cost i) ∧
    ∀ (prepare traverse restore : List (ScheduleCall K n)) (first last : GrayWord n),
      ScheduleAdmissible prepare traverse restore first last →
      (∑ i ∈ Finset.range n, (2 + 2 ^ i) * cost i) ≤
        scheduleCost cost (prepare ++ traverse ++ restore) := by
  obtain ⟨hp, ht, hr, hv, heq⟩ := polarization_schedule_correct (n := n) normalization
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨_, _, _, _, _, heq, hp, ht, hr, hv⟩
  · apply Finset.sum_congr rfl
    intro i hi
    rw [polarization_schedule_counts normalization ⟨i, Finset.mem_range.mp hi⟩]
  · intro prepare traverse restore first last hvalid
    obtain ⟨hp, ht, hr, hv⟩ := hvalid
    exact schedule_cost_bound h2 prepare traverse restore first last hp ht hr hv cost hcost

end Toffoli
