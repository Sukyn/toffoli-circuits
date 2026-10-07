import Toffoli.Polarization.PolarizationScheduleWalk
import Toffoli.Schedules.ScheduleBatchRun
import Toffoli.Schedules.GrayScan
import Toffoli.Schedules.GrayWordsComplete

namespace Toffoli

/-- The existing polarization circuit is an admissible coefficient schedule:
it prepares the first signs, visits every sign vector, and restores zero. -/
theorem polarization_schedule_correct {K : Type*} [CommRing K] {n : ℕ}
    (normalization : K) :
    let first : GrayWord n := fun _ => false
    let last := (grayFlips n).foldl grayFlip first
    let prepare := List.ofFn (fun i : Fin n => (i, (1 : K)))
    let traverse := polarizationSchedule (polarizationWalk normalization first (grayFlips n))
    let restore := List.ofFn (fun i : Fin n => (i, -(polarizationSign (last i) : K)))
    prepare.foldl scheduleStep 0 = (fun i => polarizationSign (first i)) ∧
      traverse.foldl scheduleStep (fun i => polarizationSign (first i)) =
        (fun i => polarizationSign (last i)) ∧
      restore.foldl scheduleStep
        (traverse.foldl scheduleStep (fun i => polarizationSign (first i))) = 0 ∧
      (∀ word : GrayWord n, (fun i => polarizationSign (word i)) ∈
        traverse.scanl scheduleStep (fun i => polarizationSign (first i))) ∧
      polarizationSchedule (polarizationCircuit normalization) = prepare ++ traverse ++ restore := by
  dsimp only
  obtain ⟨hscan, hrun⟩ := polarization_schedule_walk normalization (fun _ => false) (grayFlips n)
  refine ⟨?_, hrun, ?_, ?_, ?_⟩
  · simpa [polarizationSign] using schedule_batch_run (0 : Fin n → K) (fun _ => (1 : K))
  · rw [hrun, schedule_batch_run]
    ext i
    simp
  · intro word
    rw [hscan, gray_scan]
    exact List.mem_map.mpr ⟨word, mem_gray_words n word, rfl⟩
  · simp [polarizationCircuit, polarizationSchedule, List.ofFn_eq_map, List.filterMap_map]

end Toffoli
