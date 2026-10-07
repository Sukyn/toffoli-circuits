import Toffoli.Polarization.PolarizationScheduleModel

namespace Toffoli

/-- Removing power evaluations leaves exactly the signed coefficient states
of the Gray walk, including its starting and final states. -/
theorem polarization_schedule_walk {K : Type*} [CommRing K] {n : ℕ}
    (normalization : K) (word : GrayWord n) (flips : List (Fin n)) :
    let calls := polarizationSchedule (polarizationWalk normalization word flips)
    calls.scanl scheduleStep (fun i => polarizationSign (word i)) =
        (flips.scanl grayFlip word).map (fun word i => polarizationSign (word i)) ∧
      calls.foldl scheduleStep (fun i => polarizationSign (word i)) =
        fun i => polarizationSign ((flips.foldl grayFlip word) i) := by
  have hflip (word : GrayWord n) (i : Fin n) :
      scheduleStep (fun j => (polarizationSign (word j) : K))
        (i, -(2 * polarizationSign (word i))) =
        fun j => polarizationSign (grayFlip word i j) := by
    funext j
    by_cases h : j = i
    · subst j
      cases hs : word i <;> simp [scheduleStep, grayFlip, polarizationSign, hs] <;> ring
    · simp [scheduleStep, grayFlip, h]
  induction flips generalizing word with
  | nil => simp [polarizationSchedule, polarizationWalk]
  | cons i rest ih =>
    simpa [polarizationSchedule, polarizationWalk, List.scanl_cons, hflip] using
      ih (grayFlip word i)

end Toffoli
