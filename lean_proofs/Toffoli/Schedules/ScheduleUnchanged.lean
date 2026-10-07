import Toffoli.Schedules.ScheduleModel

namespace Toffoli

/-- An uncalled group keeps its coefficient, even when all other calls use
arbitrary scalars. The contrapositive prices preparation and restoration. -/
theorem schedule_unchanged {K : Type*} [Add K] {n : ℕ}
    (calls : List (ScheduleCall K n)) (initial : Fin n → K) (i : Fin n)
    (hi : i ∉ calls.map Prod.fst) :
    (calls.foldl scheduleStep initial) i = initial i := by
  induction calls generalizing initial with
  | nil => rfl
  | cons call calls ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hi
    rw [List.foldl_cons, ih _ hi.2]
    exact Function.update_of_ne hi.1 _ _

end Toffoli
