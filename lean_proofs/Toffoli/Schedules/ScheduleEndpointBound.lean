import Toffoli.Schedules.ScheduleUnchanged
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace Toffoli

/-- Changing every coefficient in the first j groups takes at least j calls.
This applies both from zero to a sign vector and from a sign vector to zero. -/
theorem schedule_endpoint_bound {K : Type*} [Add K] {n j : ℕ}
    (hj : j ≤ n) (calls : List (ScheduleCall K n)) (initial : Fin n → K)
    (hchanged : ∀ i : Fin j, (calls.foldl scheduleStep initial) (Fin.castLE hj i) ≠
      initial (Fin.castLE hj i)) :
    j ≤ schedulePrefixCalls j calls := by
  classical
  let used := ((calls.filter (fun call => decide (call.1.val < j))).map Prod.fst).toFinset
  have hsubset : Finset.univ.image (Fin.castLE hj) ⊆ used := by
    intro i hi
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    have hmem : Fin.castLE hj i ∈ calls.map Prod.fst := by
      by_contra h
      exact hchanged i (schedule_unchanged calls initial _ h)
    obtain ⟨call, hcall, heq⟩ := List.mem_map.mp hmem
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨call, List.mem_filter.mpr ⟨hcall, ?_⟩, heq⟩
    simp [heq]
  have hcard := Finset.card_le_card hsubset
  have hlength := List.toFinset_card_le
    ((calls.filter (fun call => decide (call.1.val < j))).map Prod.fst)
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective hj)] at hcard
  simpa [used, schedulePrefixCalls, List.countP_eq_length_filter] using
    hcard.trans hlength

end Toffoli
