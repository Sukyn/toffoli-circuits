import Toffoli.Schedules.ScheduleProjectionBound
import Toffoli.Polarization.PolarizationSignInjective
import Mathlib.Data.Fintype.BigOperators

namespace Toffoli

/-- Visiting every signed coefficient vector requires at least 2^j−1 calls
to its first j coordinates. Intermediate coefficients may be arbitrary. -/
theorem schedule_traversal_bound {K : Type*} [CommRing K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {n j : ℕ} (hj : j ≤ n)
    (calls : List (ScheduleCall K n)) (initial : Fin n → K)
    (hvisit : ∀ word : Fin n → Bool,
      (fun i => polarizationSign (word i)) ∈ calls.scanl scheduleStep initial) :
    2 ^ j - 1 ≤ schedulePrefixCalls j calls := by
  let project := fun state : Fin n → K => state ∘ Fin.castLE hj
  let signs := fun word : Fin j → Bool => fun i => (polarizationSign (word i) : K)
  have hinjective : Function.Injective signs :=
    (polarization_sign_injective h2).comp_left
  have hsubset : Finset.univ.image signs ⊆
      ((calls.scanl scheduleStep initial).map project).toFinset := by
    intro state hstate
    obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hstate
    -- Every prefix word extends to a full word, which the schedule visits.
    obtain ⟨extended, hextended⟩ := (Fin.castLE_injective hj).surjective_comp_right word
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨fun i => polarizationSign (extended i), hvisit extended, ?_⟩
    exact congrArg (fun word => fun i => (polarizationSign (word i) : K)) hextended
  apply Nat.sub_le_iff_le_add.mpr
  calc
    2 ^ j = (Finset.univ.image signs).card := by
      rw [Finset.card_image_of_injective _ hinjective]
      simp
    _ ≤ ((calls.scanl scheduleStep initial).map project).toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ schedulePrefixCalls j calls + 1 := schedule_projection_bound hj calls initial

end Toffoli
