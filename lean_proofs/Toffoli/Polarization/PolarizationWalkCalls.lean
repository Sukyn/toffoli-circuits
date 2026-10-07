import Toffoli.Polarization.PolarizationExecutionModel

namespace Toffoli

/-- Every flip is one recorded group call, and every visited word is one power call. -/
theorem polarization_walk_calls {K : Type*} [CommRing K] {n : ℕ}
    (normalization : K) (word : GrayWord n) (flips : List (Fin n)) :
    polarizationGroupCalls (polarizationWalk normalization word flips) = flips ∧
    polarizationPowerCalls (polarizationWalk normalization word flips) = flips.length + 1 := by
  induction flips generalizing word with
  | nil => simp [polarizationWalk, polarizationGroupCalls, polarizationPowerCalls]
  | cons i rest ih =>
    obtain ⟨hg, hp⟩ := ih (grayFlip word i)
    simp [polarizationWalk, polarizationGroupCalls, polarizationPowerCalls] at hg hp ⊢
    exact ⟨hg, by omega⟩

end Toffoli
