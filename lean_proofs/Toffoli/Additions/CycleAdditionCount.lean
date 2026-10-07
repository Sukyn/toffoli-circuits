import Toffoli.Additions.CycleAddition
import Toffoli.Additions.CycleFamilyCount

namespace Toffoli
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Counting singleton cycles as well, the canonical construction uses exactly
card K minus the number of cycles. Affine restoration adds no transpositions. -/
theorem cycle_addition_count (a b : K) (ha : a ≠ 0) (f : K → K) :
    (cycleSynthesis a b ha (permutationCycleLists (affineControl a b ha)) f).cost =
      Fintype.card K - (permutationCycleLists (affineControl a b ha)).length := by
  obtain ⟨hn, hcover, _, hne, _⟩ :=
    Classical.choose_spec (exists_cycle_listing (affineControl a b ha))
  rw [cycleSynthesis, circuit_cost_append]
  -- The affine restoration contributes no swaps.
  change (cycleFamilyCircuit _ f).cost + 0 = _
  rw [add_zero]
  exact cycleFamily_count _ f hn hcover hne

end Toffoli
