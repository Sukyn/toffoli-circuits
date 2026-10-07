import Toffoli.Additions.MultiplierCycleListCount
import Toffoli.Additions.PowerCycleModel

namespace Toffoli

/-- The canonical cycle circuit costs one fewer than the size of each
nonzero cycle. The singleton zero cycle contributes nothing. -/
theorem multiplier_cycle_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (a : Kˣ) :
    affineCycleCost (a : K) 0 a.ne_zero =
      (Fintype.card K - 1) - (Fintype.card K - 1) / orderOf a := by
  let cycles := permutationCycleLists (affineControl (a : K) 0 a.ne_zero)
  obtain ⟨hn, hcover, _, hne, hc⟩ :=
    Classical.choose_spec (exists_cycle_listing (affineControl (a : K) 0 a.ne_zero))
  have hcount := multiplier_cycle_list_count a cycles hn hcover hne
    (by
      intro labels hl
      simpa [affineControl] using hc labels hl)
  change Fintype.card K - cycles.length = _
  rw [hcount]
  omega

end Toffoli
