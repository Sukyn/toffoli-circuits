import Toffoli.Additions.TranslationCycle
import Toffoli.Additions.TranslationCycleListing

namespace Toffoli

/-- A nonzero translation has one cycle, hence the cycle algorithm uses p-1
transpositions. This count includes the final affine restoration. -/
theorem translation_cycle_count {p : ℕ} [Fact p.Prime]
    (b : ZMod p) (hb : b ≠ 0) :
    affineCycleCost 1 b one_ne_zero = p - 1 := by
  unfold affineCycleCost
  rw [cycle_listing_length_one _ (translation_cycle b hb), ZMod.card]

end Toffoli
