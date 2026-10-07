import Toffoli.Universality.OddRingUniversality
import Toffoli.Universality.FieldOneWire

namespace Toffoli

/-- Every finite field of odd cardinality at least five has universal
affine-plus-swap gates on every nonempty register. Odd cardinality excludes
characteristic two; characteristic three extensions are included. -/
theorem finite_field_universality {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hodd : Odd (Fintype.card K)) (hcard : 5 ≤ Fintype.card K) {n : ℕ} (hn : 0 < n) :
    affineSwapGroup K
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : K) 1)) = ⊤ := by
  cases Subsingleton.elim ‹DecidableEq K› (Classical.decEq K)
  classical
  exact odd_ring_universality hodd hcard field_one_wire hn

end Toffoli
