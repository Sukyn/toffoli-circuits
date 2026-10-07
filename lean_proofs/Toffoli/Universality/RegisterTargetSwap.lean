import Toffoli.Universality.RegisterJoinModel
import Toffoli.Universality.AccumulatorPermutationModel
import Toffoli.Universality.CoordinatePermutationApply

namespace Toffoli
open scoped Classical

/-- The distinguished target swap is exactly the local swap on the first
wire when the accumulator state is written as a single register. -/
theorem register_target_swap {K : Type*} [CommRing K] (n : ℕ) :
    (registerJoin (K := K) n).symm.toEquiv.permCongr
      (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : K) 1)) =
      targetSwap (C := Controls K n) := by
  ext ⟨x, t⟩ : 1
  apply Prod.ext
  · funext j
    change coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : K) 1)
      (Fin.cons t x) j.succ = x j
    simp [coordinate_permutation_apply]
  · change coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : K) 1)
      (Fin.cons t x) 0 = Equiv.swap 0 1 t
    simp [coordinate_permutation_apply]

end Toffoli
