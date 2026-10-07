import Toffoli.Universality.PrimeUniversality
import Toffoli.Universality.AffineSwapTransport
import Toffoli.Universality.RegisterTargetSwap

namespace Toffoli

/-- An accumulator with `n` controls is a register of `n + 1` wires.
Transport register universality to this presentation, including `n = 0`. -/
theorem prime_accumulator_universality {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) :
    affineSwapGroup (ZMod p) (targetSwap (C := Controls (ZMod p) n) (K := ZMod p)) = ⊤ := by
  classical
  let e := (registerJoin (K := ZMod p) n).symm
  have hgate : e.toEquiv.permCongr
      (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : ZMod p) 1)) =
      targetSwap (C := Controls (ZMod p) n) (K := ZMod p) := by
    convert register_target_swap (K := ZMod p) n using 2
    ext x j
    by_cases h0 : x j = 0 <;> by_cases h1 : x j = 1 <;>
      simp [coordinate_permutation_apply, @Equiv.swap_apply_def, h0, h1]
  simpa only [hgate] using affine_swap_transport e
    (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : ZMod p) 1))
    (prime_universality hp (Nat.succ_pos n))

end Toffoli
