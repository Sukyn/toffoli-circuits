import Toffoli.Additions.OptimalSquareAddition
import Toffoli.Polarization.TwoSquareInternal
import Toffoli.Polarization.TwoSquareCost
import Toffoli.Foundations.InternalLiftRealizes
import Toffoli.Foundations.InternalLiftCost

namespace Toffoli

/-- A primitive Toffoli may update a control used as temporary workspace.
Its two input controls, all other controls, and the final target are
unchanged. Its cost is the same C₂ as a Toffoli on the final target. -/
theorem scaled_toffoli_internal {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (μ : ZMod p) (hμ : μ ≠ 0) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) = (Function.update x k (x k + μ * x i * x j), t)) ∧
      c.cost = 2 * optimalSquareCost p hp := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨positive, hpositive, hpCost⟩ :=
    optimal_square_addition hp (μ / 4) (div_ne_zero hμ h4)
  obtain ⟨negative, hnegative, hnCost⟩ :=
    optimal_square_addition hp (-(μ / 4)) (neg_ne_zero.mpr (div_ne_zero hμ h4))
  refine ⟨twoSquareCircuit i j hij
    (positive.internalLift i k hik) (negative.internalLift i k hik), ?_, ?_⟩
  · apply two_square_internal i j k hij hik hjk μ h4
    · exact internal_lift_realizes positive _ hpositive i k hik
    · intro x t
      simpa only [neg_mul, sub_eq_add_neg] using
        internal_lift_realizes negative _ hnegative i k hik x t
  · rw [two_square_cost, internal_lift_cost, internal_lift_cost, hpCost, hnCost]
    omega

end Toffoli
