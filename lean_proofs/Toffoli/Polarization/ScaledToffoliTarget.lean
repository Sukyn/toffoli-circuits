import Toffoli.Additions.OptimalSquareAddition
import Toffoli.Polarization.TwoSquareTarget
import Toffoli.Polarization.TwoSquareCost
import Toffoli.Foundations.CoordinateLiftRealizes
import Toffoli.Foundations.CoordinateLiftCost

namespace Toffoli

/-- Compile a nonzero scaled Toffoli into the two optimal square circuits.
The three affine preparations restore every control, and the actual gate
list has exactly C₂ = 2 * optimalSquareCost transpositions. -/
theorem scaled_toffoli_target {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (i j : Fin n) (hij : i ≠ j) (μ : ZMod p) (hμ : μ ≠ 0) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * x i * x j) ∧ c.cost = 2 * optimalSquareCost p hp := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨positive, hpositive, hpCost⟩ :=
    optimal_square_addition hp (μ / 4) (div_ne_zero hμ h4)
  obtain ⟨negative, hnegative, hnCost⟩ :=
    optimal_square_addition hp (-(μ / 4)) (neg_ne_zero.mpr (div_ne_zero hμ h4))
  refine ⟨twoSquareCircuit i j hij (positive.lift i) (negative.lift i), ?_, ?_⟩
  · exact two_square_target i j hij μ h4 _ _
      (coordinate_lift_realizes positive _ hpositive i)
      (coordinate_lift_realizes negative _ hnegative i)
  · rw [two_square_cost, coordinate_lift_cost, coordinate_lift_cost, hpCost, hnCost]
    omega

end Toffoli
