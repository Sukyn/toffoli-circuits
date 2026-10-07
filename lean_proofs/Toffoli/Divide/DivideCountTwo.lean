import Toffoli.Divide.DivideRecurrence
import Toffoli.Divide.DivideCountOne
import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- With two controls, the sole preparation group is a singleton SUM.
The attained minimum therefore consists of exactly two square additions. -/
theorem divide_count_two {p : ℕ} (hp : 5 ≤ p) :
    divideCount p 2 = 2 * optimalSquareCost p hp := by
  obtain ⟨c, hdegree, hcost⟩ := (divide_recurrence hp (show 2 ≤ 2 by decide)).1
  -- A positive composition of one has exactly one block, itself of size one.
  have hc : c = Composition.ones 1 :=
    Composition.eq_ones_iff_le_length.mpr (c.length_pos_of_pos (by decide))
  subst c
  simpa [divideStepCost, divide_count_one, optimalSquareCost, optimalSquareOrder]
    using hcost

end Toffoli
