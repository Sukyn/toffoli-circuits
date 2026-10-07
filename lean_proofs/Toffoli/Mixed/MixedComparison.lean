import Toffoli.Mixed.MixedDivideBound
import Toffoli.Mixed.MixedBorrowBound

namespace Toffoli

/-- Both baseline comparisons hold for every workspace budget in the
numerical mixed family. Primitive compilation is a separate obligation. -/
theorem mixed_comparison {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 0 < d) (b : ℕ) :
    mixedCount p hp d b ≤
      min (divideCount p d) (borrowCost (2 * optimalSquareCost p hp) d) := by
  exact le_min (mixed_divide_bound hp hd b) (mixed_borrow_bound hp hd b)

end Toffoli
