import Toffoli.Divide.DivideRecurrence
import Toffoli.Divide.DivideCountOne

namespace Toffoli

/-- In the polarization range, dividing is no more expensive than the direct
construction: choose singleton groups, whose preparations are free SUMs. -/
theorem divide_direct_bound {p d : ℕ} (hp : 5 ≤ p) (hd : 2 ≤ d)
    (hdegree : d ≤ p - 2) :
    divideCount p d ≤ 2 ^ (d - 1) * ((p - 1) - (p - 1) /
      leastAdmissibleOrder (p - 1) d (by omega) (by omega)) := by
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  -- The minimum is bounded by this particular choice of grouping.
  have hbound := (divide_recurrence hp hd).2 (Composition.ones (d - 1))
    (by simpa [hpred] using hdegree)
  -- Every block has size one, so all recursive preparation costs vanish.
  simpa [divideStepCost, divide_count_one, hpred] using hbound

end Toffoli
