import Toffoli.Additions.OneControlZeroSum
import Toffoli.Additions.OneControlZeroSumNecessary

namespace Toffoli
open scoped BigOperators

/-- Over a finite field with more than two elements, a one-control addition
is realizable exactly when its increment sums to zero. -/
theorem one_control_zero_sum_iff {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) (f : K → K) :
    (∃ c : Circuit K, c.Realizes f) ↔ (∑ x, f x) = 0 := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    exact one_control_zero_sum_necessary hcard c f hc
  · intro hzero
    exact ⟨directTransferCircuit f, one_control_zero_sum f hzero⟩

end Toffoli
