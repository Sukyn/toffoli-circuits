import Toffoli.Additions.CircuitZeroSumField
import Toffoli.Additions.CircuitZeroSumInvariant

namespace Toffoli
open scoped BigOperators

/-- Necessity for one control in the paper's accumulator gate model.
Starting every target at zero, the final target table is `f`; the invariant
therefore forces its sum to vanish. This does not address multiple controls. -/
theorem one_control_zero_sum_necessary {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) (c : Circuit K) (f : K → K)
    (hrealizes : c.Realizes f) : (∑ x, f x) = 0 := by
  unfold Circuit.Realizes at hrealizes
  have invariant := circuit_preserves_target_sum (finite_field_sum_id hcard)
    c (Equiv.refl K) (fun _ => 0)
  simpa only [Equiv.refl_apply, hrealizes, zero_add, Finset.sum_const_zero] using invariant

end Toffoli
