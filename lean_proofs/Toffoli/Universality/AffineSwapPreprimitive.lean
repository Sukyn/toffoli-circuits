import Toffoli.Universality.AffineSwapTwoTransitive

namespace Toffoli

/-- Every group containing all affine maps acts primitively: its
two-transitivity rules out a nontrivial invariant partition. -/
theorem affine_swap_preprimitive {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (τ : Equiv.Perm V) :
    MulAction.IsPreprimitive (affineSwapGroup K τ) V :=
  MulAction.isPreprimitive_of_is_two_pretransitive
    (affine_swap_two_pretransitive (K := K) τ)

end Toffoli
