import Toffoli.Universality.RingAffineSwapTwoTransitive

namespace Toffoli

/-- One-wire universality and affine maps rule out every nontrivial
invariant partition of the register, including over composite alphabets. -/
theorem ring_affine_swap_preprimitive {R I : Type*} [CommRing R]
    [Nontrivial R] [DecidableEq R] (origin : I)
    (hone : affineSwapGroup R (Equiv.swap (0 : R) 1) = ⊤) :
    MulAction.IsPreprimitive
      (affineSwapGroup R (coordinatePermutation origin (Equiv.swap (0 : R) 1)))
      (I → R) :=
  MulAction.isPreprimitive_of_is_two_pretransitive
    (ring_affine_swap_two_pretransitive origin hone)

end Toffoli
