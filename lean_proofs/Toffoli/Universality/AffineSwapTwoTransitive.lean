import Toffoli.Universality.AffineSwapModel
import Toffoli.Universality.LinearEquivBetweenNonzero
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace Toffoli

/-- Affine maps already move any ordered pair of distinct points to any
other. Translate the first point to zero, map the nonzero displacement
linearly, then translate to the desired first point. -/
theorem affine_swap_two_pretransitive {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (τ : Equiv.Perm V) :
    MulAction.IsMultiplyPretransitive (affineSwapGroup K τ) V 2 := by
  classical
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨e, he⟩ := linear_equiv_between_nonzero (K := K)
    (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hcd.symm)
  let f := AffineEquiv.ofLinearEquiv e a c
  have hf : f.toEquiv ∈ affineSwapGroup K τ :=
    Subgroup.subset_closure (Or.inl ⟨f, rfl⟩)
  refine ⟨⟨f.toEquiv, hf⟩, ?_, ?_⟩
  · change f a = c
    simp [f]
  · change f b = d
    simpa [f] using congrArg (fun v => v + c) he

end Toffoli
