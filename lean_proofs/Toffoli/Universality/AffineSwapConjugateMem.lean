import Toffoli.Universality.AffineSwapModel
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.End

namespace Toffoli

/-- Transport membership, not just universality, through an affine change
of coordinates. Every affine generator stays affine under conjugation. -/
theorem affine_swap_conjugate_mem {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ᵃ[R] W) (τ g : Equiv.Perm V) (hg : g ∈ affineSwapGroup R τ) :
    e.toEquiv.permCongr g ∈ affineSwapGroup R (e.toEquiv.permCongr τ) := by
  have h : affineSwapGroup R τ ≤
      (affineSwapGroup R (e.toEquiv.permCongr τ)).comap
        e.toEquiv.permCongrHom.toMonoidHom := by
    rw [affineSwapGroup, Subgroup.closure_le]
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact Subgroup.subset_closure (Or.inl ⟨(e.symm.trans a).trans e, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)
  exact h hg

end Toffoli
