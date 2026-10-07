import Toffoli.Universality.AffineSwapConjugateMem

namespace Toffoli

/-- An affine change of coordinates preserves universality. Each affine
generator remains affine after conjugation, and the distinguished gate is
conjugated by the same change of coordinates. -/
theorem affine_swap_transport {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ᵃ[R] W) (τ : Equiv.Perm V)
    (h : affineSwapGroup R τ = ⊤) :
    affineSwapGroup R (e.toEquiv.permCongr τ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  obtain ⟨g, rfl⟩ := e.toEquiv.permCongrHom.surjective σ
  apply affine_swap_conjugate_mem e τ g
  rw [h]
  exact Subgroup.mem_top g

end Toffoli
