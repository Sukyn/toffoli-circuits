import Toffoli.Universality.AffineSwapModel
import Mathlib.Algebra.Group.Subgroup.Map

namespace Toffoli

/-- To lift a universal gate family into a larger register, it suffices to
lift each affine map and its distinguished gate. Subgroup closure then
supplies every permutation of the smaller register. -/
theorem affine_swap_lift_mem {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (τ : Equiv.Perm V)
    (huniversal : affineSwapGroup R τ = ⊤)
    (lift : Equiv.Perm V →* Equiv.Perm W) (G : Subgroup (Equiv.Perm W))
    (haffine : ∀ e : V ≃ᵃ[R] V, lift e.toEquiv ∈ G)
    (hgate : lift τ ∈ G) (σ : Equiv.Perm V) : lift σ ∈ G := by
  have h : affineSwapGroup R τ ≤ G.comap lift := by
    rw [affineSwapGroup, Subgroup.closure_le]
    rintro g (⟨e, rfl⟩ | rfl)
    · exact haffine e
    · exact hgate
  apply h
  rw [huniversal]
  exact Subgroup.mem_top σ

end Toffoli
