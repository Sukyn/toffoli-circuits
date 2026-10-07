import Toffoli.Foundations.AccumulatorLocalityModel

namespace Toffoli

/-- Enlarging the allowed pool preserves locality. Newly allowed wires are
unchanged, so their outputs depend only on their own input values. -/
theorem affine_local_mono {K : Type*} [Field K] {n : ℕ}
    {small large : Finset (Fin n)} {e : Controls K n ≃ᵃ[K] Controls K n}
    (h : AffineLocal small e) (hsub : small ⊆ large) : AffineLocal large e := by
  constructor
  · intro x i hi
    exact h.outside x i (fun hismall => hi (hsub hismall))
  · intro x y hxy i hi
    by_cases hismall : i ∈ small
    · exact h.depends x y (fun j hj => hxy j (hsub hj)) i hismall
    · rw [h.outside x i hismall, h.outside y i hismall]
      exact hxy i hi

end Toffoli
