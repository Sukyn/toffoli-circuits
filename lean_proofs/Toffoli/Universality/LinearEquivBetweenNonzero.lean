import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Toffoli

/-- An invertible linear map can send any nonzero vector to any other.
If the vectors are proportional, rescale; otherwise include them in a
basis and exchange the corresponding basis vectors. -/
theorem linear_equiv_between_nonzero {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  classical
  by_cases h : ∃ a : K, a • x = y
  · obtain ⟨a, ha⟩ := h
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hy (by simpa using ha.symm)
    exact ⟨LinearEquiv.smulOfNeZero K V a ha0, ha⟩
  · have hxy := linearIndepOn_id_pair hx (not_exists.mp h)
    let b := Module.Basis.extend hxy
    let ix : hxy.extend (Set.subset_univ {x, y}) :=
      ⟨x, hxy.subset_extend _ (by simp)⟩
    let iy : hxy.extend (Set.subset_univ {x, y}) :=
      ⟨y, hxy.subset_extend _ (by simp)⟩
    have hbx : b ix = x := Module.Basis.extend_apply_self _ _
    have hby : b iy = y := Module.Basis.extend_apply_self _ _
    refine ⟨b.equiv b (Equiv.swap ix iy), ?_⟩
    calc
      (b.equiv b (Equiv.swap ix iy)) x =
          (b.equiv b (Equiv.swap ix iy)) (b ix) :=
        congrArg (b.equiv b (Equiv.swap ix iy)) hbx.symm
      _ = b iy := by simp only [Module.Basis.equiv_apply, Equiv.swap_apply_left]
      _ = y := hby

end Toffoli
