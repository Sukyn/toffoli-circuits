import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Transvection.Basic

namespace Toffoli

/-- SUM copies a nonzero difference from its source to its target, so it
changes Hamming distance from one to two. The wires may have any finite
index type, and the alphabet may be any nontrivial ring. -/
theorem hamming_shear {R I : Type*} [Ring R] [Nontrivial R] [DecidableEq R]
    [Fintype I] (i j : I) (hij : i ≠ j) :
    ∃ (e : (I → R) ≃ᵃ[R] (I → R)) (x y : I → R),
      hammingDist x y = 1 ∧ hammingDist (e x) (e y) = 2 := by
  classical
  let e := LinearEquiv.transvection
    (f := (LinearMap.proj i : (I → R) →ₗ[R] R))
    (v := Pi.single j 1) (by simp [hij])
  -- The inputs differ only at i; SUM makes their images differ at i and j.
  refine ⟨e.toAffineEquiv, 0, Pi.single i 1, ?_, ?_⟩
  · rw [hammingDist, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext k
    simp [Pi.single_apply]
  · have e_single : e (Pi.single i 1) = Pi.single i 1 + Pi.single j 1 := by
      simp [e, LinearMap.transvection.apply]
    have support : (Finset.univ.filter fun k : I =>
        (0 : R) ≠ (Pi.single i 1 + Pi.single j 1 : I → R) k) = {i, j} := by
      ext k
      by_cases hki : k = i
      · subst k; simp [hij]
      · by_cases hkj : k = j
        · subst k; simp [hij]
        · simp [hki, hkj]
    change hammingDist (e 0) (e (Pi.single i 1)) = 2
    rw [map_zero, e_single]
    change (Finset.univ.filter fun k : I =>
      (0 : R) ≠ (Pi.single i 1 + Pi.single j 1 : I → R) k).card = 2
    rw [support]
    simp [hij]

end Toffoli
