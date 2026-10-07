import Toffoli.Foundations.AccumulatorLocalityModel
import Toffoli.Foundations.CoordinateLiftModel

namespace Toffoli

/-- Scaling and translating one control neither reads nor changes another wire. -/
theorem coordinate_affine_locality {K : Type*} [Field K] {n : ℕ}
    (i : Fin n) (a b : K) (ha : a ≠ 0) :
    AffineLocal {i} (coordinateAffine i a b ha) := by
  classical
  constructor
  · intro x j hj
    have hji : j ≠ i := by simpa only [Finset.mem_singleton] using hj
    simp [coordinateAffine, hji]
  · intro x y hxy j hj
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    have hvalue : x i = y i := hxy i (Finset.mem_singleton_self i)
    simp [coordinateAffine, hvalue]

end Toffoli
