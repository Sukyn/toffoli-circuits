import Toffoli.Mixed.MixedRecurrence
import Toffoli.Mixed.MixedCountOne
import Toffoli.Mixed.MixedCountTwo

namespace Toffoli

/-- Every polarization choice bounds the mixed minimum. At two controls,
the unique composition has one singleton preparation and two squares. -/
theorem mixed_polarization_bound {p d : ℕ} (hp : 5 ≤ p) (hd : 2 ≤ d)
    (b : ℕ) (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2) :
    mixedCount p hp d b ≤ divideStepCost p c hdegree
      (fun j => mixedCount p hp (c.blocksFun j) (d + b - c.blocksFun j - 1)) := by
  by_cases hthree : 3 ≤ d
  · exact (mixed_recurrence hp hthree b).2 (Or.inl ⟨c, hdegree, rfl⟩)
  have hd : d = 2 := by omega
  subst d
  have hc : c = Composition.ones 1 :=
    Composition.eq_ones_iff_le_length.mpr (c.length_pos_of_pos (by decide))
  subst c
  simp [divideStepCost, mixed_count_one, mixed_count_two, optimalSquareCost,
    optimalSquareOrder]

end Toffoli
