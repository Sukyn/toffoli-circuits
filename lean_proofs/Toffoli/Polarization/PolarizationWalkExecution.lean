import Toffoli.Polarization.PolarizationFlip

namespace Toffoli

/-- Execution follows the scanned Gray words. The target contains their signed
power sum; no polarization identity is assumed in this execution lemma. -/
theorem polarization_walk_run {K : Type*} [CommRing K] {n : ℕ}
    (factors : Fin n → K) (normalization x t : K) (word : GrayWord n)
    (flips : List (Fin n)) :
    runPolarization factors (polarizationWalk normalization word flips)
      (x + polarizationSum factors word, t) =
      (x + polarizationSum factors (flips.foldl grayFlip word),
        t + normalization * ((flips.scanl grayFlip word).map (fun signs =>
          polarizationWeight signs * (x + polarizationSum factors signs) ^ (n + 1))).sum) := by
  induction flips generalizing word t with
  | nil => simp [polarizationWalk, runPolarization, PolarizationCall.eval, mul_assoc]
  | cons i rest ih =>
    simp only [polarizationWalk, runPolarization, List.foldl_cons, PolarizationCall.eval]
    have hprepare : x + polarizationSum factors word +
        -2 * polarizationSign (word i) * factors i =
        x + polarizationSum factors (grayFlip word i) := by
      rw [polarization_sum_flip]
      ring
    rw [hprepare]
    change runPolarization factors (polarizationWalk normalization (grayFlip word i) rest)
      (x + polarizationSum factors (grayFlip word i),
        t + (normalization * polarizationWeight word) *
          (x + polarizationSum factors word) ^ (n + 1)) = _
    rw [ih]
    simp [List.scanl_cons, mul_add, mul_assoc, add_assoc]

end Toffoli
