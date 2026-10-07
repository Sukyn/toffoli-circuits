import Toffoli.Polynomial.MultiControlZeroSumNecessary
import Toffoli.Polynomial.PolynomialGridZeroSum
import Toffoli.Polynomial.PolynomialReducedRepresentative
import Toffoli.Polynomial.ReducedPolynomialSynthesis

namespace Toffoli

/-- The accumulator characterization for any positive number of controls.
Reduce the requested function to a polynomial; its zero grid sum removes
exactly the one monomial that the synthesis cannot produce. -/
theorem multi_control_zero_sum_iff {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (f : Controls (ZMod p) n → ZMod p) :
    (∃ c : MultiCircuit (ZMod p) n, c.Realizes f) ↔ (∑ x, f x) = 0 := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    exact multi_control_zero_sum_necessary (by rw [ZMod.card]; omega) c f hc
  · intro hzero
    obtain ⟨g, ⟨hdegree, heval⟩, _⟩ := polynomial_reduced_representative f
    have hcoeff := (polynomial_grid_zero_sum_iff g hdegree).mp
      (by simpa only [heval] using hzero)
    obtain ⟨c, hc⟩ := reduced_polynomial_synthesis hp hn g
      (by simpa only [ZMod.card] using hdegree)
      (by simpa only [ZMod.card] using hcoeff)
    refine ⟨c, ?_⟩
    intro x t
    simpa only [heval] using hc x t

end Toffoli
