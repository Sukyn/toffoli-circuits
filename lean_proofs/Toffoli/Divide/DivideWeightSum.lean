import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum

namespace Toffoli
open scoped BigOperators

/-- A degree-(n+1) step calls each group twice for preparation and restoration,
and its Gray traversal contributes another 1 + 2 + ... + 2^(n-1) calls. -/
theorem divide_weight_sum (n : ℕ) :
    (∑ j : Fin n, (2 + 2 ^ j.val)) = 2 ^ n + 2 * n - 1 := by
  have hgray : (∑ j : Fin n, (2 : ℕ) ^ j.val) + 1 = 2 ^ n := by
    rw [Fin.sum_univ_eq_sum_range]
    simpa using geom_sum_mul_add (1 : ℕ) n
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  omega

end Toffoli
