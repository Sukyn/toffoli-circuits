import Toffoli.Quadratic.QuadraticSquareDecomposition
import Toffoli.Quadratic.SquareDecompositionLowerBound
import Toffoli.Quadratic.SquareTermsSynthesis
import Toffoli.Additions.OptimalSquareCostFormula

namespace Toffoli

/-- The least number of scaled squares is the symmetric matrix's rank.
The lower bound allows a competing decomposition to choose a different
affine part. The witness has exactly that many nonzero squares, and its
primitive circuit has the paper's exact transposition count. -/
theorem quadratic_additions {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) (ZMod p)) (hM : M.IsSymm)
    (constant : ZMod p) (linear : Fin n → ZMod p) :
    (∀ (terms : List (SquareTerm (ZMod p) n)) (b : ZMod p) (a : Fin n → ZMod p),
      (∀ x, quadraticValue M x + affineValue constant linear x =
        (terms.map (fun term => term.eval x)).sum + affineValue b a x) →
      M.rank ≤ terms.length) ∧
    ∃ (terms : List (SquareTerm (ZMod p) n)) (c : MultiCircuit (ZMod p) n),
      (∀ term ∈ terms, term.Nonzero) ∧ terms.length = M.rank ∧
      (terms.map SquareTerm.matrix).sum = M ∧
      c.Realizes (fun x => quadraticValue M x + affineValue constant linear x) ∧
      (c.cost : ℚ) = (M.rank : ℚ) * ((p - 1 : ℕ) : ℚ) *
        (1 - 1 / (optimalSquareOrder p hp : ℚ)) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  obtain ⟨terms, hterms, hlength, hmatrix⟩ := quadratic_square_decomposition h2 M hM
  obtain ⟨c, hc, hcost⟩ := square_terms_synthesis hp hn terms
    (fun term ht => (hterms term ht).2) constant linear
  have heval (x : Fin n → ZMod p) :
      quadraticValue M x = (terms.map (fun term => term.eval x)).sum := by
    simpa only [hmatrix] using (square_decomposition_matrix terms).2 x
  refine ⟨fun ts b a h => square_decomposition_lower_bound h2 M hM
    constant linear ts b a h, terms, c, hterms, hlength, hmatrix, ?_, ?_⟩
  · intro x t
    simpa only [← heval x] using hc x t
  · rw [hcost, hlength, Nat.cast_mul, optimal_square_cost_formula]
    ring

end Toffoli
