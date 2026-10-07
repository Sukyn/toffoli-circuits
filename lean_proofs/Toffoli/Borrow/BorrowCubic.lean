import Toffoli.Borrow.BorrowCubicTrace
import Toffoli.Polarization.IndexedToffoli

namespace Toffoli

/-- The three-control case of Borrow uses the original wires and exactly
seven scaled Toffoli calls. Its primitive circuit restores every control,
including unused coordinates, for arbitrary initial control values and
every coefficient. A zero coefficient retains the same seven calls. -/
theorem borrow_cubic {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (i j y : Fin n) (hij : i ≠ j) (hiy : i ≠ y) (hjy : j ≠ y)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * x i * x j * x y) ∧
      c.cost = 7 * (2 * optimalSquareCost p hp) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [show (4 : ZMod p) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
  obtain ⟨prepare, hprepare, hprepare_cost, _⟩ :=
    indexed_toffoli hp i j hij (some y)
      (by simpa using hiy.symm) (by simpa using hjy.symm) 1
  obtain ⟨middle, hmiddle, hmiddle_cost, _⟩ :=
    indexed_toffoli hp i j hij (some y)
      (by simpa using hiy.symm) (by simpa using hjy.symm) (-2)
  obtain ⟨positive, hpositive, hpositive_cost, _⟩ :=
    indexed_toffoli hp y i hiy.symm none (by simp) (by simp) (μ / 4)
  obtain ⟨negative, hnegative, hnegative_cost, _⟩ :=
    indexed_toffoli hp y i hiy.symm none (by simp) (by simp) (-(μ / 4))
  simp only [indexedTargetAdd] at hprepare hmiddle hpositive hnegative
  obtain ⟨hrealizes, hcost⟩ := borrow_cubic_trace i j y hij hiy hjy μ h4
    prepare middle positive negative (by simpa only [one_mul] using hprepare)
    hmiddle hpositive hnegative
  refine ⟨borrowCubicCircuit i y hiy prepare middle positive negative, hrealizes, ?_⟩
  rw [hcost, hprepare_cost, hmiddle_cost, hpositive_cost, hnegative_cost]
  omega

end Toffoli
