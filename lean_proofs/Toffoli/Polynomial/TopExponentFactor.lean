import Toffoli.Foundations.MultiCircuitConjugation
import Toffoli.Foundations.MultiCircuitRealizesAppend
import Toffoli.Foundations.CoordinateShearApply
import Mathlib.FieldTheory.Finite.Basic

namespace Toffoli

/-- Introduce an exponent `p - 1` using a shear and two correction circuits.
Expanding `(x_i+x_j)^2*x_j^(p-2)` leaves the desired cross term after
subtracting `x_i^2*x_j^(p-2)` and `x_j`, since `x_j^p=x_j`.
The remaining factor may depend on any coordinates except `i`. -/
theorem top_exponent_factor {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (i j : Fin n) (hij : i ≠ j)
    (h : Controls (ZMod p) n → ZMod p)
    (hind : ∀ x a, h (Function.update x i a) = h x)
    (square : ∀ μ : ZMod p, ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * (x i ^ 2 * x j ^ (p - 2) * h x)))
    (linear : ∀ μ : ZMod p, ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * (x j * h x)))
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * (x i * x j ^ (p - 1) * h x)) := by
  let e := coordinateShear j i (1 : ZMod p) hij.symm
  obtain ⟨positive, hpositive⟩ := square (μ / 2)
  obtain ⟨negative, hnegative⟩ := square (-(μ / 2))
  obtain ⟨correction, hcorrection⟩ := linear (-(μ / 2))
  let conjugate := [MultiGate.affine e] ++ positive ++ [.affine e.symm]
  have hconjugate := multi_circuit_conjugation positive _ hpositive e
  have hrun := multi_circuit_realizes_append (conjugate ++ negative) correction _ _
    (multi_circuit_realizes_append conjugate negative _ _ hconjugate hnegative) hcorrection
  refine ⟨(conjugate ++ negative) ++ correction, ?_⟩
  intro x t
  rw [hrun]
  apply congrArg (fun increment => (x, t + increment))
  simp only [e, coordinate_shear_apply, Function.update_self,
    Function.update_of_ne hij.symm, one_mul, hind]
  have hnext : x j * x j ^ (p - 2) = x j ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hfield : x j ^ 2 * x j ^ (p - 2) = x j := by
    rw [← pow_add, show 2 + (p - 2) = p by omega, ZMod.pow_card]
  have hexpand : (x i + x j) ^ 2 * x j ^ (p - 2) * h x -
      x i ^ 2 * x j ^ (p - 2) * h x - x j * h x =
      2 * (x i * x j ^ (p - 1) * h x) := by
    calc
      _ = 2 * (x i * (x j * x j ^ (p - 2)) * h x) +
          (x j ^ 2 * x j ^ (p - 2) - x j) * h x := by ring
      _ = _ := by rw [hnext, hfield]; ring
  have htwo : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  calc
    _ = (μ / 2) * ((x i + x j) ^ 2 * x j ^ (p - 2) * h x -
        x i ^ 2 * x j ^ (p - 2) * h x - x j * h x) := by ring
    _ = (μ / 2) * (2 * (x i * x j ^ (p - 1) * h x)) := by rw [hexpand]
    _ = μ * (x i * x j ^ (p - 1) * h x) := by
      rw [← mul_assoc, div_mul_cancel₀ _ htwo]

end Toffoli
