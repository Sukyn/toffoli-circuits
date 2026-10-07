import Toffoli.Universality.OddRingRegisterStep
import Toffoli.Universality.OneWireRegister

namespace Toffoli

/-- Over an odd finite ring with at least five elements,
one-wire universality extends to every nonempty register. The induction
uses only the already universal smaller register. -/
theorem odd_ring_universality {R : Type*} [CommRing R]
    [Fintype R] [DecidableEq R]
    (hodd : Odd (Fintype.card R)) (hcard : 5 ≤ Fintype.card R)
    (hone : affineSwapGroup R (Equiv.swap (0 : R) 1) = ⊤)
    {n : ℕ} (hn : 0 < n) :
    affineSwapGroup R
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : R) 1)) = ⊤ := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hgate : Equiv.piCongrRight (fun _ : Fin 1 => Equiv.swap (0 : R) 1) =
        coordinatePermutation (0 : Fin 1) (Equiv.swap (0 : R) 1) := by
      ext x j
      simp [coordinate_permutation_apply, Subsingleton.elim j (0 : Fin 1)]
    simpa only [hgate] using one_wire_register (ι := Fin 1) (Equiv.swap (0 : R) 1) hone
  | succ n hn ih =>
    exact odd_ring_register_step hodd hcard hone hn ih

end Toffoli
