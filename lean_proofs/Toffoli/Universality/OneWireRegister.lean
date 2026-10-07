import Toffoli.Universality.AffineSwapTransport
import Mathlib.LinearAlgebra.Pi

namespace Toffoli

/-- A one-coordinate register is affinely equivalent to its alphabet.
Thus a one-wire generation theorem applies to the register representation
used for larger circuits as well. Take `ι = Fin 1` for the paper's base case. -/
theorem one_wire_register {R ι : Type*} [CommRing R] [Unique ι]
    (τ : Equiv.Perm R) (h : affineSwapGroup R τ = ⊤) :
    affineSwapGroup R (Equiv.piCongrRight (fun _ : ι => τ)) = ⊤ := by
  let e := (LinearEquiv.funUnique ι R R).toAffineEquiv.symm
  have hgate : e.toEquiv.permCongr τ = Equiv.piCongrRight (fun _ : ι => τ) := by
    ext x i
    change τ (x default) = τ (x i)
    rw [Subsingleton.elim (default : ι) i]
  simpa only [hgate] using affine_swap_transport e τ h

end Toffoli
