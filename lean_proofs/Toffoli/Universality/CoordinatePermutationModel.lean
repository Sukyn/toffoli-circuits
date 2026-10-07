import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Pi.Lemmas

namespace Toffoli

/-- Apply a label permutation on one coordinate, fixing every other wire.
Mathlib's coordinate inclusion and group action supply the homomorphism laws. -/
noncomputable def coordinatePermutation {I A : Type*} (i : I) :
    Equiv.Perm A →* Equiv.Perm (I → A) := by
  classical
  exact (MulAction.toPermHom (I → Equiv.Perm A) (I → A)).comp
    (MonoidHom.mulSingle (fun _ : I => Equiv.Perm A) i)

end Toffoli
