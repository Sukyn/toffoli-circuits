import Toffoli.Foundations.MultiControlModel
import Mathlib.LinearAlgebra.Pi

namespace Toffoli

/-- Put the accumulator at coordinate zero and the controls at successors.
Mathlib's product exchange and tuple equivalence supply the inverse laws. -/
def registerJoin {K : Type*} [CommRing K] (n : ℕ) :
    (Controls K n × K) ≃ᵃ[K] Controls K (n + 1) :=
  ((LinearEquiv.prodComm K (Controls K n) K).trans
    (Fin.consLinearEquiv K (fun _ : Fin (n + 1) => K))).toAffineEquiv

end Toffoli
