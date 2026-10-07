import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Defs

namespace Toffoli

/-- One ladder pass prepares each dirty wire, updates the final target,
then undoes the preparations in reverse order. The pair records the stage
and its actual coefficient; it does not prescribe an implementation or cost. -/
def indexedPassTrace {K : Type*} [One K] [Neg K] :
    (m : ℕ) → K → List (Fin (m + 1) × K)
  | 0, μ => [(0, μ)]
  | m + 1, μ => [(0, 1)] ++
      (indexedPassTrace m μ).map (fun call => (call.1.succ, call.2)) ++ [(0, -1)]

/-- A full positive pass followed by a negative tail pass cancels the dirty
inputs. Only the final-stage coefficients are scaled by `μ`; the first stage
and middle preparations use `±1`. -/
def indexedLadderTrace {K : Type*} [One K] [Neg K] (m : ℕ) (μ : K) :
    List (Fin (m + 2) × K) :=
  indexedPassTrace (m + 1) μ ++
    (indexedPassTrace m (-μ)).map (fun call => (call.1.succ, call.2))

end Toffoli
