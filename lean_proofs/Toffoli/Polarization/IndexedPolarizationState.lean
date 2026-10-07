import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- Read either the final target or a control used as the destination. -/
def indexedTargetValue {K : Type*} {n : ℕ} (target : IndexedTarget n)
    (x : Controls K n) (t : K) : K :=
  match target with
  | none => t
  | some j => x j

/-- Place the two changing values in the ambient register. All other wires
retain their reference values in `x` and `t`. -/
def polarizationState {K : Type*} {n : ℕ} (first : Fin n) (target : IndexedTarget n)
    (x : Controls K n) (t : K) (state : K × K) : Controls K n × K :=
  match target with
  | none => (Function.update x first state.1, state.2)
  | some j => (Function.update (Function.update x first state.1) j state.2, t)

end Toffoli
