import Toffoli.Foundations.MultiControlModel

namespace Toffoli

/-- `none` denotes the final target; `some i` denotes control wire i used
as temporary workspace. This is a destination descriptor, not a gate. -/
abbrev IndexedTarget (n : ℕ) := Option (Fin n)

/-- Add an amount to one selected wire, leaving every other wire unchanged. -/
def indexedTargetAdd {K : Type*} [Add K] {n : ℕ}
    (target : IndexedTarget n) (amount : K) (state : Controls K n × K) :
    Controls K n × K :=
  match target with
  | none => (state.1, state.2 + amount)
  | some i => (Function.update state.1 i (state.1 i + amount), state.2)

end Toffoli
