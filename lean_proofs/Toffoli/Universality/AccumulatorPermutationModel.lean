import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod

namespace Toffoli
open scoped Classical

/-- Add a control-dependent value to the target, leaving the controls fixed. -/
def targetAddition {C K : Type*} [AddGroup K] (f : C → K) : Equiv.Perm (C × K) :=
  Equiv.prodCongrRight (fun x => Equiv.addRight (f x))

/-- The same swap of zero and one on every target fiber. -/
noncomputable def targetSwap {C K : Type*} [Zero K] [One K] : Equiv.Perm (C × K) :=
  Equiv.prodCongrRight (fun _ => Equiv.swap (0 : K) 1)

end Toffoli
