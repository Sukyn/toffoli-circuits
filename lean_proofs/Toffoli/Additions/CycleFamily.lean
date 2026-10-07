import Toffoli.Additions.CycleTransfers
import Mathlib.GroupTheory.Perm.List

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Empty and singleton cycles require no transfers. -/
noncomputable def cycleCircuit (labels : List K) (f : K → K) : Circuit K :=
  match labels with
  | [] => []
  | a :: rest => cycleTransfers a rest f

/-- Execute the transfer sequences of all listed cycles. -/
noncomputable def cycleFamilyCircuit (cycles : List (List K)) (f : K → K) : Circuit K :=
  cycles.flatMap (fun labels => cycleCircuit labels f)

/-- The product is reversed because gate lists execute from left to right. -/
def cycleFamilyPermutation (cycles : List (List K)) : Equiv.Perm K :=
  (cycles.map List.formPerm).reverse.prod

end Toffoli
