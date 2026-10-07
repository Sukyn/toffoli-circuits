import Toffoli.Additions.CycleTransferBlock

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The paper's star transfers with unrestricted amounts, indexed by the
non-anchor label. Distinct labels allow every transfer to have its own amount. -/
noncomputable def cycleTransfersWithAmounts (a : K) : List K → (K → K) → Circuit K
  | [], _ => []
  | b :: rest, amounts => cycleTransferBlock a b (amounts b) ++
      cycleTransfersWithAmounts a rest amounts

/-- Target increment before restoring the control. For labels a,b,c the
increments are -amounts b, amounts b - amounts c, and amounts c. -/
noncomputable def cycleAmountsIncrement (a : K) : List K → (K → K) → K → K
  | [], _, _ => 0
  | b :: rest, amounts, x => transferIncrement a b (amounts b) x +
      cycleAmountsIncrement a rest amounts (Equiv.swap a b x)

noncomputable def cycleWithAmounts (labels : List K) (amounts : K → K) : Circuit K :=
  match labels with
  | [] => []
  | a :: rest => cycleTransfersWithAmounts a rest amounts

noncomputable def cycleFamilyWithAmounts (cycles : List (List K))
    (amounts : K → K) : Circuit K :=
  cycles.flatMap (fun labels => cycleWithAmounts labels amounts)

noncomputable def cycleSynthesisWithAmounts (a b : K) (ha : a ≠ 0)
    (cycles : List (List K)) (amounts : K → K) : Circuit K :=
  cycleFamilyWithAmounts cycles amounts ++
    [.affine a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)]

end Toffoli
