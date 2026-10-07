import Toffoli.Additions.TransferIncrement

/-! The unrestored three-gate block used in cycle synthesis. -/
namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Compare a SUM before and after swapping its control labels. -/
def cycleTransferBlock (a b eta : K) : Circuit K :=
  [.sum (eta / (b - a)), .swap a b, .sum (-(eta / (b - a)))]

/-- The control is swapped and the target receives opposite increments at the endpoints. -/
theorem cycleTransferBlock_spec (a b eta : K) (hab : a ≠ b) (x t : K) :
    (cycleTransferBlock a b eta).eval (x, t) =
      (Equiv.swap a b x, t + transferIncrement a b eta x) ∧
    (cycleTransferBlock a b eta).cost = 1 := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq K) (Classical.decEq K)
  constructor
  · simpa only [cycleTransferBlock, Circuit.eval, List.foldl_cons, List.foldl_nil,
      Gate.eval, add_assoc] using
      congrArg (fun increment => (Equiv.swap a b x, t + increment))
        (transfer_increment_eq a b eta x hab)
  · simp [cycleTransferBlock, Circuit.cost]

end Toffoli
