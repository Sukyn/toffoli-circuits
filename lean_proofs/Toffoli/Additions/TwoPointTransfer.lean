import Toffoli.Additions.CycleTransferBlock

/-! `lem:two-point-transfer`: the complete four-gate circuit restores the control. -/
namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The last swap restores the control after its increment has been transferred. -/
def twoPointTransfer (a b eta : K) : Circuit K :=
  cycleTransferBlock a b eta ++ [.swap a b]

/-- The circuit realizes the paper's three-case update with two transpositions. -/
theorem twoPointTransfer_spec (a b eta : K) (hab : a ≠ b) :
    (twoPointTransfer a b eta).Realizes (transferIncrement a b eta) ∧
    (twoPointTransfer a b eta).cost = 2 := by
  classical
  -- Use the evaluator's equality instance for both swaps and their increment.
  cases Subsingleton.elim (inferInstance : DecidableEq K) (Classical.decEq K)
  constructor
  · intro x t
    change (Gate.swap a b).eval ((cycleTransferBlock a b eta).eval (x, t)) = _
    rw [(cycleTransferBlock_spec a b eta hab x t).1]
    simp [Gate.eval]
  · simp [twoPointTransfer, cycleTransferBlock, Circuit.cost]

end Toffoli
