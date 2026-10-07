import Toffoli.Additions.CycleTransferBlock

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- One negation pair is completed with one transposition; its control
is negated precisely on that pair. -/
theorem odd_transfer_block (f : K → K) (hodd : ∀ x, f (-x) = -f x)
    (a : K) (ha : a ≠ -a) (x t : K) :
    (cycleTransferBlock a (-a) (-f a)).eval (x, t) =
      if x = a ∨ x = -a then (-x, t + f x) else (x, t) := by
  rw [(cycleTransferBlock_spec a (-a) (-f a) ha x t).1]
  by_cases hxa : x = a
  · subst x
    simp [transferIncrement]
  · by_cases hxna : x = -a
    · subst x
      simp [transferIncrement, hxa, hodd]
    · simp [transferIncrement, Equiv.swap_apply_def, hxa, hxna]

end Toffoli
