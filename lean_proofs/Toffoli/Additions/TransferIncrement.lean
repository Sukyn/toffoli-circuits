import Toffoli.Foundations.Basic

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def transferIncrement (a b eta x : K) : K := by
  classical
  exact if x = a then -eta else if x = b then eta else 0

/-- Comparing a linear function before and after a swap gives opposite
increments at its endpoints, and zero everywhere else. This scalar identity
is shared by the one-control block and unary factor replacement. -/
theorem transfer_increment_eq (a b eta x : K) (hab : a ≠ b) :
    (eta / (b - a)) * x + (-(eta / (b - a))) * Equiv.swap a b x =
      transferIncrement a b eta x := by
  classical
  have h : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  by_cases hxa : x = a
  · subst x
    simp [transferIncrement]
    field_simp
    ring
  · by_cases hxb : x = b
    · subst x
      simp [transferIncrement, hab.symm]
      field_simp
      ring
    · simp [transferIncrement, Equiv.swap_apply_def, hxa, hxb]

end Toffoli
