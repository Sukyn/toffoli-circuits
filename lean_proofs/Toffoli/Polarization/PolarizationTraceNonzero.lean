import Toffoli.Polarization.GroupedPolarization

namespace Toffoli

def PolarizationCall.coefficient {K : Type*} {m : ℕ} : PolarizationCall K m → K
  | .group _ a => a
  | .power a => a

/-- A nonzero product coefficient gives nonzero coefficients at every
preparation, Gray flip, power addition and restoration in its trace. -/
theorem polarization_trace_nonzero {p m : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hdegree : m + 1 ≤ p - 2) {μ : ZMod p} (hμ : μ ≠ 0)
    {call : PolarizationCall (ZMod p) m}
    (hcall : call ∈ polarizationCircuit
      (μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹))) :
    call.coefficient ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have hfactorial : ((m + 1).factorial : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
    omega
  let a := μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹)
  have ha : a ≠ 0 :=
    mul_ne_zero hμ (inv_ne_zero (mul_ne_zero (pow_ne_zero m htwo) hfactorial))
  have hsign (bit : Bool) : (polarizationSign bit : ZMod p) ≠ 0 := by
    cases bit <;> simp [polarizationSign]
  have hweight (word : GrayWord m) : (polarizationWeight word : ZMod p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hsign (word i))
  have hwalk (word : GrayWord m) (flips : List (Fin m)) :
      ∀ call ∈ polarizationWalk a word flips, call.coefficient ≠ 0 := by
    induction flips generalizing word with
    | nil =>
      intro call h
      simp only [polarizationWalk, List.mem_singleton] at h
      subst call
      exact mul_ne_zero ha (hweight word)
    | cons i flips ih =>
      intro call h
      simp only [polarizationWalk, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact mul_ne_zero ha (hweight word)
      · exact mul_ne_zero (neg_ne_zero.mpr htwo) (hsign (word i))
      · exact ih (grayFlip word i) call h
  change call ∈ polarizationCircuit a at hcall
  simp only [polarizationCircuit, List.mem_append, or_assoc] at hcall
  rcases hcall with hprepare | hwalkCall | hrestore
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hprepare
    exact one_ne_zero
  · exact hwalk _ _ call hwalkCall
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrestore
    exact neg_ne_zero.mpr (hsign _)

end Toffoli
