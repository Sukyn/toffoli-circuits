import Toffoli.Additions.CycleFamilyCorrect
import Toffoli.Additions.CycleFamilyCost
import Mathlib.Algebra.GroupWithZero.Units.Equiv

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- An affine permutation of the control wire. -/
noncomputable def affineControl (a b : K) (ha : a ≠ 0) : Equiv.Perm K :=
  (Equiv.mulLeft₀ a ha).trans (Equiv.addRight b)

/-- Transfer along the supplied cycles, then apply the affine inverse. -/
noncomputable def cycleSynthesis (a b : K) (ha : a ≠ 0)
    (cycles : List (List K)) (f : K → K) : Circuit K :=
  cycleFamilyCircuit cycles f ++ [.affine a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)]

/-- The cycle-synthesis algorithm, for any disjoint cycle listing covering the
field and composing to the chosen affine map. This checks its primitive gates,
control restoration and exact count. The paper's iff additionally needs the
necessity argument for arbitrary transfer amounts. -/
theorem cycle_synthesis_correct (a b : K) (ha : a ≠ 0)
    (cycles : List (List K)) (f : K → K)
    (hn : cycles.flatten.Nodup) (hcover : ∀ x, x ∈ cycles.flatten)
    (hperm : cycleFamilyPermutation cycles = affineControl a b ha)
    (hs : ∀ labels ∈ cycles, (labels.map f).sum = 0) :
    (cycleSynthesis a b ha cycles f).Realizes f ∧
    (cycleSynthesis a b ha cycles f).cost =
      (cycles.map (fun labels => labels.length - 1)).sum := by
  constructor
  · intro x t
    simp only [cycleSynthesis, Circuit.eval, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change Gate.eval (.affine a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha))
      ((cycleFamilyCircuit cycles f).eval (x, t)) = _
    rw [cycleFamily_correct cycles f hn hs, hperm]
    simp [hcover x, Gate.eval, affineControl, mul_add, ha]
  · rw [cycleSynthesis, circuit_cost_append, cycleFamily_cost]
    simp [Circuit.cost]

end Toffoli
