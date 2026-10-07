import Toffoli.Additions.CycleAdditionCount

namespace Toffoli
variable {K : Type*} [Field K]

/-- The cycle condition for adding the scaled power μ*x^d. -/
def PowerCycleAdmissible (a b μ : K) (ha : a ≠ 0) (d : ℕ) : Prop :=
  ∀ C : Finset K, (affineControl a b ha).IsCycleOn (C : Set K) →
    ∑ x ∈ C, μ * x ^ d = 0

/-- The exact transposition count from `cycle_addition_count`. -/
noncomputable def affineCycleCost [Fintype K] [DecidableEq K]
    (a b : K) (ha : a ≠ 0) : ℕ :=
  Fintype.card K - (permutationCycleLists (affineControl a b ha)).length

/-- The paper's canonical power circuit, including affine control restoration. -/
noncomputable def powerCycleCircuit [Fintype K] [DecidableEq K]
    (a b μ : K) (ha : a ≠ 0) (d : ℕ) : Circuit K :=
  cycleSynthesis a b ha (permutationCycleLists (affineControl a b ha))
    (fun x => μ * x ^ d)

end Toffoli
