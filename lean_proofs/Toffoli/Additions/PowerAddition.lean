import Toffoli.Additions.CycleAddition
import Toffoli.Additions.PowerCycles
import Toffoli.Additions.PowerMultiplierExists

namespace Toffoli

/-- Every power in the paper's degree range has a primitive one-control
addition circuit. Choose a multiplier, then use the complete cycle theorem. -/
theorem power_addition {K : Type*} [Field K] [Fintype K]
    (μ : K) (d : ℕ) (hd : d ≠ 0) (hbound : d < Nat.card K - 1) :
    ∃ c : Circuit K, c.Realizes (fun x => μ * x ^ d) := by
  classical
  obtain ⟨a, ha, had⟩ := power_multiplier_exists (K := K) d hd hbound
  have heq : affineControl a 0 ha = Equiv.mulLeft₀ a ha := by
    ext x
    simp [affineControl]
  have hs : ∀ C : Finset K, (affineControl a 0 ha).IsCycleOn (C : Set K) →
      ∑ x ∈ C, μ * x ^ d = 0 := by
    intro C hC
    rw [heq] at hC
    exact power_cycles a μ d ha had C hC
  obtain ⟨amounts, h⟩ := (cycle_addition a 0 ha (fun x => μ * x ^ d)).mpr hs
  exact ⟨_, h⟩

end Toffoli
