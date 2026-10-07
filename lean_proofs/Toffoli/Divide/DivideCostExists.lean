import Toffoli.Divide.DivideModel

namespace Toffoli

/-- A recursive construction exists at every positive degree. A quadratic
step with one group of size d-1 suffices for this existence argument. -/
theorem divide_cost_exists {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) :
    ∃ q, DivideCost p d q := by
  change 1 ≤ d at hd
  induction d, hd using Nat.le_induction with
  | base => exact ⟨0, DivideCost.sum⟩
  | succ d hd ih =>
    obtain ⟨q, hq⟩ := ih
    -- To add one control, use the d-control construction as the sole group.
    let c := Composition.single d hd
    have hdegree : c.length + 1 ≤ p - 2 := by
      simp only [c, Composition.single_length]
      omega
    refine ⟨_, DivideCost.step (show 2 ≤ d + 1 by omega) c hdegree (fun _ => q) ?_⟩
    intro j
    change DivideCost p (c.blocksFun j) q
    simpa only [c, Composition.single_blocksFun] using hq

end Toffoli
