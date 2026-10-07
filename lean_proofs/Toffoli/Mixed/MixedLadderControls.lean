import Toffoli.Mixed.MixedModel

namespace Toffoli

/-- Every grouped-ladder update has fewer controls than its parent.
The first group is proper because there are at least two groups; each later
update adds one borrowed control to a group of size at most d-2. -/
theorem mixed_ladder_controls {d b : ℕ} (L : MixedLadder d b)
    (j : Fin L.groups.length) : 0 < L.controls j ∧ L.controls j < d := by
  have hd : 0 < d := by
    have := L.at_least_two.trans L.groups.length_le
    omega
  have hnotSingle : L.groups ≠ Composition.single d hd := by
    simp only [ne_eq, Composition.eq_single_iff_length hd]
    exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) L.at_least_two)
  have hgroup := (Composition.ne_single_iff hd).mp hnotSingle j
  have hpositive := L.groups.one_le_blocksFun j
  by_cases hfirst : j.val = 0
  · simpa only [MixedLadder.controls, if_pos hfirst, Nat.add_zero] using
      And.intro hpositive hgroup
  · have hsmaller := L.smaller j (by omega)
    simp only [MixedLadder.controls, if_neg hfirst]
    omega

end Toffoli
