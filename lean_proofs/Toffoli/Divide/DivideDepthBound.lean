import Toffoli.Divide.BalancedComposition
import Toffoli.Divide.DivideTerminalBound
import Toffoli.Divide.DivideWeightSum

namespace Toffoli
open scoped BigOperators

/-- Balanced q-way grouping costs at most one local budget per weighted
recursion node. Problems with d ≤ q^h fit within h levels; terminal
problems use direct polarization. The budget 2^q*p is uniform in d. -/
theorem divide_depth_bound {p q d h : ℕ} (hq : 2 ≤ q) (hp : q + 3 ≤ p)
    (hd : 1 ≤ d) (hdepth : d ≤ q ^ h) :
    divideCount p d ≤ 2 ^ q * p *
      ∑ i ∈ Finset.range (h + 1), (2 ^ q + 2 * q - 1) ^ i := by
  let W := 2 ^ q + 2 * q - 1
  have hfield : 5 ≤ p := by omega
  have hone (m : ℕ) : 1 ≤ ∑ i ∈ Finset.range (m + 1), W ^ i := by
    rw [geom_sum_succ]
    omega
  induction h generalizing d with
  | zero =>
    simp only [pow_zero] at hdepth
    simp [show d = 1 by omega, divide_count_one]
  | succ h ih =>
    by_cases hsmall : d ≤ q
    · exact (divide_terminal_bound hfield (by omega) hd hsmall).trans
        (by simpa using Nat.mul_le_mul_left (2 ^ q * p) (hone (h + 1)))

    -- Each balanced group fits into the preceding level's capacity q^h.
    obtain ⟨c, hgroups, hsize⟩ :=
      balanced_composition (show 0 < q by omega) (show q ≤ d - 1 by omega)
    have hdegree : c.length + 1 ≤ p - 2 := by omega
    have hceiling : (d - 1 + q - 1) / q ≤ q ^ h := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).2
      rw [Nat.succ_mul]
      rw [pow_succ] at hdepth
      omega
    have hchildren (j : Fin c.length) :
        divideCount p (c.blocksFun j) ≤ 2 ^ q * p *
          ∑ i ∈ Finset.range (h + 1), W ^ i :=
      ih (c.one_le_blocksFun j) ((hsize j).trans hceiling)
    have hpreparations : (∑ j : Fin c.length,
        (2 + 2 ^ j.val) * divideCount p (c.blocksFun j)) ≤
        W * (2 ^ q * p * ∑ i ∈ Finset.range (h + 1), W ^ i) := by
      calc
        _ ≤ ∑ j : Fin c.length, (2 + 2 ^ j.val) *
            (2 ^ q * p * ∑ i ∈ Finset.range (h + 1), W ^ i) :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hchildren j))
        _ = _ := by rw [← Finset.sum_mul, divide_weight_sum, hgroups]
    have hlocal : 2 ^ c.length * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) (c.length + 1) (by omega) (by omega)) ≤
        2 ^ q * p := by
      exact Nat.mul_le_mul (by rw [hgroups])
        ((Nat.sub_le _ _).trans (Nat.sub_le p 1))

    -- Add this node's budget to the weighted budgets of its children.
    calc
      divideCount p d ≤ divideStepCost p c hdegree
          (fun j => divideCount p (c.blocksFun j)) :=
        (divide_recurrence hfield (by omega)).2 c hdegree
      _ ≤ 2 ^ q * p + W * (2 ^ q * p * ∑ i ∈ Finset.range (h + 1), W ^ i) :=
        Nat.add_le_add hlocal hpreparations
      _ = 2 ^ q * p * ∑ i ∈ Finset.range (h + 1 + 1), W ^ i := by
        rw [geom_sum_succ (n := h + 1)]
        ring

end Toffoli
