import Toffoli.Additions.OddTransferBlock

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

def oddBlocks (f : K → K) (representatives : List K) : Circuit K :=
  representatives.flatMap (fun a => cycleTransferBlock a (-a) (-f a))

/-- Disjoint negation pairs can be completed independently in any order. -/
theorem odd_blocks_eval (f : K → K) (hodd : ∀ x, f (-x) = -f x)
    (l : List K) (hnodup : l.Nodup)
    (hpairs : ∀ a ∈ l, ∀ b ∈ l, a ≠ -b) (x t : K) :
    (oddBlocks f l).eval (x, t) =
      if x ∈ l ∨ -x ∈ l then (-x, t + f x) else (x, t) := by
  induction l generalizing x t with
  | nil => simp [oddBlocks, Circuit.eval]
  | cons a l ih =>
    have hna : a ∉ l := (List.nodup_cons.mp hnodup).1
    have hn : l.Nodup := (List.nodup_cons.mp hnodup).2
    have hp : ∀ b ∈ l, ∀ c ∈ l, b ≠ -c := by
      intro b hb c hc
      exact hpairs b (by simp [hb]) c (by simp [hc])
    have ha : a ≠ -a := hpairs a (by simp) a (by simp)
    have hnna : -a ∉ l := by
      intro hmem
      have h := hpairs a (by simp) (-a) (by simp [hmem])
      exact h (neg_neg a).symm
    change (oddBlocks f l).eval
      ((cycleTransferBlock a (-a) (-f a)).eval (x, t)) = _
    rw [odd_transfer_block f hodd a ha x t]
    by_cases hx : x = a ∨ x = -a
    · rw [if_pos hx, ih hn hp]
      have hnone : ¬(-x ∈ l ∨ -(-x) ∈ l) := by
        rcases hx with rfl | rfl <;> simp [hna, hnna]
      rw [if_neg hnone]
      have hsome : x ∈ a :: l ∨ -x ∈ a :: l := by
        rcases hx with rfl | rfl <;> simp
      rw [if_pos hsome]
    · rw [if_neg hx, ih hn hp]
      have hxa : x ≠ a := (not_or.mp hx).1
      have hnxa : -x ≠ a := by
        intro h
        exact (not_or.mp hx).2 (neg_eq_iff_eq_neg.mp h)
      simp only [List.mem_cons, hxa, hnxa, false_or]

end Toffoli
