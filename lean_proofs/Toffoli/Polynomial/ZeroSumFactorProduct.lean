import Toffoli.Polynomial.UnaryFactorReplacement

namespace Toffoli

/-- Starting from product-addition circuits, replace each coordinate factor
by a unary zero-sum function. The induction records which factors have
already been replaced; the other coordinates still occur linearly. -/
theorem zero_sum_factor_product {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (source : ∀ μ : K, ∃ c : MultiCircuit K n,
      c.Realizes (fun x => μ * ∏ i, x i))
    (f : Fin n → K → K) (hf : ∀ i, ∑ a, f i a = 0) (μ : K) :
    ∃ c : MultiCircuit K n, c.Realizes (fun x => μ * ∏ i, f i (x i)) := by
  classical
  let factors (s : Finset (Fin n)) (x : Controls K n) :=
    ∏ j, if j ∈ s then f j (x j) else x j
  have synthesize (s : Finset (Fin n)) : ∀ a : K, ∃ c : MultiCircuit K n,
      c.Realizes (fun x => a * factors s x) := by
    induction s using Finset.induction_on with
    | empty =>
      intro a
      simpa [factors] using source a
    | @insert i s hi ih =>
      let h (x : Controls K n) :=
        ∏ j ∈ Finset.univ.erase i, if j ∈ s then f j (x j) else x j
      have hind (x : Controls K n) (a : K) : h (Function.update x i a) = h x := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
      have hbefore (x : Controls K n) : factors s x = x i * h x := by
        simpa only [if_neg hi] using
          (Finset.mul_prod_erase Finset.univ
            (fun j => if j ∈ s then f j (x j) else x j) (Finset.mem_univ i)).symm
      have hafter (x : Controls K n) : factors (insert i s) x = f i (x i) * h x := by
        change (∏ j, if j ∈ insert i s then f j (x j) else x j) = _
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => if j ∈ insert i s then f j (x j) else x j) (Finset.mem_univ i)]
        simp only [Finset.mem_insert_self, if_true]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_insert, (Finset.mem_erase.mp hj).1, false_or]
      have hsource (a : K) : ∃ c : MultiCircuit K n,
          c.Realizes (fun x => a * (x i * h x)) := by
        obtain ⟨c, hc⟩ := ih a
        exact ⟨c, fun x t => by simpa only [hbefore x] using hc x t⟩
      intro a
      obtain ⟨c, hc⟩ := unary_factor_replacement i h hind hsource (f i) (hf i) a
      exact ⟨c, fun x t => by simpa only [hafter x] using hc x t⟩
  simpa [factors] using synthesize Finset.univ μ

end Toffoli
