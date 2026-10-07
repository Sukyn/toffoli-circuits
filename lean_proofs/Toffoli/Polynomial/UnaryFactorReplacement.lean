import Toffoli.Foundations.MultiCircuitSwapConjugation
import Toffoli.Foundations.MultiCircuitRealizesList
import Toffoli.Additions.TransferDecomposition

namespace Toffoli

/-- Replace one linear factor by any unary zero-sum function. The remaining
factor is independent of that coordinate, so comparing a circuit before and
after a local swap transfers its increment between two coordinate values.
For example, over `ZMod 5`, a family for `μ*x_i*h` gives one for `μ*x_i^3*h`.
The supplied circuits and their swap conjugates restore every control. -/
theorem unary_factor_replacement {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (i : Fin n) (h : Controls K n → K)
    (hind : ∀ x a, h (Function.update x i a) = h x)
    (source : ∀ μ : K, ∃ c : MultiCircuit K n,
      c.Realizes (fun x => μ * (x i * h x)))
    (f : K → K) (hf : ∑ a, f a = 0) (μ : K) :
    ∃ c : MultiCircuit K n, c.Realizes (fun x => μ * (f (x i) * h x)) := by
  classical
  let labels := Finset.univ.erase (0 : K)
  have block (b : labels) : ∃ c : MultiCircuit K n,
      c.Realizes (fun x => μ * (transferIncrement 0 b.val (f b.val) (x i) * h x)) := by
    have hb : b.val ≠ 0 := (Finset.mem_erase.mp b.property).1
    let α := μ * (f b.val / b.val)
    obtain ⟨positive, hpositive⟩ := source α
    obtain ⟨negative, hnegative⟩ := source (-α)
    let conjugate := [MultiGate.swap i 0 b.val] ++ negative ++ [.swap i 0 b.val]
    have hconjugate := multi_circuit_swap_conjugation negative
      (fun x => (-α) * (x i * h x)) hnegative i 0 b.val
    have hrun := multi_circuit_realizes_append positive conjugate _ _ hpositive hconjugate
    refine ⟨positive ++ conjugate, ?_⟩
    intro x t
    rw [hrun]
    apply congrArg (fun increment => (x, t + increment))
    simp only [Function.update_self, hind]
    -- The same scalar transfer identity applies inside the independent factor h.
    have htransfer : (f b.val / b.val) * x i +
        (-(f b.val / b.val)) * Equiv.swap 0 b.val (x i) =
        transferIncrement 0 b.val (f b.val) (x i) := by
      simpa only [sub_zero] using transfer_increment_eq 0 b.val (f b.val) (x i) hb.symm
    calc
      α * (x i * h x) + (-α) * (Equiv.swap 0 b.val (x i) * h x) =
          μ * (((f b.val / b.val) * x i +
            (-(f b.val / b.val)) * Equiv.swap 0 b.val (x i)) * h x) := by
              dsimp [α]
              ring
      _ = μ * (transferIncrement 0 b.val (f b.val) (x i) * h x) := by rw [htransfer]

  choose circuits hcircuits using block
  refine ⟨labels.attach.toList.flatMap circuits, ?_⟩
  have hrun := multi_circuit_realizes_list labels.attach.toList circuits
    (fun b x => μ * (transferIncrement 0 b.val (f b.val) (x i) * h x))
    (fun b _ => hcircuits b)
  intro x t
  have hsum : (labels.attach.toList.map
      (fun b => μ * (transferIncrement 0 b.val (f b.val) (x i) * h x))).sum =
      μ * (f (x i) * h x) := by
    rw [Finset.sum_map_toList,
      Finset.sum_attach labels (fun b : K => μ * (transferIncrement 0 b (f b) (x i) * h x)),
      ← Finset.mul_sum, ← Finset.sum_mul]
    rw [show ∑ b ∈ labels, transferIncrement 0 b (f b) (x i) = f (x i) from
      transfer_decomposition f hf (x i)]
  simpa only [hsum] using hrun x t

end Toffoli
