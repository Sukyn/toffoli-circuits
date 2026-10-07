import Toffoli.Foundations.AffineLocalMono

namespace Toffoli

/-- A circuit may use a larger pool provided its accumulator target remains
excluded. Every gate retains its read and write restrictions. -/
theorem circuit_locality_mono {K : Type*} [Field K] {n : ℕ}
    {c : MultiCircuit K n} {small large : Finset (Fin n)} {target : IndexedTarget n}
    (h : c.AccumulatorLocal small target) (hsub : small ⊆ large)
    (htarget : ∀ i ∈ large, target ≠ some i) : c.AccumulatorLocal large target := by
  refine ⟨htarget, ?_⟩
  intro gate hgate
  cases h.gates gate hgate with
  | affine target e hlocal =>
    exact AccumulatorGate.affine target e (affine_local_mono hlocal hsub)
  | swap target i hi a b =>
    exact AccumulatorGate.swap target i (hsub hi) a b
  | sum i hi coefficient =>
    exact AccumulatorGate.sum i (hsub hi) coefficient
  | shear source dest hsource coefficient hne =>
    exact AccumulatorGate.shear source dest (hsub hsource) coefficient hne

end Toffoli
