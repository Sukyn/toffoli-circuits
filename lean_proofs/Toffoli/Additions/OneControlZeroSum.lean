import Toffoli.Additions.TwoPointTransfer
import Toffoli.Additions.TransferDecomposition
import Toffoli.Foundations.CircuitRealizesList

namespace Toffoli
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The direct-transfer construction, with no affine or control-permutation oracle. -/
noncomputable def directTransferCircuit (f : K → K) : Circuit K :=
  (Finset.univ.erase (0 : K)).toList.flatMap (fun b => twoPointTransfer 0 b (f b))

/-- Complete sufficiency proof for one control. This is a special case of the
paper's multi-control iff theorem, and is not counted as that full theorem.
-/
theorem one_control_zero_sum (f : K → K) (h : ∑ x, f x = 0) :
    (directTransferCircuit f).Realizes f := by
  have hall := circuit_realizes_list (Finset.univ.erase (0 : K)).toList
    (fun b => twoPointTransfer 0 b (f b))
    (fun b => transferIncrement 0 b (f b)) (by
      intro b hb
      have hb0 : b ≠ 0 := by simpa using hb
      exact (twoPointTransfer_spec 0 b (f b) hb0.symm).1)
  intro x t
  have hx := hall x t
  simpa [directTransferCircuit, ← Finset.sum_toList, transfer_decomposition f h x] using hx

end Toffoli
