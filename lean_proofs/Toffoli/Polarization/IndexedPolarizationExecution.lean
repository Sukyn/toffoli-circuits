import Toffoli.Polarization.IndexedPolarizationModel
import Toffoli.Polarization.IndexedPolarizationState
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- Replacing calls by primitive circuits preserves every intermediate
state. Group factors stay fixed because neither changing wire belongs to
a group; each callee restores every wire except its own destination. -/
theorem indexed_polarization_execution {K : Type*} [Field K] {m n : ℕ}
    (first : Fin n) (target : IndexedTarget n) (hfirst : target ≠ some first)
    (groups : Fin m → Finset (Fin n))
    (hgroups : ∀ j, first ∉ groups j)
    (htarget : ∀ j, ∀ k ∈ groups j, target ≠ some k)
    (group : Fin m → K → MultiCircuit K n) (power : K → MultiCircuit K n)
    (hgroup : ∀ j a x t, (group j a).eval (x, t) =
      (Function.update x first (x first + a * ∏ k ∈ groups j, x k), t))
    (hpower : ∀ a x t, (power a).eval (x, t) =
      indexedTargetAdd target (a * x first ^ (m + 1)) (x, t))
    (calls : List (PolarizationCall K m)) (x : Controls K n) (t : K) (s : K × K) :
    (compilePolarization group power calls).eval (polarizationState first target x t s) =
      polarizationState first target x t
        (runPolarization (fun j => ∏ k ∈ groups j, x k) calls s) := by
  classical
  -- Each factor is read from an unchanged wire.
  have hproducts (s : K × K) (j : Fin m) :
      (∏ k ∈ groups j, (polarizationState first target x t s).1 k) =
        ∏ k ∈ groups j, x k := by
    cases target with
    | none => exact Finset.prod_update_of_notMem (hgroups j) x s.1
    | some dest =>
      have hdest : dest ∉ groups j := fun hk => htarget j dest hk rfl
      exact (Finset.prod_update_of_notMem hdest (Function.update x first s.1) s.2).trans
        (Finset.prod_update_of_notMem (hgroups j) x s.1)
  have hvalue (s : K × K) : (polarizationState first target x t s).1 first = s.1 := by
    cases target with
    | none => simp [polarizationState]
    | some dest =>
      have hne : dest ≠ first := by simpa using hfirst
      simp [polarizationState, hne.symm]
  -- One compiled call performs the same update as its recorded counterpart.
  have hstep (call : PolarizationCall K m) (s : K × K) :
      (call.compile group power).eval (polarizationState first target x t s) =
        polarizationState first target x t
          (call.eval (fun j => ∏ k ∈ groups j, x k) s) := by
    rcases s with ⟨u, v⟩
    cases call with
    | group j a =>
      rw [PolarizationCall.compile, hgroup, hproducts, hvalue]
      cases target with
      | none => simp [polarizationState, PolarizationCall.eval]
      | some dest =>
        have hne : dest ≠ first := by simpa using hfirst
        simp [polarizationState, PolarizationCall.eval, Function.update_comm hne]
    | power a =>
      rw [PolarizationCall.compile, hpower, hvalue]
      cases target <;> simp [polarizationState, PolarizationCall.eval, indexedTargetAdd]
  -- The fold carries the single-call correspondence through the whole trace.
  simp only [compilePolarization, MultiCircuit.eval, List.foldl_flatMap, runPolarization]
  exact List.foldl_hom (polarizationState first target x t) (fun s call => hstep call s)

end Toffoli
