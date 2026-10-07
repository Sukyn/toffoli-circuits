import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Closure

namespace Toffoli

/-- Translation by one and the fixed swap generate every permutation of one
modular wire. This also covers even and composite alphabet sizes: translation
is a full cycle, so Mathlib's cycle-and-adjacent-swap theorem applies. -/
theorem modular_one_wire_generators {q : ℕ} (hq : 2 ≤ q) :
    Subgroup.closure ({Equiv.addLeft (1 : ZMod q), Equiv.swap 0 1} :
      Set (Equiv.Perm (ZMod q))) = ⊤ := by
  classical
  letI : NeZero q := ⟨by omega⟩
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  have hcycle : (Equiv.addLeft (1 : ZMod q)).IsCycle := by
    refine ⟨0, by simp, ?_⟩
    intro y _
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨k, by simp⟩
  have hsupport : (Equiv.addLeft (1 : ZMod q)).support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, add_eq_right]
  simpa using Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupport (0 : ZMod q)

end Toffoli
