import Toffoli.Universality.AffineSwapModel
import Toffoli.Universality.ModularOneWireGenerators

namespace Toffoli

/-- Affine permutations and the fixed swap generate all permutations of one
modular wire. Translation by one already supplies the needed full cycle,
so this case holds for every alphabet size at least two. -/
theorem modular_one_wire {q : ℕ} (hq : 2 ≤ q) :
    affineSwapGroup (ZMod q) (Equiv.swap (0 : ZMod q) 1) = ⊤ := by
  classical
  apply top_unique
  rw [← modular_one_wire_generators hq]
  apply Subgroup.closure_mono
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl
  · left
    refine ⟨AffineEquiv.constVAdd (ZMod q) (ZMod q) 1, ?_⟩
    ext x
    rfl
  · exact Set.mem_union_right _ (Set.mem_singleton _)

end Toffoli
