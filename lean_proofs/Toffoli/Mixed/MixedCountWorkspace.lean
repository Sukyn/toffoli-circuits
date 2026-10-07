import Toffoli.Mixed.MixedCostWorkspace
import Toffoli.Mixed.MixedCountSpec

namespace Toffoli

/-- More available borrowed wires can only lower the numerical minimum. -/
theorem mixed_count_workspace {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) :
    Antitone (mixedCount p hp d) := by
  intro b b' hb
  -- Reuse an attaining tree; enlarging its workspace leaves its cost unchanged.
  obtain ⟨tree, _⟩ := mixed_count_spec hp hd b
  exact (mixed_count_spec hp hd b').2 _
    (mixed_cost_workspace hp tree b' hb)

end Toffoli
