import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

namespace Toffoli

/-- A preparation also excludes its own internal target. Removing that wire
from the parent's available workspace leaves one fewer borrowed wire. -/
theorem workspace_preparation_card {W : Type*} [DecidableEq W]
    (pool controls : Finset W) (hcontrols : controls ⊆ pool)
    (target : W) (htarget : target ∈ pool \ controls) :
    (pool.erase target \ controls).card = pool.card - controls.card - 1 := by
  rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem htarget,
    Finset.card_sdiff_of_subset hcontrols]

end Toffoli
