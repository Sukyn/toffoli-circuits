import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Count

namespace Toffoli

/-- A trace can acquire at most one new observation per relevant call.
Irrelevant calls, repeated states, and intermediate observations are allowed. -/
theorem observed_scan_bound {State Call Observation : Type*} [DecidableEq Observation]
    (step : State → Call → State) (observe : State → Observation)
    (relevant : Call → Bool)
    (hstep : ∀ state call, relevant call = false →
      observe (step state call) = observe state)
    (calls : List Call) (initial : State) :
    ((calls.scanl step initial).map observe).toFinset.card ≤ calls.countP relevant + 1 := by
  induction calls generalizing initial with
  | nil => simp
  | cons call calls ih =>
    have hmem : observe (step initial call) ∈
        ((calls.scanl step (step initial call)).map observe).toFinset := by
      cases calls <;> simp
    simp only [List.scanl_cons, List.map_cons, List.toFinset_cons]
    cases h : relevant call with
    | false =>
      rw [hstep initial call h] at hmem
      rw [Finset.insert_eq_of_mem hmem]
      simpa [List.countP_cons, h] using ih (step initial call)
    | true =>
      simp only [List.countP_cons, h, ↓reduceIte]
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (ih (step initial call)) 1)

end Toffoli
