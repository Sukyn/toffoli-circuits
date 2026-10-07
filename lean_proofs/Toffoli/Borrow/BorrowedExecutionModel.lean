import Toffoli.Borrow.BorrowedLadderModel

/-! The evaluator returns the final state and call trace. `runBorrowedAdd`
pairs each value update with its accumulator call. -/
namespace Toffoli

structure BorrowedStage (K : Type*) where
  factor : K
  dirty : K
  cost : ℕ

structure BorrowedExecution (K : Type*) where
  first : K
  stages : List (BorrowedStage K)
  target : K
  calls : List BorrowedCall

variable {K : Type*} [Ring K]

def runBorrowedAdd (call : Bool → BorrowedCall) (inverse : Bool)
    (amount value : K) : K × BorrowedCall :=
  (value + if inverse then -amount else amount, call inverse)

def runBorrowedPass (b : K) (stages : List (BorrowedStage K))
    (last t : K) (qLast : ℕ) (inverse : Bool) : BorrowedExecution K :=
  match stages with
  | [] =>
    let update := runBorrowedAdd (.target qLast) inverse (b * last) t
    ⟨b, [], update.1, [update.2]⟩
  | stage :: rest =>
    let prepare := runBorrowedAdd (.middle stage.cost) false (b * stage.factor) stage.dirty
    let result := runBorrowedPass prepare.1 rest last t qLast inverse
    let undo := runBorrowedAdd (.middle stage.cost) true (b * stage.factor) result.first
    ⟨b, { stage with dirty := undo.1 } :: result.stages, result.target,
      prepare.2 :: (result.calls ++ [undo.2])⟩

def runBorrowedLadder (first : K) (stages : List (BorrowedStage K))
    (last dirty t : K) (qFirst qLast : ℕ) : BorrowedExecution K :=
  let prepare := runBorrowedAdd (.first qFirst) false first dirty
  let positive := runBorrowedPass prepare.1 stages last t qLast false
  let undo := runBorrowedAdd (.first qFirst) true first positive.first
  let negative := runBorrowedPass undo.1 positive.stages last positive.target qLast true
  ⟨negative.first, negative.stages, negative.target,
    prepare.2 :: (positive.calls ++ undo.2 :: negative.calls)⟩

def borrowedValues (stages : List (BorrowedStage K)) : List (K × K) :=
  stages.map (fun stage => (stage.factor, stage.dirty))

def borrowedCosts (stages : List (BorrowedStage K)) : List ℕ :=
  stages.map BorrowedStage.cost

end Toffoli
