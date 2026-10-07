import Toffoli.Polarization.PolarizationModel
import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- One call to a chosen group circuit, or to the one-control power circuit.
Each supplied subcircuit is assumed to restore its own controls and workspace. -/
inductive PolarizationCall (K : Type*) (n : ℕ) where
  | group (index : Fin n) (coefficient : K)
  | power (coefficient : K)

variable {K : Type*} [CommRing K] {n : ℕ}

def PolarizationCall.eval (factors : Fin n → K)
    (call : PolarizationCall K n) (state : K × K) : K × K :=
  match call with
  | .group i a => (state.1 + a * factors i, state.2)
  | .power a => (state.1, state.2 + a * state.1 ^ (n + 1))

def runPolarization (factors : Fin n → K) (calls : List (PolarizationCall K n))
    (state : K × K) : K × K :=
  calls.foldl (fun state call => call.eval factors state) state

/-- Evaluate the current signed power, then flip one coordinate and recurse.
The coefficient -2*sign changes +F to -F, or -F to +F, in one group call. -/
def polarizationWalk (normalization : K) (word : GrayWord n) :
    List (Fin n) → List (PolarizationCall K n)
  | [] => [.power (normalization * polarizationWeight word)]
  | i :: rest =>
    .power (normalization * polarizationWeight word) ::
      .group i (-2 * polarizationSign (word i)) ::
        polarizationWalk normalization (grayFlip word i) rest

/-- The complete preparation, Gray walk and restoration on the first control. -/
def polarizationCircuit (normalization : K) : List (PolarizationCall K n) :=
  let start : GrayWord n := fun _ => false
  let last := (grayFlips n).foldl grayFlip start
  List.ofFn (fun i : Fin n => PolarizationCall.group i (1 : K)) ++
    polarizationWalk normalization start (grayFlips n) ++
    List.ofFn (fun i : Fin n => PolarizationCall.group i (-polarizationSign (last i)))

def polarizationGroupCalls (calls : List (PolarizationCall K n)) : List (Fin n) :=
  calls.filterMap (fun call => match call with
    | .group i _ => some i
    | .power _ => none)

def polarizationPowerCalls (calls : List (PolarizationCall K n)) : ℕ :=
  (calls.filter (fun call => match call with
    | .group _ _ => false
    | .power _ => true)).length

end Toffoli
