import Toffoli.Polarization.PolarizationExecutionModel
import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

variable {K : Type*} [Field K] {m n : ℕ}

/-- Replace one recorded call by its chosen primitive circuit. -/
def PolarizationCall.compile
    (group : Fin m → K → MultiCircuit K n) (power : K → MultiCircuit K n) :
    PolarizationCall K m → MultiCircuit K n
  | .group i a => group i a
  | .power a => power a

/-- Concatenate the chosen circuits in the order of the polarization trace. -/
def compilePolarization
    (group : Fin m → K → MultiCircuit K n) (power : K → MultiCircuit K n)
    (calls : List (PolarizationCall K m)) : MultiCircuit K n :=
  calls.flatMap (PolarizationCall.compile group power)

end Toffoli
