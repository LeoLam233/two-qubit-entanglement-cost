import EC2.EntropyScalar
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section
open scoped BigOperators

namespace EC2.Entropy

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- Squared singular-value spectrum of an arbitrary complex rectangular matrix,
with the zero eigenvalues on the row space retained. -/
def gramSpectrum (M : Matrix r s ℂ) : r → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues

def gramEntropy (M : Matrix r s ℂ) : ℝ := entropy (gramSpectrum M)

def gramMass (M : Matrix r s ℂ) : ℝ := mass (gramSpectrum M)

def weightedGramEntropy (M : Matrix r s ℂ) : ℝ :=
  gramMass M * normalizedEntropy (gramSpectrum M)

theorem gramSpectrum_nonneg (M : Matrix r s ℂ) (i : r) : 0 ≤ gramSpectrum M i :=
  Matrix.eigenvalues_self_mul_conjTranspose_nonneg M i

theorem gramEntropy_decomposition (M : Matrix r s ℂ) :
    gramEntropy M = Real.negMulLog (gramMass M) + weightedGramEntropy M :=
  entropy_normalize_nonneg (gramSpectrum M) (gramSpectrum_nonneg M)

end EC2.Entropy
