import EC2.EntropySpectral
import EC2.EntropyMatrixAlgebra
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Rectangular matrix spectra and block entropy

The squared singular values are the eigenvalues of `M * Mᴴ`; this includes
rectangular matrices and all their zero eigenvalues.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EC2.Entropy

variable {r s t u : Type*} [Fintype r] [Fintype s] [Fintype t] [Fintype u]
  [DecidableEq r] [DecidableEq s] [DecidableEq t] [DecidableEq u]

def rectSchattenNorm (M : Matrix r s ℂ) (q : ℝ) : ℝ :=
  spectralNorm (gramSpectrum M) q

theorem rectSchattenNorm_rpow (M : Matrix r s ℂ) {q : ℝ} (hq : 0 < q) :
    rectSchattenNorm M q ^ q = moment (gramSpectrum M) q := by
  have hnonneg : 0 ≤ moment (gramSpectrum M) q := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (gramSpectrum_nonneg M i) _
  rw [rectSchattenNorm, spectralNorm, ← Real.rpow_mul hnonneg,
    one_div_mul_cancel hq.ne', Real.rpow_one]

/-- The external Schatten Hanner inequality at fixed arbitrary rectangular dimensions.
This is exactly the substantial cited input; no EC2 entropy statement occurs in it. -/
def RectangularHanner (r s : Type*) [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s] : Prop :=
  ∀ (X Y : Matrix r s ℂ) (q : ℝ), 2 ≤ q →
    rectSchattenNorm (X + Y) q ^ q + rectSchattenNorm (X - Y) q ^ q ≤
      (rectSchattenNorm X q + rectSchattenNorm Y q) ^ q +
        |rectSchattenNorm X q - rectSchattenNorm Y q| ^ q

/-- The full balanced rectangular block entropy inequality in its finite
spectral representation, including zero blocks and `x = y`.
`hHanner` is precisely the established external Schatten Hanner theorem.
Every EC2-specific step of the implication is proved. -/
theorem balanced_rectangular_entropy_nats
    (A B C D : Matrix r s ℂ) (x y : ℝ)
    (hA : gramMass A = x / 2) (hB : gramMass B = y / 2)
    (hC : gramMass C = y / 2) (hD : gramMass D = x / 2)
    (hxy : x + y = 1)
    (hM : gramMass (Matrix.fromBlocks A B C D) = 1)
    (hHanner : RectangularHanner (r ⊕ r) (s ⊕ s)) :
    wNats |x - y| + weightedGramEntropy A + weightedGramEntropy B +
      weightedGramEntropy C + weightedGramEntropy D ≤
      gramEntropy (Matrix.fromBlocks A B C D) := by
  let X : Matrix (r ⊕ r) (s ⊕ s) ℂ := Matrix.fromBlocks A 0 0 D
  let Y : Matrix (r ⊕ r) (s ⊕ s) ℂ := Matrix.fromBlocks 0 B C 0
  have hx : gramMass X = x := by
    have h := gramSpectrum_sum_fromBlocks_zero A D (fun z => z)
    change gramMass X = gramMass A + gramMass D at h
    rw [h, hA, hD]
    ring
  have hy : gramMass Y = y := by
    have h := gramSpectrum_sum_fromBlocks_offDiagonal B C (fun z => z)
    change gramMass Y = gramMass B + gramMass C at h
    rw [h, hB, hC]
    ring
  have hEX : gramEntropy X = gramEntropy A + gramEntropy D :=
    gramSpectrum_sum_fromBlocks_zero A D Real.negMulLog
  have hEY : gramEntropy Y = gramEntropy B + gramEntropy C :=
    gramSpectrum_sum_fromBlocks_offDiagonal B C Real.negMulLog
  have hmoment : ∀ q : ℝ, 2 < q →
      2 * moment (gramSpectrum (Matrix.fromBlocks A B C D)) q ≤
        (spectralNorm (gramSpectrum X) q + spectralNorm (gramSpectrum Y) q) ^ q +
          |spectralNorm (gramSpectrum X) q - spectralNorm (gramSpectrum Y) q| ^ q := by
    intro q hq
    have h := hHanner X Y q hq.le
    have hadd : X + Y = Matrix.fromBlocks A B C D := by
      simp [X, Y, Matrix.fromBlocks_add]
    have hsub : X - Y = Matrix.fromBlocks A (-B) (-C) D := by
      ext (i | i) (j | j) <;> simp [X, Y]
    have hneg : rectSchattenNorm (Matrix.fromBlocks A (-B) (-C) D) q =
        rectSchattenNorm (Matrix.fromBlocks A B C D) q := by
      simp only [rectSchattenNorm, gramSpectrum_fromBlocks_neg]
    rw [hadd, hsub, hneg,
      rectSchattenNorm_rpow _ (by linarith : 0 < q)] at h
    simpa only [← two_mul, rectSchattenNorm] using h
  have hd := entropy_le_from_hanner
    (gramSpectrum (Matrix.fromBlocks A B C D)) (gramSpectrum X) (gramSpectrum Y)
    (gramSpectrum_nonneg _) (gramSpectrum_nonneg _) (gramSpectrum_nonneg _) hM
    (show mass (gramSpectrum X) + mass (gramSpectrum Y) = 1 by change gramMass X + gramMass Y = 1; rw [hx, hy, hxy])
    hmoment
  change wNats |gramMass X - gramMass Y| + weightedGramEntropy X +
    weightedGramEntropy Y - Real.log 2 ≤ gramEntropy (Matrix.fromBlocks A B C D) at hd
  rw [hx, hy] at hd
  have hclass :
      Real.negMulLog (gramMass A) + Real.negMulLog (gramMass B) +
      Real.negMulLog (gramMass C) + Real.negMulLog (gramMass D) =
      Real.negMulLog x + Real.negMulLog y + Real.log 2 := by
    rw [hA, hB, hC, hD]
    have hc := balanced_classical_entropy x y hxy
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      show 1 - x = y by linarith] at hc
    linarith
  have hsplit : weightedGramEntropy X + weightedGramEntropy Y - Real.log 2 =
      weightedGramEntropy A + weightedGramEntropy B +
        weightedGramEntropy C + weightedGramEntropy D := by
    have hX := gramEntropy_decomposition X
    have hY := gramEntropy_decomposition Y
    rw [hx] at hX
    rw [hy] at hY
    linarith [gramEntropy_decomposition A, gramEntropy_decomposition B,
      gramEntropy_decomposition C, gramEntropy_decomposition D]
  linarith

end EC2.Entropy
