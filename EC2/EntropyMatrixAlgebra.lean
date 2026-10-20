import EC2.EntropyMatrixDefs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Spectral identities for arbitrary finite complex rectangular block matrices. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EC2.Entropy

variable {r s t u : Type*} [Fintype r] [Fintype s] [Fintype t] [Fintype u]
  [DecidableEq r] [DecidableEq s] [DecidableEq t] [DecidableEq u]

/-- Applying any real-valued function to a Hermitian spectrum and summing it
can be computed from the characteristic-polynomial roots. -/
theorem sum_function_eigenvalues_eq_roots (A : Matrix r r ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (hA.eigenvalues i)) =
      (A.charpoly.roots.map (fun z : ℂ => f z.re)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp [Function.comp_def, Finset.sum_map_val]

theorem sum_function_eigenvalues_fromBlocks
    (A : Matrix r r ℂ) (D : Matrix t t ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hAD : (Matrix.fromBlocks A (0 : Matrix r t ℂ) (0 : Matrix t r ℂ) D).IsHermitian)
    (f : ℝ → ℝ) :
    (∑ i, f (hAD.eigenvalues i)) =
      (∑ i, f (hA.eigenvalues i)) + (∑ j, f (hD.eigenvalues j)) := by
  rw [sum_function_eigenvalues_eq_roots _ hAD,
    sum_function_eigenvalues_eq_roots _ hA, sum_function_eigenvalues_eq_roots _ hD,
    Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic A).ne_zero
      (Matrix.charpoly_monic D).ne_zero), Multiset.map_add, Multiset.sum_add]

/-- Direct-sum spectral identity for two arbitrary rectangular blocks. -/
theorem gramSpectrum_sum_fromBlocks_zero
    (A : Matrix r s ℂ) (D : Matrix t u ℂ) (f : ℝ → ℝ) :
    (∑ i, f (gramSpectrum (Matrix.fromBlocks A (0 : Matrix r u ℂ)
      (0 : Matrix t s ℂ) D) i)) =
      (∑ i, f (gramSpectrum A i)) + (∑ j, f (gramSpectrum D j)) := by
  have hgram :
      Matrix.fromBlocks A (0 : Matrix r u ℂ) (0 : Matrix t s ℂ) D *
        (Matrix.fromBlocks A (0 : Matrix r u ℂ) (0 : Matrix t s ℂ) D).conjTranspose =
      Matrix.fromBlocks (A * A.conjTranspose) (0 : Matrix r t ℂ)
        (0 : Matrix t r ℂ) (D * D.conjTranspose) := by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  let hAD := (Matrix.isHermitian_mul_conjTranspose_self A).fromBlocks
    (by simp : (0 : Matrix r t ℂ).conjTranspose = (0 : Matrix t r ℂ))
    (Matrix.isHermitian_mul_conjTranspose_self D)
  change (∑ i, f ((Matrix.isHermitian_mul_conjTranspose_self
    (Matrix.fromBlocks A (0 : Matrix r u ℂ) (0 : Matrix t s ℂ) D)).eigenvalues i)) = _
  have heig : (Matrix.isHermitian_mul_conjTranspose_self
      (Matrix.fromBlocks A (0 : Matrix r u ℂ) (0 : Matrix t s ℂ) D)).eigenvalues =
      hAD.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
    exact congrArg Matrix.charpoly hgram
  rw [heig]
  exact sum_function_eigenvalues_fromBlocks _ _ _ _ hAD f

theorem gramSpectrum_sum_fromBlocks_offDiagonal
    (B : Matrix r u ℂ) (C : Matrix t s ℂ) (f : ℝ → ℝ) :
    (∑ i, f (gramSpectrum (Matrix.fromBlocks (0 : Matrix r s ℂ) B C
      (0 : Matrix t u ℂ)) i)) =
      (∑ i, f (gramSpectrum B i)) + (∑ j, f (gramSpectrum C j)) := by
  have hgram :
      Matrix.fromBlocks (0 : Matrix r s ℂ) B C (0 : Matrix t u ℂ) *
        (Matrix.fromBlocks (0 : Matrix r s ℂ) B C (0 : Matrix t u ℂ)).conjTranspose =
      Matrix.fromBlocks (B * B.conjTranspose) (0 : Matrix r t ℂ)
        (0 : Matrix t r ℂ) (C * C.conjTranspose) := by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  let hBC := (Matrix.isHermitian_mul_conjTranspose_self B).fromBlocks
    (by simp : (0 : Matrix r t ℂ).conjTranspose = (0 : Matrix t r ℂ))
    (Matrix.isHermitian_mul_conjTranspose_self C)
  change (∑ i, f ((Matrix.isHermitian_mul_conjTranspose_self
    (Matrix.fromBlocks (0 : Matrix r s ℂ) B C (0 : Matrix t u ℂ))).eigenvalues i)) = _
  have heig : (Matrix.isHermitian_mul_conjTranspose_self
      (Matrix.fromBlocks (0 : Matrix r s ℂ) B C (0 : Matrix t u ℂ))).eigenvalues =
      hBC.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
    exact congrArg Matrix.charpoly hgram
  rw [heig]
  exact sum_function_eigenvalues_fromBlocks _ _ _ _ hBC f

/-- Changing the signs of the off-diagonal blocks preserves every Gram eigenvalue. -/
theorem gramSpectrum_fromBlocks_neg
    (A : Matrix r s ℂ) (B : Matrix r u ℂ) (C : Matrix t s ℂ) (D : Matrix t u ℂ) :
    gramSpectrum (Matrix.fromBlocks A (-B) (-C) D) =
      gramSpectrum (Matrix.fromBlocks A B C D) := by
  let K : Matrix (r ⊕ t) (r ⊕ t) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hK : K * K = 1 := by
    simp [K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hgram :
      Matrix.fromBlocks A (-B) (-C) D * (Matrix.fromBlocks A (-B) (-C) D).conjTranspose =
      K * (Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D).conjTranspose) * K := by
    simp [K, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, add_comm]
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  rw [hgram]
  have hcomm := Matrix.charpoly_mul_comm K
    ((Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D).conjTranspose) * K)
  simpa [Matrix.mul_assoc, hK] using hcomm


end EC2.Entropy
