import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite matrix algebra for the EC2 concurrence proof

This file verifies the polynomial identities used before the spectral and
convex-roof arguments.  The polynomial statements are intentionally stronger
than their positive-semidefinite specializations.  They do not assert the
remaining passage from characteristic roots to mixed-state concurrence.
-/

namespace EC2
namespace ConcurrenceAlgebra

noncomputable section

open Matrix

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- σ_y ⊗ σ_y, in the computational order 00,01,10,11. -/
def spinFlipJ : Mat4 :=
  !![0, 0, 0, -1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

theorem spinFlipJ_squared : spinFlipJ * spinFlipJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinFlipJ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- The canonical rank-two factor, with the complex entry kept arbitrary. -/
def canonicalFactor (L z s t r : ℂ) : Matrix (Fin 4) (Fin 2) ℂ :=
  !![L, 0;
     0, 0;
     z, s;
     t, r]

/-- EC2 Eq. (15), valid before imposing reality or sign restrictions. -/
theorem canonical_spin_flip (L z s t r : ℂ) :
    (canonicalFactor L z s t r).transpose * spinFlipJ * canonicalFactor L z s t r =
      !![-2 * L * t, -L * r; -L * r, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalFactor, spinFlipJ, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> ring

def productKernelMatrix (a g d p p' q q' w : ℂ) : Mat4 :=
  !![a, 0, p, w;
     0, 0, 0, 0;
     p', 0, g, q;
     w, 0, q', d]

/-- On a Hermitian state, transpose equals entrywise complex conjugation,
so this polynomial expression is the physical spin flip. -/
def transposeSpinFlip (R : Mat4) : Mat4 := spinFlipJ * R.transpose * spinFlipJ

/-- The characteristic determinant in optional constructive proof C. -/
theorem product_kernel_characteristic (a g d p p' q q' w lam : ℂ) :
    Matrix.det (lam • (1 : Mat4) -
      productKernelMatrix a g d p p' q q' w *
        transposeSpinFlip (productKernelMatrix a g d p p' q q' w)) =
      lam ^ 2 * ((lam - a * d - w ^ 2) ^ 2 - 4 * a * d * w ^ 2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, productKernelMatrix,
    transposeSpinFlip, spinFlipJ, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMul, dotProduct,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_succ,
    Fin.succAbove]
  ring

/-- The scalar factorization behind the two potentially nonzero
spin-flip roots. -/
theorem product_kernel_quadratic_factor (a d w lam : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (lam - a * d - w ^ 2) ^ 2 - 4 * a * d * w ^ 2 =
      (lam - (Real.sqrt (a * d) + w) ^ 2) *
      (lam - (Real.sqrt (a * d) - w) ^ 2) := by
  have hs : Real.sqrt (a * d) ^ 2 = a * d := Real.sq_sqrt (mul_nonneg ha hd)
  rw [show 4 * a * d * w ^ 2 = 4 * (a * d) * w ^ 2 by ring]
  generalize Real.sqrt (a * d) = q at hs ⊢
  rw [← hs]
  ring

/-- If positivity has supplied `w ≤ √(a d)`, the two scalar roots are
ordered and nonnegative, and their difference is exactly `2w`. -/
theorem product_kernel_root_difference (a d w : ℝ)
    (hw : 0 ≤ w) (hupper : w ≤ Real.sqrt (a * d)) :
    0 ≤ Real.sqrt (a * d) - w ∧
    Real.sqrt (a * d) - w ≤ Real.sqrt (a * d) + w ∧
    (Real.sqrt (a * d) + w) - (Real.sqrt (a * d) - w) = 2 * w := by
  constructor
  · linarith
  constructor
  · linarith
  · ring

/-- Scalar estimate used on the real zero face: the largest absolute
eigenvalue cannot exceed half the absolute sum when the trace vanishes. -/
theorem traceless_four_concurrence_zero (μ : Fin 4 → ℝ)
    (htrace : μ 0 + μ 1 + μ 2 + μ 3 = 0) (i : Fin 4) :
    max 0 (2 * |μ i| - (|μ 0| + |μ 1| + |μ 2| + |μ 3|)) = 0 := by
  have hbound (j : Fin 4) :
      2 * |μ j| ≤ |μ 0| + |μ 1| + |μ 2| + |μ 3| := by
    fin_cases j <;> dsimp only
    · change 2 * |μ 0| ≤ |μ 0| + |μ 1| + |μ 2| + |μ 3|
      have h : μ 0 = -(μ 1 + μ 2 + μ 3) := by linarith
      have ht := abs_add_le (μ 1 + μ 2) (μ 3)
      have ht' := abs_add_le (μ 1) (μ 2)
      rw [h, abs_neg]
      linarith
    · change 2 * |μ 1| ≤ |μ 0| + |μ 1| + |μ 2| + |μ 3|
      have h : μ 1 = -(μ 0 + μ 2 + μ 3) := by linarith
      have ht := abs_add_le (μ 0 + μ 2) (μ 3)
      have ht' := abs_add_le (μ 0) (μ 2)
      rw [h, abs_neg]
      linarith
    · change 2 * |μ 2| ≤ |μ 0| + |μ 1| + |μ 2| + |μ 3|
      have h : μ 2 = -(μ 0 + μ 1 + μ 3) := by linarith
      have ht := abs_add_le (μ 0 + μ 1) (μ 3)
      have ht' := abs_add_le (μ 0) (μ 1)
      rw [h, abs_neg]
      linarith
    · change 2 * |μ 3| ≤ |μ 0| + |μ 1| + |μ 2| + |μ 3|
      have h : μ 3 = -(μ 0 + μ 1 + μ 2) := by linarith
      have ht := abs_add_le (μ 0 + μ 1) (μ 2)
      have ht' := abs_add_le (μ 0) (μ 1)
      rw [h, abs_neg]
      linarith
  exact max_eq_left (by linarith [hbound i])

end
end ConcurrenceAlgebra
end EC2
