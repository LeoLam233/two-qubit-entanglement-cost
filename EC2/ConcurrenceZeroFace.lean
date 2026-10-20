import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constructive zero-diagonal bases in the two-qubit zero face

A real symmetric trace-zero matrix of order four has a real orthonormal basis
whose four quadratic forms all vanish. In this fixed dimension, diagonalizing
and applying the real Hadamard matrix gives a direct construction, so no
induction on dimension or intermediate-value argument is needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace EC2.ConcurrenceZeroFace

abbrev RealMat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The real normalized Walsh–Hadamard matrix in dimension four. -/
def hadamard4 : RealMat4 :=
  !![1/2, 1/2, 1/2, 1/2;
     1/2, -1/2, 1/2, -1/2;
     1/2, 1/2, -1/2, -1/2;
     1/2, -1/2, -1/2, 1/2]

/-- All sixteen squared entries equal one quarter. -/
theorem hadamard4_entry_sq (i j : Fin 4) : hadamard4 i j ^ 2 = 1/4 := by
  fin_cases i <;> fin_cases j <;> norm_num [hadamard4]

/-- The Hadamard change of basis is real orthogonal. -/
theorem hadamard4_mul_adjoint : hadamard4 * hadamard4ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard4, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

/-- The orthogonal matrix bundled as a real unitary for the spectral API. -/
def hadamardUnitary : Matrix.unitaryGroup (Fin 4) ℝ :=
  ⟨hadamard4, Matrix.mem_unitaryGroup_iff.mpr hadamard4_mul_adjoint⟩

/-- Hadamard mixing makes every diagonal entry the arithmetic mean of the spectrum. -/
theorem hadamard_diagonal_average (d : Fin 4 → ℝ) (j : Fin 4) :
    (hadamard4ᴴ * Matrix.diagonal d * hadamard4) j j = (∑ i, d i) / 4 := by
  fin_cases j <;>
    simp [hadamard4, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.diagonal_apply] <;> ring

/--
Every real symmetric matrix of order four with zero trace admits an orthogonal
basis in which all four diagonal quadratic forms are exactly zero.
-/
theorem exists_orthogonal_zero_diagonal (A : RealMat4) (hA : A.IsHermitian)
    (htrace : A.trace = 0) :
    ∃ U : Matrix.unitaryGroup (Fin 4) ℝ,
      ∀ j : Fin 4, ((U : RealMat4)ᴴ * A * (U : RealMat4)) j j = 0 := by
  let V := hA.eigenvectorUnitary
  let U := V * hadamardUnitary
  have hdiag : (V : RealMat4)ᴴ * A * (V : RealMat4) =
      Matrix.diagonal hA.eigenvalues := by
    simpa only [V, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hconj : (U : RealMat4)ᴴ * A * (U : RealMat4) =
      hadamard4ᴴ * Matrix.diagonal hA.eigenvalues * hadamard4 := by
    change ((V : RealMat4) * hadamard4)ᴴ * A * ((V : RealMat4) * hadamard4) = _
    rw [Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using
      congrArg (fun Z : RealMat4 => hadamard4ᴴ * Z * hadamard4) hdiag
  have hsum : (∑ i, hA.eigenvalues i) = 0 := by
    have ht := hA.trace_eq_sum_eigenvalues
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using ht.symm.trans htrace
  refine ⟨U, fun j => ?_⟩
  rw [hconj, hadamard_diagonal_average, hsum, zero_div]

/-- The real spin-flip bilinear form, in the computational order 00,01,10,11. -/
def realSpinJ : RealMat4 :=
  !![0, 0, 0, -1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

theorem realSpinJ_hermitian : realSpinJ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realSpinJ, Matrix.conjTranspose_apply]

/-- A real column is spin-isotropic exactly when its two-qubit determinant vanishes. -/
theorem realSpinJ_column (X : RealMat4) (j : Fin 4) :
    (Xᴴ * realSpinJ * X) j j = -2 * (X 0 j * X 3 j - X 1 j * X 2 j) := by
  simp [realSpinJ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  ring

open scoped MatrixOrder in
/--
A real positive semidefinite matrix with zero spin trace has an exact real
factorization into four columns of determinant zero, including zero columns.
-/
theorem exists_real_zero_determinant_factor (A : RealMat4) (hA : A.PosSemidef)
    (hspin : (A * realSpinJ).trace = 0) :
    ∃ X : RealMat4, X * Xᴴ = A ∧
      ∀ j : Fin 4, X 0 j * X 3 j - X 1 j * X 2 j = 0 := by
  obtain ⟨T, hT⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let R : RealMat4 := Tᴴ
  have hR : R * Rᴴ = A := by
    simpa only [R, Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose] using hT.symm
  let S : RealMat4 := Rᴴ * realSpinJ * R
  have hS : S.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul R realSpinJ_hermitian
  have htr : S.trace = 0 := by
    change (Rᴴ * realSpinJ * R).trace = 0
    rw [Matrix.trace_mul_cycle, hR]
    exact hspin
  obtain ⟨U, hU⟩ := exists_orthogonal_zero_diagonal S hS htr
  let X : RealMat4 := R * (U : RealMat4)
  have hUU : (U : RealMat4) * (U : RealMat4)ᴴ = 1 := Unitary.coe_mul_star_self U
  refine ⟨X, ?_, ?_⟩
  · change (R * (U : RealMat4)) * (R * (U : RealMat4))ᴴ = A
    rw [Matrix.conjTranspose_mul]
    calc
      R * (U : RealMat4) * ((U : RealMat4)ᴴ * Rᴴ) =
          R * ((U : RealMat4) * (U : RealMat4)ᴴ) * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hUU, Matrix.mul_one, hR]
  · intro j
    have hconj : Xᴴ * realSpinJ * X = (U : RealMat4)ᴴ * S * (U : RealMat4) := by
      change (R * (U : RealMat4))ᴴ * realSpinJ * (R * (U : RealMat4)) = _
      simp only [Matrix.conjTranspose_mul, S, Matrix.mul_assoc]
    have hz := hU j
    rw [← hconj, realSpinJ_column] at hz
    linarith

/-- The real zero-antidiagonal face has zero spin trace, at every rank. -/
theorem spin_trace_zero_of_antidiagonal (A : RealMat4) (hA : A.IsHermitian)
    (hw : A 0 3 = 0) (hz : A 1 2 = 0) : (A * realSpinJ).trace = 0 := by
  have hw' : A 3 0 = 0 := by simpa using (hA.apply 0 3).trans hw
  have hz' : A 2 1 = 0 := by simpa using (hA.apply 1 2).trans hz
  simp [Matrix.trace, Matrix.mul_apply, realSpinJ, Fin.sum_univ_succ, hw, hz, hw', hz']

/-- Explicit determinant-zero-column decomposition of every real zero-antidiagonal state. -/
theorem exists_real_zero_face_factor (A : RealMat4) (hA : A.PosSemidef)
    (hw : A 0 3 = 0) (hz : A 1 2 = 0) :
    ∃ X : RealMat4, X * Xᴴ = A ∧
      ∀ j : Fin 4, X 0 j * X 3 j - X 1 j * X 2 j = 0 :=
  exists_real_zero_determinant_factor A hA (spin_trace_zero_of_antidiagonal A hA.1 hw hz)

end EC2.ConcurrenceZeroFace
