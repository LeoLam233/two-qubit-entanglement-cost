import EC2.ConcurrencePauli

/-! # A unitary measurement basis for every prescribed unit axis -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2
namespace Pauli
open ConcurrenceGeometry Matrix

def zAxis : Vec3 := ![0,0,1]

theorem observable_zAxis : observable zAxis = Qubit.Z.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [observable, zAxis, Qubit.Z]

/-- Every prescribed unit Bloch axis has a unitary measurement basis with
+1 at the first basis vector and -1 at the second. The basis is obtained
from the actual Hermitian spectral theorem; no nonzero marginal is used. -/
theorem exists_axis_unitary (n : Vec3) (hn : sqLength n = 1) :
    ∃ U : Matrix.unitaryGroup Q ℂ, rotation U zAxis = n := by
  let hH := observable_hermitian n
  let W := hH.eigenvectorUnitary
  let a : ℝ := hH.eigenvalues 0
  let b : ℝ := hH.eigenvalues 1
  have hsum : a + b = 0 := by
    have h := hH.sum_eigenvalues_eq_trace
    rw [observable_trace] at h
    simpa [a, b, Fin.sum_univ_two] using congrArg Complex.re h
  have hprod : a * b = -1 := by
    have h := hH.det_eq_prod_eigenvalues
    rw [observable_determinant, hn] at h
    simpa [a, b, Fin.prod_univ_two, Complex.mul_re] using congrArg Complex.re h.symm
  have hcases : a = 1 ∨ a = -1 := by
    have hscaled := congrArg (fun x : ℝ => a*x) hsum
    have hmul : (a-1)*(a+1) = 0 := by nlinarith only [hscaled, hprod]
    rcases mul_eq_zero.mp hmul with h | h
    · left; linarith
    · right; linarith
  have hspec : observable n = W.val *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * W.val.conjTranspose := by
    have h := hH.spectral_theorem
    change observable n = W.val *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * W.val.conjTranspose at h
    exact h
  rcases hcases with ha | ha
  · have hb : b = -1 := by linarith
    change hH.eigenvalues 0 = 1 at ha
    change hH.eigenvalues 1 = -1 at hb
    have hd : Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) = observable zAxis := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal_apply, observable, zAxis, ha, hb]
    refine ⟨W, observable_injective ?_⟩
    rw [observable_rotation, ← hd]
    exact hspec.symm
  · have hb : b = 1 := by linarith
    change hH.eigenvalues 0 = -1 at ha
    change hH.eigenvalues 1 = 1 at hb
    have hd : Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) =
        Qubit.X.val * observable zAxis * Qubit.X.val.conjTranspose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal_apply, observable, zAxis, Qubit.X,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          ha, hb]
    refine ⟨W * Qubit.X, observable_injective ?_⟩
    rw [observable_rotation]
    change (W.val * Qubit.X.val) * observable zAxis *
      (W.val * Qubit.X.val).conjTranspose = observable n
    rw [Matrix.conjTranspose_mul, hspec, hd]
    simp only [Matrix.mul_assoc]

/-- An equivalent statement convenient for projective measurement formulas. -/
theorem exists_axis_measurement_basis (n : Vec3) (hn : sqLength n = 1) :
    ∃ U : Matrix.unitaryGroup Q ℂ,
      observable n = U.val * Qubit.Z.val * U.val.conjTranspose := by
  obtain ⟨U,hU⟩ := exists_axis_unitary n hn
  refine ⟨U, ?_⟩
  rw [← observable_zAxis, ← observable_rotation, hU]

end Pauli
end EC2
