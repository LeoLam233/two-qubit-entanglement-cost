import EC2.ConcurrenceQuantum
import Mathlib.Analysis.Matrix.Spectrum

/-! # Pauli vectors and exact local-axis transport

Real three-vectors represent traceless Hermitian 2×2 observables. The
representation and unitary action are proved at the level of complex
matrix entries; norm preservation follows from determinant invariance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2
namespace Pauli
open ConcurrenceGeometry Matrix

def observable (u : Vec3) : Matrix Q Q ℂ :=
  !![(u 2 : ℂ), (u 0 : ℂ) - Complex.I * (u 1 : ℂ);
    (u 0 : ℂ) + Complex.I * (u 1 : ℂ), -(u 2 : ℂ)]

def coordinates (H : Matrix Q Q ℂ) : Vec3 :=
  ![(H 0 1).re, -(H 0 1).im, (H 0 0).re]

theorem observable_hermitian (u : Vec3) : (observable u).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observable, Matrix.conjTranspose_apply, sub_eq_add_neg]

theorem observable_trace (u : Vec3) : (observable u).trace = 0 := by
  simp [observable, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem observable_determinant (u : Vec3) : (observable u).det = -(sqLength u : ℂ) := by
  apply Complex.ext <;>
    simp [observable, Matrix.det_fin_two, sqLength, dot3, Complex.mul_re, Complex.mul_im] <;> ring

theorem observable_squared (u : Vec3) :
    observable u * observable u = (sqLength u : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [observable, Matrix.mul_apply, Fin.sum_univ_two, sqLength, dot3,
      Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem coordinates_observable (u : Vec3) : coordinates (observable u) = u := by
  funext i
  fin_cases i <;> simp [coordinates, observable]

/-- Every traceless Hermitian two-dimensional matrix is exactly one Pauli vector. -/
theorem observable_coordinates (H : Matrix Q Q ℂ)
    (hH : H.IsHermitian) (ht : H.trace = 0) : observable (coordinates H) = H := by
  have hdiag0 : (H 0 0).im = 0 := by
    have h := congrFun (congrFun hH 0) 0
    have hi := congrArg Complex.im h
    simp [Matrix.conjTranspose_apply] at hi
    linarith
  have hdiag1 : (H 1 1).im = 0 := by
    have h := congrFun (congrFun hH 1) 1
    have hi := congrArg Complex.im h
    simp [Matrix.conjTranspose_apply] at hi
    linarith
  have htrace : H 0 0 + H 1 1 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using ht
  have hoff : conj (H 0 1) = H 1 0 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hH 1) 0
  have hreal : (H 0 0).re + (H 1 1).re = 0 := by
    simpa using congrArg Complex.re htrace
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [observable, coordinates, hdiag0]
  · apply Complex.ext <;> simp [observable, coordinates]
  · change observable (coordinates H) 1 0 = H 1 0
    rw [← hoff]
    apply Complex.ext <;> simp [observable, coordinates]
  · apply Complex.ext
    · simp [observable, coordinates]
      linarith
    · simp [observable, coordinates, hdiag1]

theorem observable_injective : Function.Injective observable := by
  intro u v h
  simpa using congrArg coordinates h

/-- The standard adjoint action of a qubit unitary on a real Pauli vector. -/
def rotation (U : Matrix.unitaryGroup Q ℂ) (u : Vec3) : Vec3 :=
  coordinates (U.val * observable u * U.val.conjTranspose)

/-- Rotation coordinates represent the actual conjugated observable. -/
theorem observable_rotation (U : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    observable (rotation U u) = U.val * observable u * U.val.conjTranspose := by
  apply observable_coordinates
  · exact Matrix.isHermitian_mul_mul_conjTranspose U.val (observable_hermitian u)
  · have hU : U.val.conjTranspose * U.val = 1 := U.prop.1
    rw [Matrix.trace_mul_cycle, hU, one_mul, observable_trace]

theorem det_unitary_conjugate (U : Matrix.unitaryGroup Q ℂ) (H : Matrix Q Q ℂ) :
    (U.val * H * U.val.conjTranspose).det = H.det := by
  calc
    (U.val * H * U.val.conjTranspose).det = H.det * (U.val * U.val.conjTranspose).det := by
      simp only [Matrix.det_mul]
      ring
    _ = H.det := by
      have hU : U.val * U.val.conjTranspose = 1 := U.prop.2
      rw [hU, Matrix.det_one, mul_one]

/-- Unitary conjugation preserves the Euclidean length of the Pauli vector. -/
theorem rotation_sqLength (U : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    sqLength (rotation U u) = sqLength u := by
  have h := congrArg Matrix.det (observable_rotation U u)
  rw [observable_determinant, det_unitary_conjugate, observable_determinant] at h
  exact_mod_cast neg_injective h

theorem observable_add (u v : Vec3) : observable (u+v) = observable u + observable v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observable, Matrix.add_apply] <;> ring

theorem observable_smul (a : ℝ) (u : Vec3) :
    observable (a • u) = (a : ℂ) • observable u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observable, Matrix.smul_apply] <;> ring

theorem rotation_add (U : Matrix.unitaryGroup Q ℂ) (u v : Vec3) :
    rotation U (u+v) = rotation U u + rotation U v := by
  apply observable_injective
  simp only [observable_rotation, observable_add, Matrix.mul_add, Matrix.add_mul]

theorem rotation_smul (U : Matrix.unitaryGroup Q ℂ) (a : ℝ) (u : Vec3) :
    rotation U (a • u) = a • rotation U u := by
  apply observable_injective
  simp only [observable_rotation, observable_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem rotation_dot (U : Matrix.unitaryGroup Q ℂ) (u v : Vec3) :
    dot3 (rotation U u) (rotation U v) = dot3 u v := by
  have h := rotation_sqLength U (u+v)
  rw [rotation_add] at h
  have hu := rotation_sqLength U u
  have hv := rotation_sqLength U v
  simp only [sqLength, dot3, Pi.add_apply] at h hu hv ⊢
  nlinarith only [h, hu, hv]


@[simp] theorem rotation_one (u : Vec3) : rotation 1 u = u := by
  apply observable_injective
  simp [observable_rotation]

theorem rotation_comp (U V : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    rotation V (rotation U u) = rotation (V * U) u := by
  apply observable_injective
  rw [observable_rotation, observable_rotation, observable_rotation]
  change V.val * (U.val * observable u * U.val.conjTranspose) * V.val.conjTranspose =
    (V.val * U.val) * observable u * (V.val * U.val).conjTranspose
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

@[simp] theorem rotation_inverse (U : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    rotation U⁻¹ (rotation U u) = u := by
  rw [rotation_comp, inv_mul_cancel, rotation_one]

@[simp] theorem rotation_inverse' (U : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    rotation U (rotation U⁻¹ u) = u := by
  rw [rotation_comp, mul_inv_cancel, rotation_one]

end Pauli
end EC2
