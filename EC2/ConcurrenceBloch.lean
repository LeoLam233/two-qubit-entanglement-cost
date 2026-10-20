import EC2.ConcurrenceAlgebra
import EC2.ConcurrenceGeometry
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Canonical two-qubit states and their Pauli correlations

The matrix basis is 00,01,10,11.  These proofs connect the geometric lemmas
to actual Pauli traces, rather than defining the desired traces by their
claimed coordinate formulas.
-/

namespace EC2
namespace ConcurrenceBloch

noncomputable section
open Matrix ConcurrenceAlgebra ConcurrenceGeometry
open scoped ComplexConjugate

def pauliA : Fin 3 → Mat4 :=
  ![!![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,-Complex.I,0; 0,0,0,-Complex.I; Complex.I,0,0,0; 0,Complex.I,0,0],
    !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]]

def pauliB : Fin 3 → Mat4 :=
  ![!![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0],
    !![0,-Complex.I,0,0; Complex.I,0,0,0; 0,0,0,-Complex.I; 0,0,Complex.I,0],
    !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1]]

def blochA (ρ : Mat4) : Vec3 := fun i => (Matrix.trace (ρ * pauliA i)).re

def blochB (ρ : Mat4) : Vec3 := fun i => (Matrix.trace (ρ * pauliB i)).re

def correlation (ρ : Mat4) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (Matrix.trace (ρ * pauliA i * pauliB j)).re

def canonicalDensity (L u v s t r : ℝ) : Mat4 :=
  let Z := canonicalFactor (L : ℂ) ((u : ℂ) + Complex.I * (v : ℂ)) (s : ℂ) (t : ℂ) (r : ℂ)
  Z * Z.conjTranspose

def canonicalMass (L u v s t r : ℝ) : ℝ :=
  L ^ 2 + u ^ 2 + v ^ 2 + s ^ 2 + t ^ 2 + r ^ 2

def canonicalA (L u v s t r : ℝ) : Vec3 :=
  ![2 * L * u, 2 * L * v, 2 * L ^ 2 - canonicalMass L u v s t r]

def canonicalB (L u v s t r : ℝ) : Vec3 :=
  ![2 * (t * u + s * r), -2 * t * v,
    canonicalMass L u v s t r - 2 * (t ^ 2 + r ^ 2)]

/-- The normalization N in EC2 §3.1 is the actual matrix trace. -/
theorem canonicalDensity_trace (L u v s t r : ℝ) :
    (Matrix.trace (canonicalDensity L u v s t r)).re = canonicalMass L u v s t r := by
  simp [canonicalDensity, canonicalFactor, canonicalMass, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Complex.star_def, Complex.mul_re, Complex.mul_im]
  ring

/-- First marginal Bloch vector, EC2 Eq. (16). -/
theorem canonicalDensity_blochA (L u v s t r : ℝ) :
    blochA (canonicalDensity L u v s t r) = canonicalA L u v s t r := by
  funext i
  fin_cases i <;>
    simp [blochA, pauliA, canonicalDensity, canonicalFactor, canonicalA,
      canonicalMass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring

/-- Second marginal Bloch vector, EC2 Eq. (16). -/
theorem canonicalDensity_blochB (L u v s t r : ℝ) :
    blochB (canonicalDensity L u v s t r) = canonicalB L u v s t r := by
  funext i
  fin_cases i <;>
    simp [blochB, pauliB, canonicalDensity, canonicalFactor, canonicalB,
      canonicalMass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring

/-- The complete 3×3 Pauli correlation matrix, EC2 Eq. (17). -/
theorem canonicalDensity_correlation (L u v s t r : ℝ) :
    correlation (canonicalDensity L u v s t r) =
      !![2 * L * t, 0, 2 * L * u;
         0, -2 * L * t, 2 * L * v;
         -2 * (t * u + s * r), 2 * t * v,
           2 * (L ^ 2 + t ^ 2 + r ^ 2) - canonicalMass L u v s t r] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlation, pauliA, pauliB, canonicalDensity, canonicalFactor,
      canonicalMass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual canonical correlation matrix has the diagonal-plus-two-
corrections action required by the fixed-axis geometric proof. -/
theorem canonical_correlation_action (L u v s t r : ℝ) (w : Vec3) :
    (correlation (canonicalDensity L u v s t r)).mulVec w =
      correctedAction (2 * L * t) (canonicalMass L u v s t r)
        (canonicalA L u v s t r) (canonicalB L u v s t r) w := by
  rw [canonicalDensity_correlation]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, correctedAction,
      diagAction, canonicalA, canonicalB, dot3] <;> ring

/-- The fixed-axis estimate for the actual canonical density matrix.  The
trace is left unnormalized, exactly as in EC2 §3.1. -/
theorem canonical_fixed_axes_correlation (L u v s t r : ℝ)
    (hL : 0 ≤ L) (ht : 0 ≤ t) (n m : Vec3) (α β : ℝ)
    (ha : blochA (canonicalDensity L u v s t r) = fun i => α * n i)
    (hb : blochB (canonicalDensity L u v s t r) = fun i => β * m i) :
    ∃ x y : Vec3,
      sqLength x = 1 ∧ sqLength y = 1 ∧ dot3 n x = 0 ∧ dot3 m y = 0 ∧
      2 * L * t ≤ |dot3 x ((correlation (canonicalDensity L u v s t r)).mulVec y)| := by
  have hc : 0 ≤ 2 * L * t := mul_nonneg (mul_nonneg (by norm_num) hL) ht
  have hmass : 2 * L * t ≤ canonicalMass L u v s t r :=
    canonical_concurrence_le_trace L u v s t r
  have hae : canonicalA L u v s t r = fun i => α * n i := by
    rwa [canonicalDensity_blochA] at ha
  have hbe : canonicalB L u v s t r = fun i => β * m i := by
    rwa [canonicalDensity_blochB] at hb
  obtain ⟨x, y, hx, hy, hxn, hym, hxy⟩ :=
    fixed_axes_canonical_abs_lower (2 * L * t) (canonicalMass L u v s t r) hc hmass n m α β
  refine ⟨x, y, hx, hy, hxn, hym, ?_⟩
  rw [canonical_correlation_action, hae, hbe]
  exact hxy

end
end ConcurrenceBloch
end EC2
