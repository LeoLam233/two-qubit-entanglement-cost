import EC2.ConcurrenceBloch

/-! # Pauli geometry on a product-kernel face

The diagonal-plus-two-corrections identity needs only the product-kernel
zero row, not the particular rank-two factorization. Complex entries are
kept in full; only the 00--11 coherence is phase-gauged to a real number.
-/

noncomputable section
open scoped ComplexConjugate

namespace EC2
namespace ConcurrenceProductKernel
open ConcurrenceAlgebra ConcurrenceBloch ConcurrenceGeometry Matrix

def density (a g d w : ℝ) (p q : ℂ) : Mat4 :=
  productKernelMatrix (a : ℂ) (g : ℂ) (d : ℂ) p (conj p) q (conj q) (w : ℂ)

def marginalA (a g d : ℝ) (p : ℂ) : Vec3 := ![2 * p.re, -2 * p.im, a-g-d]

def marginalB (a g d : ℝ) (q : ℂ) : Vec3 := ![2 * q.re, -2 * q.im, a+g-d]

theorem density_blochA (a g d w : ℝ) (p q : ℂ) :
    blochA (density a g d w p q) = marginalA a g d p := by
  funext i
  fin_cases i <;>
    simp [blochA, density, productKernelMatrix, pauliA, marginalA,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem density_blochB (a g d w : ℝ) (p q : ℂ) :
    blochB (density a g d w p q) = marginalB a g d q := by
  funext i
  fin_cases i <;>
    simp [blochB, density, productKernelMatrix, pauliB, marginalB,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem density_correlation (a g d w : ℝ) (p q : ℂ) :
    correlation (density a g d w p q) =
      !![2*w, 0, 2*p.re; 0, -2*w, -2*p.im; -2*q.re, 2*q.im, a-g+d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlation, density, productKernelMatrix, pauliA, pauliB,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem density_correlation_action (a g d w : ℝ) (p q : ℂ) (v : Vec3) :
    (correlation (density a g d w p q)).mulVec v =
      correctedAction (2*w) (a+g+d) (marginalA a g d p) (marginalB a g d q) v := by
  rw [density_correlation]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, correctedAction,
      diagAction, marginalA, marginalB, dot3] <;> ring

/-- The plane-intersection bound for the entire product-kernel matrix face.
No matrix-rank hypothesis occurs; the complex coherences remain arbitrary. -/
theorem fixed_axes_correlation (a g d w : ℝ) (p q : ℂ)
    (hw : 0 ≤ w) (hN : 2*w ≤ a+g+d) (n m : Vec3) (α β : ℝ)
    (ha : blochA (density a g d w p q) = fun i => α * n i)
    (hb : blochB (density a g d w p q) = fun i => β * m i) :
    ∃ x y : Vec3,
      sqLength x = 1 ∧ sqLength y = 1 ∧ dot3 n x = 0 ∧ dot3 m y = 0 ∧
      2*w ≤ |dot3 x ((correlation (density a g d w p q)).mulVec y)| := by
  have ha' : marginalA a g d p = fun i => α * n i := by
    rwa [density_blochA] at ha
  have hb' : marginalB a g d q = fun i => β * m i := by
    rwa [density_blochB] at hb
  obtain ⟨x,y,hx,hy,hxn,hym,hxy⟩ :=
    fixed_axes_canonical_abs_lower (2*w) (a+g+d) (mul_nonneg (by norm_num) hw) hN n m α β
  refine ⟨x,y,hx,hy,hxn,hym, ?_⟩
  rw [density_correlation_action, ha', hb']
  exact hxy

end ConcurrenceProductKernel
end EC2
