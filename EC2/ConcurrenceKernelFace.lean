import EC2.ConcurrenceGram
import EC2.ConcurrenceProductKernel
import EC2.ConcurrenceExpectations

/-! # Fixed-axis inequality on the normalized product-kernel face -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace EC2
open ConcurrenceGeometry ConcurrenceBloch

/-- A zero diagonal entry of a positive state annihilates the corresponding
column and row, without any invertibility or strict-positivity condition. -/
theorem state_zero_column_row (ρ : MState (Q × Q)) (a : Q × Q)
    (ha : ρ.m a a = 0) : (∀ b, ρ.m b a = 0) ∧ (∀ b, ρ.m a b = 0) := by
  have hq : star (Pi.single a (1 : ℂ)) ⬝ᵥ ρ.m.mulVec (Pi.single a 1) = 0 := by
    simpa using ha
  have hv := ρ.psd.dotProduct_mulVec_zero_iff.mp hq
  have hc : ∀ b, ρ.m b a = 0 := by
    intro b
    simpa using congrFun hv b
  refine ⟨hc, ?_⟩
  intro b
  have h := congrFun (congrFun ρ.Hermitian a) b
  simpa [Matrix.conjTranspose_apply, hc b] using h.symm

theorem state_diagonal_im_zero (ρ : MState (Q × Q)) (a : Q × Q) :
    (ρ.m a a).im = 0 := by
  have h := congrArg Complex.im (congrFun (congrFun ρ.Hermitian a) a)
  simp [Matrix.conjTranspose_apply] at h
  linarith

/-- An actual state with zero |01〉 population has exactly the product-kernel
matrix representation, once its 00--11 coherence is real. -/
theorem state_product_kernel_matrix (ρ : MState (Q × Q))
    (hzero : ρ.m (0,1) (0,1) = 0) (hw : (ρ.m (0,0) (1,1)).im = 0) :
    twoQubitMatrix ρ = ConcurrenceProductKernel.density
      (ρ.m (0,0) (0,0)).re (ρ.m (1,0) (1,0)).re (ρ.m (1,1) (1,1)).re
      (ρ.m (0,0) (1,1)).re (ρ.m (0,0) (1,0)) (ρ.m (1,0) (1,1)) := by
  obtain ⟨hc,hr⟩ := state_zero_column_row ρ (0,1) hzero
  have hstar (a b : Q × Q) : conj (ρ.m b a) = ρ.m a b := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun ρ.Hermitian a) b
  have hreal (a : Q × Q) : ((ρ.m a a).re : ℂ) = ρ.m a a := by
    apply Complex.ext <;> simp [state_diagonal_im_zero]
  have hwreal : ((ρ.m (0,0) (1,1)).re : ℂ) = ρ.m (0,0) (1,1) := by
    apply Complex.ext <;> simp [hw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoQubitMatrix, twoQubitIndex, ConcurrenceProductKernel.density,
      ConcurrenceAlgebra.productKernelMatrix, hreal, hwreal, hc, hr, hstar]
  have h := hstar (1,1) (0,0)
  rw [← hwreal] at h
  calc
    ρ.m (1,1) (0,0) = ((ρ.m (0,0) (1,1)).re : ℂ) := by simpa using h.symm
    _ = _ := hwreal

/-- Positivity bounds twice a real 00--11 coherence by the total mass of
the product-kernel matrix. This includes endpoint and singular states. -/
theorem product_kernel_coherence_le_mass (ρ : MState (Q × Q))
    (hw : (ρ.m (0,0) (1,1)).im = 0) :
    2 * (ρ.m (0,0) (1,1)).re ≤
      (ρ.m (0,0) (0,0)).re + (ρ.m (1,0) (1,0)).re + (ρ.m (1,1) (1,1)).re := by
  have hpos := ρ.psd.re_dotProduct_nonneg
    (fun ab : Q × Q => (!![1,0;0,-1] : Matrix Q Q ℂ) ab.1 ab.2)
  have hstar : conj (ρ.m (0,0) (1,1)) = ρ.m (1,1) (0,0) := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun ρ.Hermitian (1,1)) (0,0)
  have hg : 0 ≤ (ρ.m (1,0) (1,0)).re := (Complex.nonneg_iff.mp ρ.psd.diag_nonneg).1
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, ← hstar] at hpos
  linarith

/-- Equation (13) on the real-coherence product-kernel face, proved for
actual states of every rank at most two and every allowed fixed axis pair. -/
theorem fixed_axis_concurrence_zero_diagonal_real (ρ : MState (Q × Q))
    (hrank : ρ.m.rank ≤ 2) (hzero : ρ.m (0,1) (0,1) = 0)
    (hwreal : (ρ.m (0,0) (1,1)).im = 0)
    (hwpos : 0 ≤ (ρ.m (0,0) (1,1)).re)
    (n m : Vec3) (ha : IsMarginalAxis (marginalBlochA ρ) n)
    (hb : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  have hrep := state_product_kernel_matrix ρ hzero hwreal
  obtain ⟨_,α,hα⟩ := ha
  obtain ⟨_,β,hβ⟩ := hb
  have ha' : blochA (ConcurrenceProductKernel.density
      (ρ.m (0,0) (0,0)).re (ρ.m (1,0) (1,0)).re (ρ.m (1,1) (1,1)).re
      (ρ.m (0,0) (1,1)).re (ρ.m (0,0) (1,0)) (ρ.m (1,0) (1,1))) =
      fun i => α * n i := by
    simpa only [marginalBlochA, hrep] using hα
  have hb' : blochB (ConcurrenceProductKernel.density
      (ρ.m (0,0) (0,0)).re (ρ.m (1,0) (1,0)).re (ρ.m (1,1) (1,1)).re
      (ρ.m (0,0) (1,1)).re (ρ.m (0,0) (1,0)) (ρ.m (1,0) (1,1))) =
      fun i => β * m i := by
    simpa only [marginalBlochB, hrep] using hβ
  obtain ⟨u,v,hu,hv,hun,hvm,hcorr⟩ :=
    ConcurrenceProductKernel.fixed_axes_correlation _ _ _ _ _ _ hwpos
      (product_kernel_coherence_le_mass ρ hwreal) n m α β ha' hb'
  have hC := concurrence_le_twice_coherence_of_zero_diagonal ρ hrank hzero
  have hnorm : ‖ρ.m (0,0) (1,1)‖ = (ρ.m (0,0) (1,1)).re := by
    have he : ρ.m (0,0) (1,1) = ((ρ.m (0,0) (1,1)).re : ℂ) := by
      apply Complex.ext <;> simp [hwreal]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwpos]
    simp
  rw [hnorm] at hC
  apply hC.trans
  apply le_transverseBound_of_witness ρ n m u v _ hu hv hun hvm
  simpa only [correlationMatrix, hrep] using hcorr

end EC2
