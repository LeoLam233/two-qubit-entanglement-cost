import EC2.ConcurrenceAlignment
import EC2.ConcurrenceFactor

/-! # Constructive concurrence bound on a rank-two product-kernel face

An explicit right unitary aligns the first row of a two-column Gram factor.
Only one column can then have a nonzero determinant. The bound follows
directly from the ordinary convex roof, including rank-one and zero-column
cases, without the Wootters spectral formula.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2

/-- Every normalized Gram factor gives the expected pure-column ensemble
upper bound for the actual concurrence convex roof. -/
theorem concurrence_le_gram_columns {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : MState (Q × Q)) (Z : Matrix (Q × Q) ι ℂ)
    (hZ : Z * Z.conjTranspose = ρ.m) :
    concurrence ρ ≤ ∑ j, 2 * ‖Z (0,0) j * Z (1,1) j - Z (0,1) j * Z (1,0) j‖ := by
  have he (z : ℂ) : (z * conj z).re = Complex.normSq z := by
    rw [Complex.mul_conj]
    rfl
  have hnorm : ∑ j, ∑ ab : Q × Q, ‖Z ab j‖ ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Q × Q) (Q × Q) ℂ => M.trace.re) hZ
    rw [ρ.tr'] at h
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def, he, Complex.normSq_eq_norm_sq, Complex.one_re] at h
    rwa [Finset.sum_comm] at h
  let ψ : Ket (ι × (Q × Q)) :=
    { vec := fun ja => Z ja.2 ja.1
      normalized' := by simpa [Fintype.sum_prod_type] using hnorm }
  have hρ : (MState.pure ψ).traceLeft = ρ := by
    apply MState.ext_m
    ext ab cd
    change (∑ j, Z ab j * conj (Z cd j)) = ρ.m ab cd
    exact congrFun (congrFun hZ ab) cd
  rw [← hρ]
  exact concurrence_traceLeft_le_column_determinants ψ

/-- The zero diagonal of a Gram matrix annihilates the entire associated
factor row. Here two columns suffice for every state of rank at most two. -/
theorem gram_two_row_zero (Z : Matrix (Q × Q) Q ℂ) (a : Q × Q)
    (h : (Z * Z.conjTranspose) a a = 0) : ∀ j, Z a j = 0 := by
  have hs : Complex.normSq (Z a 0) + Complex.normSq (Z a 1) = 0 := by
    have hr := congrArg Complex.re h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply] using hr
  have h0 := Complex.normSq_nonneg (Z a 0)
  have h1 := Complex.normSq_nonneg (Z a 1)
  have hz0 : Complex.normSq (Z a 0) = 0 := by linarith
  have hz1 : Complex.normSq (Z a 1) = 0 := by linarith
  intro j
  fin_cases j
  · exact Complex.normSq_eq_zero.mp hz0
  · exact Complex.normSq_eq_zero.mp hz1

/-- Rank-at-most-two states whose |01〉 vector lies in the kernel satisfy
C(ρ)≤2|ρ00,11| by an explicit two-column pure-state ensemble. -/
theorem concurrence_le_twice_coherence_of_zero_diagonal
    (ρ : MState (Q × Q)) (hrank : ρ.m.rank ≤ 2)
    (hzero : ρ.m (0,1) (0,1) = 0) :
    concurrence ρ ≤ 2 * ‖ρ.m (0,0) (1,1)‖ := by
  obtain ⟨Z,hZ⟩ := ConcurrenceReduction.exists_rank_le_factor ρ.M ρ.nonneg hrank
  have hz : ∀ j, Z (0,1) j = 0 :=
    gram_two_row_zero Z (0,1) (by rw [hZ]; exact hzero)
  obtain ⟨U,hU⟩ := exists_qubit_row_alignment (fun j => Z (0,0) j)
  let R := Z * U.val
  have hR : R * R.conjTranspose = ρ.m := by
    have hUU : U.val * U.val.conjTranspose = 1 := U.prop.2
    dsimp [R]
    rw [Matrix.conjTranspose_mul]
    calc
      Z * U.val * (U.val.conjTranspose * Z.conjTranspose) =
          Z * (U.val * U.val.conjTranspose) * Z.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = ρ.m := by rw [hUU, Matrix.mul_one, hZ]; rfl
  have hzR : ∀ j, R (0,1) j = 0 := by
    intro j
    simp [R, Matrix.mul_apply, hz]
  have hR01 : R (0,0) 1 = 0 := by
    simpa [R, Matrix.mul_apply, Fin.sum_univ_two] using hU
  have hw : R (0,0) 0 * conj (R (1,1) 0) = ρ.m (0,0) (1,1) := by
    have h := congrFun (congrFun hR (0,0)) (1,1)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, hR01] using h
  have hbound := concurrence_le_gram_columns ρ R hR
  have hcost : (∑ j : Q, 2 * ‖R (0,0) j * R (1,1) j - R (0,1) j * R (1,0) j‖) =
      2 * ‖ρ.m (0,0) (1,1)‖ := by
    simp [Fin.sum_univ_two, hzR, hR01, ← hw, norm_mul]
  rwa [hcost] at hbound

end EC2
