import EC2.ConcurrenceZeroFace
import EC2.ConcurrenceCanonical

/-!
# The real two-qubit zero face has zero actual convex-roof concurrence

The real factor constructed by the Hadamard argument is converted into a
normalized purification. Its conditional ensemble consists of columns of
zero determinant. The actual defining convex roof therefore vanishes, with
zero columns handled by the existing conditional-ensemble infrastructure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace EC2.ConcurrenceZeroFace

/-- Taking real parts of a complex positive matrix preserves real positivity. -/
theorem realPart_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.PosSemidef) : (M.map Complex.re).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def]
      using congrArg Complex.re (hM.1.apply i j)
  · intro x
    have h := hM.re_dotProduct_nonneg (fun i => (x i : ℂ))
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re] using h

/-- The standard row-major inverse of the computational two-qubit indexing. -/
def flattenPair (p : Q × Q) : Fin 4 := !![0,1;2,3] p.1 p.2

theorem flattenPair_index (i : Fin 4) : flattenPair (twoQubitIndex i) = i := by
  fin_cases i <;> rfl

theorem index_flattenPair (p : Q × Q) : twoQubitIndex (flattenPair p) = p := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> rfl

theorem sum_flattenPair (f : Fin 4 → ℝ) :
    (∑ p : Q × Q, f (flattenPair p)) = ∑ i : Fin 4, f i := by
  simp [Fintype.sum_prod_type, Q, flattenPair, Fin.sum_univ_succ]
  <;> ring

/-- A normalized real column factor, regarded as a purification with four environment labels. -/
def realFactorKet (X : RealMat4) (hN : ∑ i, ∑ j, X i j ^ 2 = 1) :
    Ket (Fin 4 × (Q × Q)) where
  vec p := (X (flattenPair p.2) p.1 : ℂ)
  normalized' := by
    rw [Fintype.sum_prod_type]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have he : (∑ j : Fin 4, ∑ p : Q × Q, X (flattenPair p) j ^ 2) =
        ∑ j : Fin 4, ∑ i : Fin 4, X i j ^ 2 :=
      Finset.sum_congr rfl (fun j _ => sum_flattenPair (fun i => X i j ^ 2))
    rw [he, Finset.sum_comm]
    exact hN

/-- The density matrix reduced from the column purification is its exact real Gram matrix. -/
theorem realFactorKet_matrix (X : RealMat4) (hN : ∑ i, ∑ j, X i j ^ 2 = 1) :
    twoQubitMatrix (MState.pure (realFactorKet X hN)).traceLeft =
      (X * Xᴴ).map Complex.ofReal := by
  ext i j
  change (∑ k : Fin 4,
    (realFactorKet X hN) (k, twoQubitIndex i) *
      conj ((realFactorKet X hN) (k, twoQubitIndex j))) = _
  simp [realFactorKet, Ket.apply, flattenPair_index, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul]

/--
Every two-qubit density matrix that is real in the computational basis and
has both antidiagonal coherences zero has concurrence zero. No rank or
strict-positivity assumption occurs.
-/
theorem concurrence_zero_of_real_antidiagonal (ρ : MState (Q × Q))
    (hreal : ∀ i j : Fin 4, (twoQubitMatrix ρ i j).im = 0)
    (hw : twoQubitMatrix ρ 0 3 = 0) (hz : twoQubitMatrix ρ 1 2 = 0) :
    concurrence ρ = 0 := by
  let A : RealMat4 := (twoQubitMatrix ρ).map Complex.re
  have hM : (twoQubitMatrix ρ).PosSemidef := ρ.psd.submatrix twoQubitIndex
  have hA : A.PosSemidef := realPart_posSemidef _ hM
  have hAw : A 0 3 = 0 := by simp [A, hw]
  have hAz : A 1 2 = 0 := by simp [A, hz]
  have htrace : A.trace = 1 := by
    have h := congrArg Complex.re (twoQubitMatrix_trace ρ)
    simpa [A, Matrix.trace, Matrix.diag] using h
  have hcomplex : A.map Complex.ofReal = twoQubitMatrix ρ := by
    ext i j
    apply Complex.ext
    · rfl
    · simpa [A] using (hreal i j).symm
  obtain ⟨X, hX, hdet⟩ := exists_real_zero_face_factor A hA hAw hAz
  have hN : (∑ i, ∑ j, X i j ^ 2) = 1 := by
    have h := (congrArg Matrix.trace hX).trans htrace
    simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      pow_two] using h
  have hstate : (MState.pure (realFactorKet X hN)).traceLeft = ρ := by
    apply twoQubitMatrix_injective
    rw [realFactorKet_matrix, hX, hcomplex]
  have hbound := concurrence_traceLeft_le_column_determinants (realFactorKet X hN)
  rw [hstate] at hbound
  have hdet' (k : Fin 4) :
      (realFactorKet X hN) (k,(0,0)) * (realFactorKet X hN) (k,(1,1)) -
      (realFactorKet X hN) (k,(0,1)) * (realFactorKet X hN) (k,(1,0)) = 0 := by
    change (X 0 k : ℂ) * (X 3 k : ℂ) - (X 1 k : ℂ) * (X 2 k : ℂ) = 0
    exact_mod_cast hdet k
  simp only [hdet', norm_zero, mul_zero, Finset.sum_const_zero] at hbound
  exact le_antisymm hbound (concurrence_nonneg ρ)

end EC2.ConcurrenceZeroFace
