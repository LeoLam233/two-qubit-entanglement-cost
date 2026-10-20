import EC2.ConcurrenceEnsemble

/-! # The fixed-axis concurrence bound for actual canonical density matrices

The canonical factor is used as an explicit purification. Its conditional
column ensemble gives the concurrence upper bound, including zero columns.
The Pauli-trace geometry then gives the fixed-axis inequality for every
allowed axis choice, including zero marginal Bloch vectors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate NNReal

namespace EC2
open ConcurrenceAlgebra ConcurrenceBloch ConcurrenceGeometry

def canonicalKet (L u v s t r : ℝ) (hN : canonicalMass L u v s t r = 1) :
    Ket (Q × (Q × Q)) where
  vec j := ![!![(L : ℂ), 0; (u : ℂ) + Complex.I * (v : ℂ), (t : ℂ)],
    !![0, 0; (s : ℂ), (r : ℂ)]] j.1 j.2.1 j.2.2
  normalized' := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    unfold canonicalMass at hN
    nlinarith only [hN]

def canonicalState (L u v s t r : ℝ) (hN : canonicalMass L u v s t r = 1) :
    MState (Q × Q) := (MState.pure (canonicalKet L u v s t r hN)).traceLeft

/-- The explicit column purification has precisely the matrix Z Z†. -/
theorem canonicalState_matrix (L u v s t r : ℝ)
    (hN : canonicalMass L u v s t r = 1) :
    twoQubitMatrix (canonicalState L u v s t r hN) = canonicalDensity L u v s t r := by
  ext i j
  change (∑ k : Q, canonicalKet L u v s t r hN (k, twoQubitIndex i) *
    conj (canonicalKet L u v s t r hN (k, twoQubitIndex j))) = _
  fin_cases i <;> fin_cases j <;>
    simp [twoQubitIndex, canonicalKet, canonicalDensity, canonicalFactor,
      Ket.apply, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The defining convex roof is at most the cost of the two canonical columns.
The second column has zero determinant; the proof has no strict rank or
nonzero-column hypothesis. -/
theorem concurrence_canonical_le (L u v s t r : ℝ)
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hN : canonicalMass L u v s t r = 1) :
    concurrence (canonicalState L u v s t r hN) ≤ 2 * L * t := by
  have h := concurrence_traceLeft_le_column_determinants (canonicalKet L u v s t r hN)
  simpa [canonicalState, canonicalKet, Ket.apply, Fin.sum_univ_two,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    abs_of_nonneg ht, mul_assoc] using h

/-- Equation (13) for every normalized canonical density matrix and every
allowed fixed marginal-axis pair. Zero marginals and zero concurrence are
included in the same theorem. -/
theorem canonical_fixed_axis_concurrence (L u v s t r : ℝ)
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hN : canonicalMass L u v s t r = 1)
    (n m : Vec3)
    (ha : IsMarginalAxis (marginalBlochA (canonicalState L u v s t r hN)) n)
    (hb : IsMarginalAxis (marginalBlochB (canonicalState L u v s t r hN)) m) :
    concurrence (canonicalState L u v s t r hN) ≤
      transverseBound (canonicalState L u v s t r hN) n m := by
  obtain ⟨_, α, hα⟩ := ha
  obtain ⟨_, β, hβ⟩ := hb
  have ha' : blochA (canonicalDensity L u v s t r) = fun i => α * n i := by
    simpa only [marginalBlochA, canonicalState_matrix] using hα
  have hb' : blochB (canonicalDensity L u v s t r) = fun i => β * m i := by
    simpa only [marginalBlochB, canonicalState_matrix] using hβ
  obtain ⟨x, y, hx, hy, hxn, hym, hxy⟩ :=
    canonical_fixed_axes_correlation L u v s t r hL ht n m α β ha' hb'
  apply (concurrence_canonical_le L u v s t r hL ht hN).trans
  apply le_transverseBound_of_witness _ n m x y _ hx hy hxn hym
  simpa only [correlationMatrix, canonicalState_matrix] using hxy

/-- The computational-basis flattening retains the full density matrix. -/
theorem twoQubitMatrix_injective : Function.Injective twoQubitMatrix := by
  intro ρ σ h
  apply MState.ext_m
  ext a b
  let flatten : Q × Q → Fin 4 := fun ab => !![0,1;2,3] ab.1 ab.2
  have hab := congrFun (congrFun h (flatten a)) (flatten b)
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simpa [twoQubitMatrix, twoQubitIndex, flatten] using hab

/-- Trace preservation of the 00,01,10,11 flattening. -/
theorem twoQubitMatrix_trace (ρ : MState (Q × Q)) : (twoQubitMatrix ρ).trace = 1 := by
  have htrace : (twoQubitMatrix ρ).trace = ρ.m.trace := by
    simp [twoQubitMatrix, twoQubitIndex, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  rw [htrace, ρ.tr']

/-- The canonical mass is automatically one when the canonical Gram matrix
is the matrix of a normalized quantum state. -/
theorem canonicalMass_eq_one_of_matrix (ρ : MState (Q × Q))
    (L u v s t r : ℝ) (hρ : twoQubitMatrix ρ = canonicalDensity L u v s t r) :
    canonicalMass L u v s t r = 1 := by
  rw [← canonicalDensity_trace, ← hρ, twoQubitMatrix_trace]
  rfl

/-- Canonical fixed-axis inequality stated for an existing ordinary density
matrix rather than for a constructor, with normalization derived from it. -/
theorem fixed_axis_concurrence_of_canonical_matrix (ρ : MState (Q × Q))
    (L u v s t r : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hρ : twoQubitMatrix ρ = canonicalDensity L u v s t r)
    (n m : Vec3) (ha : IsMarginalAxis (marginalBlochA ρ) n)
    (hb : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  have hN := canonicalMass_eq_one_of_matrix ρ L u v s t r hρ
  have heq : ρ = canonicalState L u v s t r hN :=
    twoQubitMatrix_injective (hρ.trans (canonicalState_matrix L u v s t r hN).symm)
  subst ρ
  exact canonical_fixed_axis_concurrence L u v s t r hL ht hN n m ha hb

end EC2
