import EC2.ConcurrencePauli
import EC2.ConcurrenceCovariance

/-! # Pauli expectations and covariance of the fixed-axis maximum -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace EC2
open ConcurrenceGeometry ConcurrenceBloch

/-- The first marginal Bloch vector is the expectation of σ(u)⊗I. -/
theorem pauli_expectation_left (ρ : MState (Q × Q)) (u : Vec3) :
    (Matrix.trace (ρ.m * (Pauli.observable u ⊗ₖ (1 : Matrix Q Q ℂ)))).re =
      dot3 (marginalBlochA ρ) u := by
  simp [dot3, marginalBlochA, blochA, twoQubitMatrix, twoQubitIndex,
    Pauli.observable, pauliA, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.kronecker, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- The second marginal Bloch vector is the expectation of I⊗σ(v). -/
theorem pauli_expectation_right (ρ : MState (Q × Q)) (v : Vec3) :
    (Matrix.trace (ρ.m * ((1 : Matrix Q Q ℂ) ⊗ₖ Pauli.observable v))).re =
      dot3 (marginalBlochB ρ) v := by
  simp [dot3, marginalBlochB, blochB, twoQubitMatrix, twoQubitIndex,
    Pauli.observable, pauliB, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.kronecker, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- The matrix correlation is exactly the joint Pauli expectation. -/
theorem pauli_expectation_joint (ρ : MState (Q × Q)) (u v : Vec3) :
    (Matrix.trace (ρ.m * (Pauli.observable u ⊗ₖ Pauli.observable v))).re =
      dot3 u ((correlationMatrix ρ).mulVec v) := by
  simp [dot3, correlationMatrix, correlation, twoQubitMatrix, twoQubitIndex,
    Pauli.observable, pauliA, pauliB, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.kronecker,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- Simultaneous unitary transport of a state matrix and observable preserves
its complex trace expectation. -/
theorem trace_unitary_expectation {d : Type} [Fintype d] [DecidableEq d]
    (ρ H : Matrix d d ℂ) (U : Matrix.unitaryGroup d ℂ) :
    Matrix.trace ((U.val * ρ * U.val.conjTranspose) *
      (U.val * H * U.val.conjTranspose)) = Matrix.trace (ρ * H) := by
  have hU : U.val.conjTranspose * U.val = 1 := U.prop.1
  have hprod : (U.val * ρ * U.val.conjTranspose) *
      (U.val * H * U.val.conjTranspose) = U.val * (ρ * H) * U.val.conjTranspose := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.val.conjTranspose U.val, hU, one_mul]
  rw [hprod, Matrix.trace_mul_cycle, hU, one_mul]

/-- Product conjugation of two observables is their tensor-product conjugation. -/
theorem tensor_conjugation {a b : Type} [Fintype a] [Fintype b]
    (U A : Matrix a a ℂ) (V B : Matrix b b ℂ) :
    (U * A * U.conjTranspose) ⊗ₖ (V * B * V.conjTranspose) =
      (U ⊗ₖ V) * (A ⊗ₖ B) * (U ⊗ₖ V).conjTranspose := by
  rw [Matrix.kroneckerMap_conjTranspose, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

/-- The joint Pauli correlation is unchanged when state and both axes are
transported by their respective local unitaries. -/
theorem correlation_localConj (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ)
    (u v : Vec3) :
    dot3 (Pauli.rotation U u)
      ((correlationMatrix (localConj ρ U V)).mulVec (Pauli.rotation V v)) =
      dot3 u ((correlationMatrix ρ).mulVec v) := by
  rw [← pauli_expectation_joint, ← pauli_expectation_joint,
    Pauli.observable_rotation, Pauli.observable_rotation, tensor_conjugation]
  change (Matrix.trace (((U ⊗ᵤ V).val * ρ.m * (U ⊗ᵤ V).val.conjTranspose) *
    ((U ⊗ᵤ V).val * (Pauli.observable u ⊗ₖ Pauli.observable v) *
      (U ⊗ᵤ V).val.conjTranspose))).re = _
  rw [trace_unitary_expectation]

/-- Expectation covariance for the first marginal Pauli vector. -/
theorem marginal_expectation_left_localConj (ρ : MState (Q × Q))
    (U V : Matrix.unitaryGroup Q ℂ) (u : Vec3) :
    dot3 (marginalBlochA (localConj ρ U V)) (Pauli.rotation U u) =
      dot3 (marginalBlochA ρ) u := by
  rw [← pauli_expectation_left, ← pauli_expectation_left, Pauli.observable_rotation]
  have hV : V.val * (1 : Matrix Q Q ℂ) * V.val.conjTranspose = 1 := by
    rw [Matrix.mul_one]
    exact V.prop.2
  nth_rw 1 [← hV]
  rw [tensor_conjugation]
  change (Matrix.trace (((U ⊗ᵤ V).val * ρ.m * (U ⊗ᵤ V).val.conjTranspose) *
    ((U ⊗ᵤ V).val * (Pauli.observable u ⊗ₖ (1 : Matrix Q Q ℂ)) *
      (U ⊗ᵤ V).val.conjTranspose))).re = _
  rw [trace_unitary_expectation]

/-- Expectation covariance for the second marginal Pauli vector. -/
theorem marginal_expectation_right_localConj (ρ : MState (Q × Q))
    (U V : Matrix.unitaryGroup Q ℂ) (v : Vec3) :
    dot3 (marginalBlochB (localConj ρ U V)) (Pauli.rotation V v) =
      dot3 (marginalBlochB ρ) v := by
  rw [← pauli_expectation_right, ← pauli_expectation_right, Pauli.observable_rotation]
  have hU : U.val * (1 : Matrix Q Q ℂ) * U.val.conjTranspose = 1 := by
    rw [Matrix.mul_one]
    exact U.prop.2
  nth_rw 1 [← hU]
  rw [tensor_conjugation]
  change (Matrix.trace (((U ⊗ᵤ V).val * ρ.m * (U ⊗ᵤ V).val.conjTranspose) *
    ((U ⊗ᵤ V).val * ((1 : Matrix Q Q ℂ) ⊗ₖ Pauli.observable v) *
      (U ⊗ᵤ V).val.conjTranspose))).re = _
  rw [trace_unitary_expectation]

theorem dot3_ext {a b : Vec3} (h : ∀ u : Vec3, dot3 a u = dot3 b u) : a = b := by
  have h0 := h ![1,0,0]
  have h1 := h ![0,1,0]
  have h2 := h ![0,0,1]
  simp [dot3] at h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Exact rotation law for the first marginal Bloch vector, including zero. -/
theorem marginalBlochA_localConj (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ) :
    marginalBlochA (localConj ρ U V) = Pauli.rotation U (marginalBlochA ρ) := by
  apply dot3_ext
  intro u
  have h := marginal_expectation_left_localConj ρ U V (Pauli.rotation U⁻¹ u)
  rw [Pauli.rotation_inverse'] at h
  rw [h]
  rw [← Pauli.rotation_dot U (marginalBlochA ρ) (Pauli.rotation U⁻¹ u),
    Pauli.rotation_inverse']

/-- Exact rotation law for the second marginal Bloch vector, including zero. -/
theorem marginalBlochB_localConj (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ) :
    marginalBlochB (localConj ρ U V) = Pauli.rotation V (marginalBlochB ρ) := by
  apply dot3_ext
  intro v
  have h := marginal_expectation_right_localConj ρ U V (Pauli.rotation V⁻¹ v)
  rw [Pauli.rotation_inverse'] at h
  rw [h]
  rw [← Pauli.rotation_dot V (marginalBlochB ρ) (Pauli.rotation V⁻¹ v),
    Pauli.rotation_inverse']

/-- Every allowed marginal axis is carried to an allowed marginal axis;
zero Bloch vectors keep all their prescribed choices. -/
theorem marginalAxis_rotation (a n : Vec3) (U : Matrix.unitaryGroup Q ℂ)
    (h : IsMarginalAxis a n) : IsMarginalAxis (Pauli.rotation U a) (Pauli.rotation U n) := by
  obtain ⟨hn, α, ha⟩ := h
  refine ⟨(Pauli.rotation_sqLength U n).trans hn, α, ?_⟩
  have ha' : a = α • n := ha
  rw [ha', Pauli.rotation_smul]
  rfl

/-- The exact fixed-axis maximum is invariant under simultaneous local
unitary transport of the state and its two fixed marginal axes. -/
theorem transverseBound_localConj (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ)
    (n m : Vec3) :
    transverseBound (localConj ρ U V) (Pauli.rotation U n) (Pauli.rotation V m) =
      transverseBound ρ n m := by
  have hset : transverseValues (localConj ρ U V) (Pauli.rotation U n) (Pauli.rotation V m) =
      transverseValues ρ n m := by
    ext z
    constructor
    · rintro ⟨u,v,hu,hv,hn,hm,hz⟩
      refine ⟨Pauli.rotation U⁻¹ u, Pauli.rotation V⁻¹ v,
        (Pauli.rotation_sqLength U⁻¹ u).trans hu,
        (Pauli.rotation_sqLength V⁻¹ v).trans hv, ?_, ?_, ?_⟩
      · have h := Pauli.rotation_dot U n (Pauli.rotation U⁻¹ u)
        rw [Pauli.rotation_inverse'] at h
        exact h.symm.trans hn
      · have h := Pauli.rotation_dot V m (Pauli.rotation V⁻¹ v)
        rw [Pauli.rotation_inverse'] at h
        exact h.symm.trans hm
      · rw [hz, ← correlation_localConj ρ U V, Pauli.rotation_inverse', Pauli.rotation_inverse']
    · rintro ⟨u,v,hu,hv,hn,hm,hz⟩
      refine ⟨Pauli.rotation U u, Pauli.rotation V v,
        (Pauli.rotation_sqLength U u).trans hu,
        (Pauli.rotation_sqLength V v).trans hv, ?_, ?_, ?_⟩
      · exact (Pauli.rotation_dot U n u).trans hn
      · exact (Pauli.rotation_dot V m v).trans hm
      · rw [hz, correlation_localConj]
  exact congrArg sSup hset

end EC2
