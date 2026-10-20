import EC2.ConcurrenceCovariance

/-! # Explicit local diagonal phase changes

These total phases include vanishing matrix entries. They are shared by the
complex zero-face proof and the canonical antidiagonal phase reduction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2

/-- A unit complex phase, chosen as one when the original number vanishes. -/
def phaseOf (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem norm_phaseOf (z : ℂ) : ‖phaseOf z‖ = 1 := by
  by_cases hz : z = 0
  · simp [phaseOf, hz]
  · simp [phaseOf, hz, norm_div, norm_ne_zero_iff.mpr hz]

@[simp] theorem phaseOf_mul_conj (z : ℂ) : phaseOf z * conj (phaseOf z) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phaseOf]
  norm_num

@[simp] theorem conj_phaseOf_mul (z : ℂ) : conj (phaseOf z) * phaseOf z = 1 := by
  rw [mul_comm, phaseOf_mul_conj]

/-- Removing a total phase gives the nonnegative modulus, also at zero. -/
theorem mul_conj_phaseOf (z : ℂ) : z * conj (phaseOf z) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phaseOf, if_neg hz, map_div₀, Complex.conj_ofReal, ← mul_div_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    push_cast
    field_simp

/-- Diagonal entries of a local qubit phase unitary. -/
def phaseDiagonal (z : ℂ) : Q → ℂ := ![1, phaseOf z]

/-- The exact local diagonal unitary diag(1,z/|z|), with a total zero convention. -/
def phaseUnitary (z : ℂ) : Matrix.unitaryGroup Q ℂ :=
  ⟨Matrix.diagonal (phaseDiagonal z), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, phaseDiagonal, RCLike.star_def]⟩

@[simp] theorem phaseUnitary_apply (z : ℂ) (i j : Q) :
    (phaseUnitary z).val i j = if i = j then phaseDiagonal z i else 0 := rfl

/-- Matrix entries under independent local diagonal phases. -/
theorem localConj_phase_apply (ρ : MState (Q × Q)) (a b : ℂ) (i j k l : Q) :
    (localConj ρ (phaseUnitary b) (phaseUnitary a)).m (i,j) (k,l) =
      (phaseDiagonal b i * phaseDiagonal a j) * ρ.m (i,j) (k,l) *
        conj (phaseDiagonal b k * phaseDiagonal a l) := by
  change ((phaseUnitary b ⊗ᵤ phaseUnitary a).val * ρ.m *
    (phaseUnitary b ⊗ᵤ phaseUnitary a).val.conjTranspose) (i,j) (k,l) = _
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      Matrix.unitary_kron_apply, phaseUnitary_apply, RCLike.star_def]

/-- The same diagonal phase action in the fixed 00,01,10,11 ordering. -/
theorem twoQubitMatrix_localConj_phase (ρ : MState (Q × Q)) (a b : ℂ) (i j : Fin 4) :
    twoQubitMatrix (localConj ρ (phaseUnitary b) (phaseUnitary a)) i j =
      (phaseDiagonal b (twoQubitIndex i).1 * phaseDiagonal a (twoQubitIndex i).2) *
        twoQubitMatrix ρ i j *
        conj (phaseDiagonal b (twoQubitIndex j).1 * phaseDiagonal a (twoQubitIndex j).2) :=
  localConj_phase_apply ρ a b _ _ _ _

end EC2
