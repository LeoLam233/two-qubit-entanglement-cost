import EC2.ConcurrencePhase
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Simultaneous nonnegative antidiagonal phase gauge

For the fixed 00,01,10,11 ordering, the offdiagonal entries transform as
w ↦ w conjugate(αβ) and z ↦ z β conjugate(α). A unit square root of the
product of their total phases therefore makes both entries nonnegative,
including either or both zero entries.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2

theorem phaseOf_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : phaseOf z = z := by
  have hz0 : z ≠ 0 := by
    intro h
    simpa [h] using hz
  simp [phaseOf, hz0, hz]

/-- The exact compatible pair of local phases, with both zero cases total. -/
theorem exists_antidiagonal_phases (w z : ℂ) :
    ∃ α β : ℂ, ‖α‖ = 1 ∧ ‖β‖ = 1 ∧
      α * β = phaseOf w ∧ α * conj β = phaseOf z := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (phaseOf w * phaseOf z) (by decide : 0 < 2)
  have hαnorm : ‖α‖ = 1 := by
    have h := congrArg norm hα
    simp only [norm_pow, norm_mul, norm_phaseOf, one_mul] at h
    nlinarith [norm_nonneg α]
  have hαconj : α * conj α = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hαnorm]
    norm_num
  let β := phaseOf w * conj α
  have hβnorm : ‖β‖ = 1 := by simp [β, norm_mul, hαnorm]
  refine ⟨α, β, hαnorm, hβnorm, ?_, ?_⟩
  · calc
      α * β = phaseOf w * (α * conj α) := by dsimp [β]; ring
      _ = phaseOf w := by rw [hαconj, mul_one]
  · calc
      α * conj β = α ^ 2 * conj (phaseOf w) := by simp [β]; ring
      _ = phaseOf z * (phaseOf w * conj (phaseOf w)) := by rw [hα]; ring
      _ = phaseOf z := by rw [phaseOf_mul_conj, mul_one]

/-- Diagonal marginal coherences transform by a single phase. -/
theorem localConj_phase_marginalA (ρ : MState (Q × Q)) (a b : ℂ) :
    twoQubitMatrix (localConj ρ (phaseUnitary b) (phaseUnitary a)) 0 2 +
      twoQubitMatrix (localConj ρ (phaseUnitary b) (phaseUnitary a)) 1 3 =
      (twoQubitMatrix ρ 0 2 + twoQubitMatrix ρ 1 3) * conj (phaseOf b) := by
  rw [twoQubitMatrix_localConj_phase, twoQubitMatrix_localConj_phase]
  change (1 * 1) * twoQubitMatrix ρ 0 2 * conj (phaseOf b * 1) +
      (1 * phaseOf a) * twoQubitMatrix ρ 1 3 * conj (phaseOf b * phaseOf a) = _
  simp only [map_mul, map_one, one_mul, mul_one]
  calc
    twoQubitMatrix ρ 0 2 * conj (phaseOf b) +
        phaseOf a * twoQubitMatrix ρ 1 3 * (conj (phaseOf b) * conj (phaseOf a)) =
      (twoQubitMatrix ρ 0 2 + twoQubitMatrix ρ 1 3 *
        (phaseOf a * conj (phaseOf a))) * conj (phaseOf b) := by ring
    _ = _ := by rw [phaseOf_mul_conj, mul_one]

theorem localConj_phase_marginalB (ρ : MState (Q × Q)) (a b : ℂ) :
    twoQubitMatrix (localConj ρ (phaseUnitary b) (phaseUnitary a)) 0 1 +
      twoQubitMatrix (localConj ρ (phaseUnitary b) (phaseUnitary a)) 2 3 =
      (twoQubitMatrix ρ 0 1 + twoQubitMatrix ρ 2 3) * conj (phaseOf a) := by
  rw [twoQubitMatrix_localConj_phase, twoQubitMatrix_localConj_phase]
  change (1 * 1) * twoQubitMatrix ρ 0 1 * conj (1 * phaseOf a) +
      (phaseOf b * 1) * twoQubitMatrix ρ 2 3 * conj (phaseOf b * phaseOf a) = _
  simp only [map_mul, map_one, one_mul, mul_one]
  calc
    twoQubitMatrix ρ 0 1 * conj (phaseOf a) +
        phaseOf b * twoQubitMatrix ρ 2 3 * (conj (phaseOf b) * conj (phaseOf a)) =
      (twoQubitMatrix ρ 0 1 + twoQubitMatrix ρ 2 3 *
        (phaseOf b * conj (phaseOf b))) * conj (phaseOf a) := by ring
    _ = _ := by rw [phaseOf_mul_conj, mul_one]

/-- Every pair of antidiagonal entries can simultaneously be made real
and nonnegative by exact local diagonal unitaries. -/
theorem exists_nonnegative_antidiagonal_gauge (ρ : MState (Q × Q)) :
    ∃ α β : ℂ, ‖α‖ = 1 ∧ ‖β‖ = 1 ∧
      twoQubitMatrix (localConj ρ (phaseUnitary α) (phaseUnitary β)) 0 3 =
        (‖twoQubitMatrix ρ 0 3‖ : ℂ) ∧
      twoQubitMatrix (localConj ρ (phaseUnitary α) (phaseUnitary β)) 1 2 =
        (‖twoQubitMatrix ρ 1 2‖ : ℂ) := by
  obtain ⟨α, β, hα, hβ, hw, hz⟩ :=
    exists_antidiagonal_phases (twoQubitMatrix ρ 0 3) (twoQubitMatrix ρ 1 2)
  refine ⟨α, β, hα, hβ, ?_, ?_⟩
  · rw [twoQubitMatrix_localConj_phase]
    change (1 * 1) * twoQubitMatrix ρ 0 3 * conj (phaseOf α * phaseOf β) = _
    rw [phaseOf_of_norm_one hα, phaseOf_of_norm_one hβ, hw]
    simpa using mul_conj_phaseOf (twoQubitMatrix ρ 0 3)
  · rw [twoQubitMatrix_localConj_phase]
    change (1 * phaseOf β) * twoQubitMatrix ρ 1 2 * conj (phaseOf α * 1) = _
    rw [phaseOf_of_norm_one hα, phaseOf_of_norm_one hβ]
    have hzc : β * conj α = conj (phaseOf (twoQubitMatrix ρ 1 2)) := by
      have h := congrArg (conj : ℂ → ℂ) hz
      simpa [mul_comm] using h
    calc
      (1 * β) * twoQubitMatrix ρ 1 2 * conj (α * 1) =
        twoQubitMatrix ρ 1 2 * (β * conj α) := by simp; ring
      _ = _ := by rw [hzc, mul_conj_phaseOf]

end EC2
