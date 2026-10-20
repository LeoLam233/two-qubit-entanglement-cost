import EC2.ConcurrenceQuantum
import EC2.Measurements

/-! # Explicit column-ensemble concurrence estimates

These proofs use the defining convex roof directly. In the canonical rank-two
factor, one column is a product vector, so the other column's determinant
gives the required upper bound without any spectral formula for concurrence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal ComplexConjugate

namespace EC2

/-- Normalizing an unnormalized two-qubit vector and multiplying by its
squared norm gives exactly its homogeneous determinant concurrence.
The identity also holds for the zero vector. -/
theorem weighted_conditional_pureConcurrence (v : Q × Q → ℂ) :
    vectorWeight v * (pureConcurrence (conditionalKet v) : ℝ) =
      2 * ‖v (0,0) * v (1,1) - v (0,1) * v (1,0)‖ := by
  classical
  by_cases h : ∃ j, v j ≠ 0
  · have hp := vectorWeight_pos v h
    have hs : Real.sqrt (vectorWeight v) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    have hsc : (Real.sqrt (vectorWeight v) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hs2 : (Real.sqrt (vectorWeight v) : ℂ) ^ 2 = (vectorWeight v : ℂ) := by
      exact_mod_cast Real.sq_sqrt hp.le
    have hdet :
        v (0,0) / (Real.sqrt (vectorWeight v) : ℂ) *
          (v (1,1) / (Real.sqrt (vectorWeight v) : ℂ)) -
        v (0,1) / (Real.sqrt (vectorWeight v) : ℂ) *
          (v (1,0) / (Real.sqrt (vectorWeight v) : ℂ)) =
        (v (0,0) * v (1,1) - v (0,1) * v (1,0)) / (vectorWeight v : ℂ) := by
      rw [← hs2]
      field_simp [hsc]
    change vectorWeight v *
      (2 * ‖(conditionalKet v) (0,0) * (conditionalKet v) (1,1) -
        (conditionalKet v) (0,1) * (conditionalKet v) (1,0)‖) = _
    simp only [conditionalKet, dite_eq_left h, Ket.normalize, Ket.apply,
      ← Complex.normSq_eq_norm_sq]
    change vectorWeight v * (2 * ‖v (0,0) / (Real.sqrt (vectorWeight v) : ℂ) *
      (v (1,1) / (Real.sqrt (vectorWeight v) : ℂ)) -
      v (0,1) / (Real.sqrt (vectorWeight v) : ℂ) *
      (v (1,0) / (Real.sqrt (vectorWeight v) : ℂ))‖) = _
    rw [hdet, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    field_simp [ne_of_gt hp]
  · have hz : ∀ j, v j = 0 := by simpa using h
    simp [vectorWeight, hz]

/-- The determinant cost of the explicit conditional pure ensemble bounds
concurrence of the reduced two-qubit density matrix, for every finite
environment and including zero conditional columns. -/
theorem concurrence_traceLeft_le_column_determinants {ι : Type}
    [Fintype ι] [DecidableEq ι] (ψ : Ket (ι × (Q × Q))) :
    concurrence (MState.pure ψ).traceLeft ≤
      ∑ i, 2 * ‖ψ (i,(0,0)) * ψ (i,(1,1)) -
        ψ (i,(0,1)) * ψ (i,(1,0))‖ := by
  have hroof := convex_roof_le_any_ensemble phaseConcurrence (conditionalEnsemble ψ)
  have h : concurrence (MState.pure ψ).traceLeft ≤
      (Ensemble.pure_average_NNReal (phaseConcurrence ∘ KetUpToPhase.mk)
        (conditionalEnsemble ψ) : ℝ) := by
    unfold concurrence
    rw [← conditionalEnsemble_mix ψ]
    exact hroof
  apply h.trans_eq
  rw [pure_average_real]
  apply Finset.sum_congr rfl
  intro i _
  change vectorWeight (fun j => ψ (i,j)) *
    (pureConcurrence (conditionalKet (fun j => ψ (i,j))) : ℝ) = _
  exact weighted_conditional_pureConcurrence _

end EC2
