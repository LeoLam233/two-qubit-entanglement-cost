import EC2.Quantum

/-! Additivity of actual finite-dimensional density-state entropy in bits. -/

noncomputable section
open scoped BigOperators

namespace EC2

theorem entropyBits_prod {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ρ : MState a) (σ : MState b) :
    entropyBits (ρ.prod σ) = entropyBits ρ + entropyBits σ := by
  obtain ⟨e,he⟩ := MState.spectrum_prod ρ σ
  unfold entropyBits
  rw [← add_div]
  congr 1
  change (∑ i, Real.negMulLog ((ρ.prod σ).spectrum i : ℝ)) =
    (∑ i, Real.negMulLog (ρ.spectrum i : ℝ)) +
    ∑ j, Real.negMulLog (σ.spectrum j : ℝ)
  rw [← Equiv.sum_comp e]
  simp only [Fintype.sum_prod_type, he, Prob.coe_mul, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ProbDistribution.normalized, one_mul]

end EC2
