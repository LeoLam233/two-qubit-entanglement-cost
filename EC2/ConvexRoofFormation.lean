import EC2.ConvexRoofQuantum
import EC2.Quantum

/-!
# Formation-entanglement ensemble calculus in bits

These are unconditional properties of Physlib's actual convex-roof definition:
finite-ensemble convexity, upper bounds, arbitrarily accurate decompositions,
and the lower-bound principle for the infimum. No optimal ensemble is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Ensemble MState
open scoped BigOperators NNReal

namespace EC2

section General
variable {a b ι : Type} [Fintype a] [Fintype b] [Fintype ι]
variable [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]

/-- The phase-invariant pure-state entropy used by Physlib's formation roof, in nats. -/
def formationPureCostNats : KetUpToPhase (a × b) → ℝ≥0 := KetUpToPhase.lift
  (fun ψ => ⟨Sᵥₙ (MState.pure ψ).traceRight, Sᵥₙ_nonneg (MState.pure ψ).traceRight⟩)
  (fun ψ φ h => by
    congr 1
    congr 1
    exact congrArg MState.traceRight ((MState.PhaseEquiv_iff_pure_eq ψ φ).mp h))

/-- Evaluation of the pure cost requires no quotient representatives to be chosen. -/
theorem formationPureCostNats_mk (ψ : Ket (a × b)) :
    (formationPureCostNats (KetUpToPhase.mk ψ) : ℝ) =
      Sᵥₙ (MState.pure ψ).traceRight := rfl

/-- A named pure-cost interface for the unchanged imported entanglement-of-formation definition. -/
theorem EoF_eq_formationPureCostNats (ρ : MState (a × b)) :
    EoF ρ = convex_roof formationPureCostNats ρ := rfl

/-- Formation entanglement in bits is convex on every finite mixed ensemble. -/
theorem formationBits_finite_jensen (e : MEnsemble (a × b) ι) :
    formationBits (Ensemble.mix e) ≤
      ∑ i, (e.distr i : ℝ) * formationBits (e.states i) := by
  have h : (EoF (Ensemble.mix e) : ℝ) ≤
      ∑ i, (e.distr i : ℝ) * (EoF (e.states i) : ℝ) := by
    unfold EoF
    exact convex_roof_finite_jensen _ e
  unfold formationBits
  calc
    (EoF (Ensemble.mix e) : ℝ) / Real.log 2 ≤
        (∑ i, (e.distr i : ℝ) * (EoF (e.states i) : ℝ)) / Real.log 2 :=
      div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num))
    _ = _ := by simp only [Finset.sum_div, mul_div_assoc]

/-- Any finite pure ensemble provides a formation-entanglement upper bound in bits. -/
theorem formationBits_le_pure_average (e : PEnsemble (a × b) ι) :
    formationBits (Ensemble.mix (toMEnsemble e)) ≤
      ∑ i, (e.distr i : ℝ) * entropyBits (MState.pure (e.states i)).traceRight := by
  have h := formationBits_finite_jensen (toMEnsemble e)
  change formationBits (Ensemble.mix (toMEnsemble e)) ≤
    ∑ i, (e.distr i : ℝ) * formationBits (MState.pure (e.states i)) at h
  simpa only [formationBits_pure] using h

/-- Arbitrarily accurate finite pure decompositions exist for formation entanglement in bits. -/
theorem exists_pure_ensemble_formationBits_lt (ρ : MState (a × b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (e : PEnsemble (a × b) (Fin n)),
      Ensemble.mix (toMEnsemble e) = ρ ∧
      (∑ i, (e.distr i : ℝ) * entropyBits (MState.pure (e.states i)).traceRight) <
        formationBits ρ + ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn, e, hmix, hcost⟩ :=
    exists_pure_ensemble_average_lt formationPureCostNats ρ (mul_pos hε hlog)
  refine ⟨n, hn, e, hmix, ?_⟩
  rw [pure_average_real] at hcost
  simp only [formationPureCostNats_mk, ← EoF_eq_formationPureCostNats] at hcost
  have hr := (div_lt_div_of_pos_right hcost hlog)
  simpa only [formationBits, add_div, Finset.sum_div,
    entropyBits, mul_div_assoc, mul_div_cancel_right₀ ε (ne_of_gt hlog)] using hr

/-- Taking the infimum over all pure ensembles needs no attainment assumption. -/
theorem formationBits_lower_bound_over_pure_ensembles
    (ρ : MState (a × b)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ (n : ℕ), 0 < n → ∀ e : PEnsemble (a × b) (Fin n),
      Ensemble.mix (toMEnsemble e) = ρ →
      c ≤ ∑ i, (e.distr i : ℝ) *
        entropyBits (MState.pure (e.states i)).traceRight) :
    c ≤ formationBits ρ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : (⟨c * Real.log 2, mul_nonneg hc hlog.le⟩ : ℝ≥0) ≤ EoF ρ := by
    rw [EoF_eq_formationPureCostNats]
    apply le_convex_roof _ ρ
    intro n hn e hmix
    change c * Real.log 2 ≤
      (pure_average_NNReal (formationPureCostNats ∘ KetUpToPhase.mk) e : ℝ)
    rw [pure_average_real]
    simp only [formationPureCostNats_mk]
    apply (le_div_iff₀ hlog).mp
    calc
      c ≤ ∑ i, (e.distr i : ℝ) *
          entropyBits (MState.pure (e.states i)).traceRight := hbound n hn e hmix
      _ = _ := by simp only [entropyBits, Finset.sum_div, mul_div_assoc]
  exact (le_div_iff₀ hlog).mpr h

end General


end EC2
