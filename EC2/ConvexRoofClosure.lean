import EC2.ConvexRoofFormation
import EC2.Measurements

/-!
# EC2 mixed-state closure with the exact bipartitions

The main declaration proves the extension from the pure-state entropy bound
(Eq. 25) to all mixed states (Eq. 1). The dimensions of both auxiliary systems
are arbitrary. The pure entropy bound is an explicit remaining premise here;
this module is not an unconditional proof of Eq. 1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Ensemble MState
open scoped BigOperators NNReal

namespace EC2

section ExactEC2
variable {a b : Type} [Fintype a] [Fintype b]
variable [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]

/--
EC2 Eq. 25 implies Eq. 1 for every mixed `AA':BB'` state and arbitrary finite
`A'`, `B'`. Axes chosen in the proof of the pure premise may depend on the
ensemble member. No condition on ranks or marginal spectra is introduced.
-/
theorem strong_superadditivity_of_pure_entropy
    (hpure : ∀ ψ : Ket ((Q × a) × (Q × b)),
      formationBits (marginalAB (MState.pure ψ)) +
        formationBits (marginalAux (MState.pure ψ)) ≤
          entropyBits (MState.pure ψ).traceRight)
    (Ω : MState ((Q × a) × (Q × b))) :
    formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω := by
  apply formationBits_lower_bound_over_pure_ensembles Ω _
    (add_nonneg (formationBits_nonneg _) (formationBits_nonneg _))
  intro n hn e hmix
  have hAB := formationBits_finite_jensen (marginalAB <$> toMEnsemble e)
  have hAux := formationBits_finite_jensen (marginalAux <$> toMEnsemble e)
  rw [← marginalAB_mix, hmix] at hAB
  rw [← marginalAux_mix, hmix] at hAux
  change formationBits (marginalAB Ω) ≤
    ∑ i, (e.distr i : ℝ) * formationBits (marginalAB (MState.pure (e.states i))) at hAB
  change formationBits (marginalAux Ω) ≤
    ∑ i, (e.distr i : ℝ) * formationBits (marginalAux (MState.pure (e.states i))) at hAux
  calc
    formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤
        (∑ i, (e.distr i : ℝ) * formationBits (marginalAB (MState.pure (e.states i)))) +
        (∑ i, (e.distr i : ℝ) * formationBits (marginalAux (MState.pure (e.states i)))) :=
      add_le_add hAB hAux
    _ = ∑ i, (e.distr i : ℝ) *
        (formationBits (marginalAB (MState.pure (e.states i))) +
        formationBits (marginalAux (MState.pure (e.states i)))) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ i, (e.distr i : ℝ) *
        entropyBits (MState.pure (e.states i)).traceRight :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hpure (e.states i)) (e.distr i).zero_le_coe)

/-- Strong superadditivity supplies the product-state lower bound at every partner dimension. -/
theorem formationBits_partner_lower_bound
    (hstrong : ∀ Ω : MState ((Q × a) × (Q × b)),
      formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω)
    (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    formationBits ρ + formationBits σ ≤ formationBits (partnerProduct ρ σ) := by
  simpa using hstrong (partnerProduct ρ σ)

/-- Product subadditivity and the exact EC2 lower bound yield arbitrary-partner additivity. -/
theorem formationBits_partner_additivity
    (hstrong : ∀ Ω : MState ((Q × a) × (Q × b)),
      formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω)
    (hsubadditive : ∀ (ρ : MState (Q × Q)) (σ : MState (a × b)),
      formationBits (partnerProduct ρ σ) ≤ formationBits ρ + formationBits σ)
    (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    formationBits (partnerProduct ρ σ) = formationBits ρ + formationBits σ :=
  le_antisymm (hsubadditive ρ σ) (formationBits_partner_lower_bound hstrong ρ σ)

end ExactEC2
end EC2
