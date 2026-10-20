import EC2.ConcurrenceFull
import EC2.PureEC2
import EC2.ConsequencesOperational

/-!
# EC2 final theorem statements

The EC2-specific dependencies are discharged by the actual proofs in this
project. The only remaining proof arguments are the precisely stated,
established results imported by the manuscript: complex Schatten Hanner,
Wootters' two formulas, and (only for operational cost) HHT regularization.
These inputs are propositions passed explicitly, not axioms or definitions
that silently identify the requested quantities.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EC2

section Auxiliary
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] [Nonempty b]

/-- Manuscript Eq. 1: every mixed state, qubit A,B and arbitrary finite A',B'. -/
theorem strong_superadditivity
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (Ω : MState ((Q × a) × (Q × b))) :
    formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω :=
  strong_superadditivity_from_fixed_axis (fixed_axis_concurrence hConcurrence)
    hFormation hHanner Ω

/-- Manuscript Eq. 2: additivity with every finite-dimensional bipartite partner. -/
theorem arbitrary_partner_additivity
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    formationBits (partnerProduct ρ σ) = formationBits ρ + formationBits σ :=
  formationBits_partner_additivity_of_strong
    (strong_superadditivity hHanner hFormation hConcurrence) ρ σ

end Auxiliary

/-- Strong superadditivity at every auxiliary dimension used by finite tensor iteration. -/
theorem tensorPowerStrong
    (hHanner : Literature.ComplexRectangularHanner)
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula) : TensorPowerStrong := by
  intro n Ω
  exact strong_superadditivity (hHanner _ _) hFormation hConcurrence Ω

/-- Manuscript Eq. 3: every positive finite tensor power of every two-qubit state. -/
theorem formation_tensor_power
    (hHanner : Literature.ComplexRectangularHanner)
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (ρ : MState (Q × Q)) (n : ℕ) (hn : 0 < n) :
    formationBits (qubitTensorPower ρ n hn) = (n : ℝ) * Entropy.wBits (concurrence ρ) := by
  rw [formationBits_tensorPower_of_strong
    (tensorPowerStrong hHanner hFormation hConcurrence), hFormation ρ]

/-- Manuscript Eq. 4: Bell-pair dilution cost under complete adaptive LOCC
with vanishing trace-distance error, for every two-qubit state. -/
theorem entanglement_cost_formula
    (hHanner : Literature.ComplexRectangularHanner)
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (hRegularization : Operational.HHTRegularization)
    (ρ : MState (Q × Q)) :
    Operational.entanglementCost ρ = ENNReal.ofReal (Entropy.wBits (concurrence ρ)) :=
  Operational.entanglementCost_eq_of_formation_formula
    (tensorPowerStrong hHanner hFormation hConcurrence)
    hRegularization ρ _ (hFormation ρ)

/-- The operational cost is finite, as a consequence of the proved formula. -/
theorem entanglement_cost_finite
    (hHanner : Literature.ComplexRectangularHanner)
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (hRegularization : Operational.HHTRegularization)
    (ρ : MState (Q × Q)) : Operational.entanglementCost ρ ≠ ⊤ := by
  rw [entanglement_cost_formula hHanner hFormation hConcurrence hRegularization]
  exact ENNReal.ofReal_ne_top

/-- Eq. 4 in real-valued notation, with finiteness separately established. -/
theorem entanglement_cost_real_formula
    (hHanner : Literature.ComplexRectangularHanner)
    (hFormation : Literature.WoottersFormation)
    (hConcurrence : ConcurrenceReduction.WoottersSpectralFormula)
    (hRegularization : Operational.HHTRegularization)
    (ρ : MState (Q × Q)) :
    (Operational.entanglementCost ρ).toReal = Entropy.wBits (concurrence ρ) := by
  have hn : 0 ≤ Entropy.wBits (concurrence ρ) := by
    rw [← hFormation ρ]
    exact formationBits_nonneg ρ
  rw [entanglement_cost_formula hHanner hFormation hConcurrence hRegularization,
    ENNReal.toReal_ofReal hn]

end EC2
