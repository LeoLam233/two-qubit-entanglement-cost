import EC2.ConsequencesLOCCSoundness
import EC2.ConsequencesQuantum

/-!
# Operational cost from EC2 and the established regularization theorem

The operational cost in this file is the concrete complete-LOCC dilution cost
from `ConsequencesLOCC`. The external regularization result is stated as a
visible proposition; it is not installed as an axiom or silently proved by
redefining operational cost. The EC2 step below proves the consequence from this
established interface and the actual tensor-power formation formula.
-/

noncomputable section
open Filter Topology

namespace EC2.Operational

/--
Precise regularization interface for the Hayden–Horodecki–Terhal theorem at the
needed two-qubit input scope, using complete finite adaptive LOCC, Bell-pair
rate, and vanishing trace-distance error as defined in `entanglementCost`.
The `n + 1` indexing enumerates exactly all positive tensor powers.
-/
def HHTRegularization : Prop :=
  ∀ (ρ : MState (Q × Q)) (c : ℝ),
    Tendsto (fun n : ℕ => formationBits (qubitTensorPowerSucc ρ n) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 c) → entanglementCost ρ = ENNReal.ofReal c

/--
EC2 Eq. 4 with its concrete operational meaning, conditional on Eq. 1 and the
precisely stated established operational regularization theorem.
-/
theorem entanglementCost_eq_formationBits (hstrong : TensorPowerStrong)
    (hregularization : HHTRegularization) (ρ : MState (Q × Q)) :
    entanglementCost ρ = ENNReal.ofReal (formationBits ρ) :=
  hregularization ρ (formationBits ρ) (formationBits_tensorPower_limit hstrong ρ)

/-- A separately established two-qubit formation formula transfers to the operational cost. -/
theorem entanglementCost_eq_of_formation_formula (hstrong : TensorPowerStrong)
    (hregularization : HHTRegularization) (ρ : MState (Q × Q)) (c : ℝ)
    (hformula : formationBits ρ = c) :
    entanglementCost ρ = ENNReal.ofReal c := by
  rw [entanglementCost_eq_formationBits hstrong hregularization, hformula]

end EC2.Operational
