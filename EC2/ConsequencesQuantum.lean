import EC2.ConsequencesTensorDefs
import EC2.ConvexRoofProduct
import EC2.Consequences

/-!
# Exact finite tensor powers and the regularization consequence

The tensor states imported here are ordinary density-matrix tensor products
with the exact local bipartition. The EC2 strong-superadditivity premise is
visible in every theorem requiring it. The operational theorem also visibly
assumes the established operational regularization identity; an operational
LOCC model is not defined in this module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace EC2

/-- EC2 strong superadditivity in the particular finite dimensions used by the iteration. -/
def TensorPowerStrong : Prop :=
  ∀ (n : ℕ) (Ω : MState ((Q × QCopies n) × (Q × QCopies n))),
    formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω

/-- Eq. 1 in arbitrary auxiliary dimensions proves the actual positive tensor-power formula. -/
theorem formationBits_tensorPowerSucc_of_strong (hstrong : TensorPowerStrong)
    (ρ : MState (Q × Q)) (n : ℕ) :
    formationBits (qubitTensorPowerSucc ρ n) = ((n + 1 : ℕ) : ℝ) * formationBits ρ := by
  induction n with
  | zero =>
    simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul] <;> rfl
  | succ n ih =>
    change formationBits (partnerProduct ρ (qubitTensorPowerSucc ρ n)) = _
    rw [formationBits_partner_additivity_of_strong (hstrong n), ih]
    push_cast
    ring

/-- Eq. 3 for every positive natural tensor exponent, with no auxiliary-dimension bound. -/
theorem formationBits_tensorPower_of_strong (hstrong : TensorPowerStrong)
    (ρ : MState (Q × Q)) (n : ℕ) (hn : 0 < n) :
    formationBits (qubitTensorPower ρ n hn) = (n : ℝ) * formationBits ρ := by
  unfold qubitTensorPower
  rw [formationBits_tensorPowerSucc_of_strong hstrong, Nat.sub_add_cancel hn]

/-- The regularized sequence of actual tensor states is exactly constant after normalization. -/
theorem normalized_formationBits_tensorPowerSucc (hstrong : TensorPowerStrong)
    (ρ : MState (Q × Q)) (n : ℕ) :
    formationBits (qubitTensorPowerSucc ρ n) / ((n + 1 : ℕ) : ℝ) = formationBits ρ := by
  rw [formationBits_tensorPowerSucc_of_strong hstrong]
  exact mul_div_cancel_left₀ _ (by positivity)

/-- The entanglement-of-formation regularization limit for the concrete tensor powers. -/
theorem formationBits_tensorPower_limit (hstrong : TensorPowerStrong)
    (ρ : MState (Q × Q)) :
    Tendsto (fun n : ℕ => formationBits (qubitTensorPowerSucc ρ n) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (formationBits ρ)) := by
  have hfun : (fun n : ℕ => formationBits (qubitTensorPowerSucc ρ n) / ((n + 1 : ℕ) : ℝ)) =
      (fun _ : ℕ => formationBits ρ) := by
    funext n
    exact normalized_formationBits_tensorPowerSucc hstrong ρ n
  rw [hfun]
  exact tendsto_const_nhds

/--
The operational entanglement cost equals single-copy formation entanglement
when the established operational regularization theorem supplies this limit.
The operational meaning is an explicit interface and is not replaced by a
new definition of `E_C` as a formal limit.
-/
theorem operational_cost_eq_formationBits_of_regularization
    (hstrong : TensorPowerStrong) (ρ : MState (Q × Q)) (operationalCost : ℝ)
    (hregularization : Tendsto
      (fun n : ℕ => formationBits (qubitTensorPowerSucc ρ n) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 operationalCost)) :
    operationalCost = formationBits ρ :=
  tendsto_nhds_unique hregularization (formationBits_tensorPower_limit hstrong ρ)

end EC2
