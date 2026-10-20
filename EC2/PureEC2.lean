import EC2.MeasurementBalance
import EC2.Literature
import EC2.ConvexRoofClosure

/-! # The primary arbitrary-auxiliary-system argument

This file proves the complete passage from the fixed-axis concurrence lemma
and the established Hanner/Wootters inputs to every pure and mixed AA'BB'
state. In particular, the auxiliary dimensions are never restricted to qubits.
The fixed-axis input is explicit here and will be supplied by the concurrence
branch when the final declarations are integrated.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

namespace EC2
open ConcurrenceGeometry

/-- The exact Eq. 13 proposition, with both fixed axes universally quantified. -/
def FixedAxisConcurrence : Prop :=
  ∀ (ρ : MState (Q × Q)) (n m : Vec3),
    IsMarginalAxis (marginalBlochA ρ) n →
    IsMarginalAxis (marginalBlochB ρ) m →
    concurrence ρ ≤ transverseBound ρ n m

section Auxiliary
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] [Nonempty b]

/-- Eq. 25 with the actual rectangular coefficient matrix, physical
measurement probabilities, and exact auxiliary ensemble. -/
theorem pure_entropy_from_fixed_axis
    (hfixed : FixedAxisConcurrence)
    (hWootters : Literature.WoottersFormation)
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (ψ : Ket ((Q × a) × (Q × b))) :
    formationBits (marginalAB (MState.pure ψ)) +
      formationBits (marginalAux (MState.pure ψ)) ≤
        entropyBits (MState.pure ψ).traceRight := by
  let ρ := marginalAB (MState.pure ψ)
  obtain ⟨n,hn⟩ := exists_marginal_axis (marginalBlochA ρ)
  obtain ⟨m,hm⟩ := exists_marginal_axis (marginalBlochB ρ)
  obtain ⟨U,V,κ,hκ,hbal⟩ := exists_balanced_maximizing_measurement ρ n m hn hm
  have hc : concurrence ρ ≤ |κ| := by
    rw [hκ]
    exact hfixed ρ n m hn hm
  have hAB : formationBits ρ ≤ Entropy.wBits |κ| := by
    rw [hWootters ρ]
    exact Entropy.wBits_monotoneOn
      ⟨concurrence_nonneg ρ, concurrence_le_one ρ⟩
      ⟨abs_nonneg κ, hbal.abs_le_one⟩ hc
  have hw (i j : Q) :
      matrixWeight (matrixBlock (coefficientMatrix (qubitBasisKet ψ U V)) i j) =
        measurementProbability (localConj ρ U V) i j := by
    rw [matrixBlock_weight_eq_AB_probability, pure_qubitBasisKet,
      marginalAB_qubitBasisChange]
  apply pure_entropy_bound_of_qubit_measurement ψ U V ((1+κ)/2) ((1-κ)/2)
  · rw [hw, hbal.p00]
    ring
  · rw [hw, hbal.p01]
    ring
  · rw [hw, hbal.p10]
    ring
  · rw [hw, hbal.p11]
    ring
  · ring
  · exact hHanner
  · have he : (1+κ)/2 - (1-κ)/2 = κ := by ring
    simpa only [he] using hAB

/-- The full mixed-state Eq. 1 follows from the actual fixed-axis lemma and
only the established Hanner and Wootters inputs, at arbitrary finite a,b. -/
theorem strong_superadditivity_from_fixed_axis
    (hfixed : FixedAxisConcurrence)
    (hWootters : Literature.WoottersFormation)
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (Ω : MState ((Q × a) × (Q × b))) :
    formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω :=
  strong_superadditivity_of_pure_entropy
    (pure_entropy_from_fixed_axis hfixed hWootters hHanner) Ω

end Auxiliary
end EC2
