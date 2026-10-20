import EC2.ConcurrenceQuantum
import EC2.EntropyMatrix

/-! # Precisely stated published inputs

These propositions are interfaces, not additional axioms. Theorems using
them retain the corresponding proof arguments, so an axiom audit cannot
hide an unformalized literature result. None assumes an EC2 claim.

* W. K. Wootters, quant-ph/9709029: the ordinary two-qubit EoF formula.
* Otte Heinävaara, arXiv:2310.03227: the complex Schatten Hanner inequality
  (its exact finite rectangular form is `Entropy.RectangularHanner`).
* The operational HHT interface is in `EC2.ConsequencesOperational`.
-/
noncomputable section
namespace EC2.Literature

/-- The published Wootters formula, in bits, for every two-qubit density
state. The concurrence on the right is the ordinary pure-state convex roof. -/
def WoottersFormation : Prop :=
  ∀ ρ : MState (Q × Q), formationBits ρ = Entropy.wBits (concurrence ρ)

/-- The published complex Schatten Hanner inequality at every finite
rectangular dimension and every real exponent at least two. -/
def ComplexRectangularHanner : Prop :=
  ∀ (r s : Type) [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s],
    Entropy.RectangularHanner r s

end EC2.Literature
