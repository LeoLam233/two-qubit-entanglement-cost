import EC2.ConsequencesTensorDefs
import QuantumInfo.States.Mixed.TraceDistance
import Mathlib.Topology.Order.Basic

/-!
# A concrete operational entanglement-cost definition

The protocol relation below describes finite adaptive LOCC trees. Each node is
a complete local Kraus instrument; its outcome is freely available to both
parties when choosing the continuation. Rectangular Kraus matrices allow local
ancillas and discarding local systems. All branches are summed, so the protocol
has no postselection. The only shared input resource in dilution is an integer
number of ordinary Bell pairs. The number of rounds, outcomes, and all local
ancilla dimensions may vary without bound along the asymptotic sequence.

The cost is an extended-real infimum of nonnegative achievable Bell-pair rates
with vanishing trace-distance error. It is not defined using a convex-roof
regularization formula.
-/

noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker ENNReal

namespace EC2.Operational

/-- An unnormalized matrix on a finite bipartite system. -/
abbrev BipMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

/-- One Alice outcome, acting only on her local factor. -/
def aliceBranch {a a' b : ℕ} (K : Matrix (Fin a') (Fin a) ℂ)
    (X : BipMatrix a b) : BipMatrix a' b :=
  (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * X *
    (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ

/-- One Bob outcome, acting only on his local factor. -/
def bobBranch {a b b' : ℕ} (K : Matrix (Fin b') (Fin b) ℂ)
    (X : BipMatrix a b) : BipMatrix a b' :=
  ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K) * X *
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K)ᴴ

/--
A finite LOCC tree acting on unnormalized matrices. Completeness is imposed at
every local instrument, and all outcome branches are retained and summed.
This relation has no constructor for an arbitrary separable operation.
-/
inductive FiniteLOCC : {a b c d : ℕ} → BipMatrix a b → BipMatrix c d → Prop
  | identity {a b : ℕ} (X : BipMatrix a b) : FiniteLOCC X X
  | alice {a a' b c d r : ℕ}
      (K : Fin r → Matrix (Fin a') (Fin a) ℂ)
      (complete : ∑ i, (K i)ᴴ * K i = 1)
      (X : BipMatrix a b) (Y : Fin r → BipMatrix c d)
      (branches : ∀ i, FiniteLOCC (aliceBranch (K i) X) (Y i)) :
      FiniteLOCC X (∑ i, Y i)
  | bob {a b b' c d r : ℕ}
      (K : Fin r → Matrix (Fin b') (Fin b) ℂ)
      (complete : ∑ i, (K i)ᴴ * K i = 1)
      (X : BipMatrix a b) (Y : Fin r → BipMatrix c d)
      (branches : ∀ i, FiniteLOCC (bobBranch (K i) X) (Y i)) :
      FiniteLOCC X (∑ i, Y i)

/-- Every protocol tree preserves positivity, including its zero-probability branches. -/
theorem FiniteLOCC.preserves_posSemidef {a b c d : ℕ}
    {X : BipMatrix a b} {Y : BipMatrix c d} (h : FiniteLOCC X Y) :
    X.PosSemidef → Y.PosSemidef := by
  induction h with
  | identity X => exact id
  | alice K complete X Y branches ih =>
    intro hX
    exact Matrix.posSemidef_sum Finset.univ
      (fun i _ => ih i (hX.mul_mul_conjTranspose_same _))
  | bob K complete X Y branches ih =>
    intro hX
    exact Matrix.posSemidef_sum Finset.univ
      (fun i _ => ih i (hX.mul_mul_conjTranspose_same _))

/-- The recursive local tensor basis relabeled as the standard finite index type. -/
def tensorBasisEquiv (n : ℕ) : QCopies n ≃ Fin (2 ^ (n + 1)) :=
  (Fintype.equivFin (QCopies n)).trans (finCongr (qCopies_card n))

/-- The actual `n + 1` tensor power in standard local finite bases. -/
def tensorTarget (ρ : MState (Q × Q)) (n : ℕ) :
    MState (Fin (2 ^ (n + 1)) × Fin (2 ^ (n + 1))) :=
  (qubitTensorPowerSucc ρ n).relabel
    ((tensorBasisEquiv n).symm.prodCongr (tensorBasisEquiv n).symm)

/-- One ordinary Bell pair. -/
def bellPair : MState (Q × Q) := MState.pure (Ket.MES Q)

/-- Exactly `k` ordinary Bell pairs, with their local factors grouped together. -/
def bellPairs : (k : ℕ) → MState (Fin (2 ^ k) × Fin (2 ^ k))
  | 0 => MState.pure (Ket.MES (Fin 1))
  | k + 1 => tensorTarget bellPair k

/-- The positive Bell resource is the corresponding actual tensor product. -/
theorem bellPairs_succ (k : ℕ) : bellPairs (k + 1) = tensorTarget bellPair k := rfl

/--
A Bell-pair rate is achievable by dilution when complete finite LOCC protocols
prepare all positive tensor powers with vanishing trace-distance error and the
consumed number of Bell pairs per output copy tends to that rate.
-/
def AchievableDilutionRate (ρ : MState (Q × Q)) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ (k : ℕ → ℕ)
    (outputs : (n : ℕ) → MState (Fin (2 ^ (n + 1)) × Fin (2 ^ (n + 1)))),
    (∀ n, FiniteLOCC (bellPairs (k n)).m (outputs n).m) ∧
    Tendsto (fun n => TrDistance (outputs n) (tensorTarget ρ n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (k n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 R)

/--
Operational entanglement cost in Bell pairs per copy. The value is `∞` if no
finite rate is achievable, by the extended-real infimum convention.
-/
def entanglementCost (ρ : MState (Q × Q)) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {R : ℝ | AchievableDilutionRate ρ R})

/-- An actual dilution protocol family gives the corresponding operational upper bound. -/
theorem entanglementCost_le_of_achievable (ρ : MState (Q × Q)) {R : ℝ}
    (hR : AchievableDilutionRate ρ R) : entanglementCost ρ ≤ ENNReal.ofReal R := by
  exact sInf_le ⟨R, hR, rfl⟩

end EC2.Operational
