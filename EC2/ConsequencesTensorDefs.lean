import EC2.Quantum

/-!
# Concrete finite tensor powers and their regularized formation cost

`qubitTensorPowerSucc ρ n` is the ordinary tensor product of `n + 1` copies
of the two-qubit state `ρ`, grouped across the bipartition
`A₁⋯Aₙ₊₁ : B₁⋯Bₙ₊₁`. This representation covers every positive tensor
power and makes each application of the arbitrary-partner theorem explicit.

The definitions in this module impose no entanglement inequality assumption.
-/

noncomputable section

namespace EC2

/-- The local basis of `n + 1` qubits, with a fixed recursive grouping. -/
def QCopies : ℕ → Type
  | 0 => Q
  | n + 1 => Q × QCopies n

instance qCopiesFintype : (n : ℕ) → Fintype (QCopies n)
  | 0 => inferInstanceAs (Fintype Q)
  | n + 1 => letI := qCopiesFintype n
             inferInstanceAs (Fintype (Q × QCopies n))

instance qCopiesDecidableEq : (n : ℕ) → DecidableEq (QCopies n)
  | 0 => inferInstanceAs (DecidableEq Q)
  | n + 1 => letI := qCopiesDecidableEq n
             inferInstanceAs (DecidableEq (Q × QCopies n))

instance qCopiesNonempty : (n : ℕ) → Nonempty (QCopies n)
  | 0 => inferInstanceAs (Nonempty Q)
  | n + 1 => letI := qCopiesNonempty n
             inferInstanceAs (Nonempty (Q × QCopies n))

/-- The exact local dimension of the recursively grouped positive tensor powers. -/
theorem qCopies_card (n : ℕ) : Fintype.card (QCopies n) = 2 ^ (n + 1) := by
  induction n with
  | zero => exact Fintype.card_fin 2
  | succ n ih =>
    change Fintype.card (Q × QCopies n) = _
    rw [Fintype.card_prod, ih]
    simp [Q, pow_succ, Nat.mul_comm]

/-- `n + 1` identical two-qubit factors with the exact local tensor bipartition. -/
def qubitTensorPowerSucc (ρ : MState (Q × Q)) :
    (n : ℕ) → MState (QCopies n × QCopies n)
  | 0 => ρ
  | n + 1 => partnerProduct ρ (qubitTensorPowerSucc ρ n)

/-- A positive-index interface for the ordinary `n`th tensor power. -/
def qubitTensorPower (ρ : MState (Q × Q)) (n : ℕ) (_hn : 0 < n) :
    MState (QCopies (n - 1) × QCopies (n - 1)) :=
  qubitTensorPowerSucc ρ (n - 1)


end EC2
