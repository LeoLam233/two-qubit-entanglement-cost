import EC2.ConsequencesLOCC

/-! Completeness of each local instrument makes the concrete LOCC relation trace preserving. -/

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker Matrix

namespace EC2.Operational

/-- A complete finite Kraus instrument preserves the total trace. -/
theorem complete_kraus_trace {m n ι : Type} [Fintype m] [Fintype n] [Fintype ι]
    [DecidableEq n] (K : ι → Matrix m n ℂ)
    (complete : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix n n ℂ) :
    (∑ i, K i * X * (K i)ᴴ).trace = X.trace := by
  calc
    (∑ i, K i * X * (K i)ᴴ).trace = ∑ i, ((K i)ᴴ * K i * X).trace := by
      rw [Matrix.trace_sum]
      exact Finset.sum_congr rfl (fun i _ => Matrix.trace_mul_cycle (K i) X (K i)ᴴ)
    _ = ((∑ i, (K i)ᴴ * K i) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [complete, Matrix.one_mul]

/-- Completeness of Alice's local instrument also holds on the full bipartite system. -/
theorem alice_kraus_complete {a a' b r : ℕ}
    (K : Fin r → Matrix (Fin a') (Fin a) ℂ)
    (complete : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, (K i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ *
      (K i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = 1 := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    (∑ i, ((K i)ᴴ * K i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
        (∑ i, (K i)ᴴ * K i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
      ext ⟨x₁,x₂⟩ ⟨y₁,y₂⟩
      simp only [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]
    _ = 1 := by rw [complete, Matrix.one_kronecker_one]

/-- Completeness of Bob's local instrument also holds on the full bipartite system. -/
theorem bob_kraus_complete {a b b' r : ℕ}
    (K : Fin r → Matrix (Fin b') (Fin b) ℂ)
    (complete : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K i)ᴴ *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K i) = 1 := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    (∑ i, (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ ((K i)ᴴ * K i)) =
        (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (∑ i, (K i)ᴴ * K i) := by
      ext ⟨x₁,x₂⟩ ⟨y₁,y₂⟩
      simp only [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]
    _ = 1 := by rw [complete, Matrix.one_kronecker_one]

/-- Every concrete finite LOCC protocol preserves total probability; no outcome is postselected. -/
theorem FiniteLOCC.preserves_trace {a b c d : ℕ}
    {X : BipMatrix a b} {Y : BipMatrix c d} (h : FiniteLOCC X Y) :
    Y.trace = X.trace := by
  induction h with
  | identity X => rfl
  | alice K complete X Y branches ih =>
    calc
      (∑ i, Y i).trace = (∑ i, aliceBranch (K i) X).trace := by
        rw [Matrix.trace_sum, Matrix.trace_sum]
        exact Finset.sum_congr rfl (fun i _ => ih i)
      _ = X.trace := complete_kraus_trace _ (alice_kraus_complete K complete) X
  | bob K complete X Y branches ih =>
    calc
      (∑ i, Y i).trace = (∑ i, bobBranch (K i) X).trace := by
        rw [Matrix.trace_sum, Matrix.trace_sum]
        exact Finset.sum_congr rfl (fun i _ => ih i)
      _ = X.trace := complete_kraus_trace _ (bob_kraus_complete K complete) X

end EC2.Operational
