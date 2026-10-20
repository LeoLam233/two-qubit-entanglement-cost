import EC2.Quantum

/-! Finite projective conditional ensembles, including zero-probability outcomes,
and the exact marginal/mixture identities used in EC2 Section 4. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate

namespace EC2

section Conditional
variable {ι d : Type} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

def vectorWeight (v : d → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

theorem vectorWeight_nonneg (v : d → ℂ) : 0 ≤ vectorWeight v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem vectorWeight_pos (v : d → ℂ) (h : ∃ j, v j ≠ 0) : 0 < vectorWeight v := by
  obtain ⟨j,hj⟩ := h
  have hs : 0 < Complex.normSq (v j) := Complex.normSq_pos.mpr hj
  exact lt_of_lt_of_le hs (Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset d)) => Complex.normSq_nonneg (v k))
    (Finset.mem_univ j))

/-- A zero vector contributes only at zero weight, where any normalized ket can be used. -/
def conditionalKet (v : d → ℂ) : Ket d :=
  if h : ∃ j, v j ≠ 0 then Ket.normalize v h else default

theorem weighted_conditionalKet_entry (v : d → ℂ) (a b : d) :
    (vectorWeight v : ℂ) * (MState.pure (conditionalKet v)).m a b =
      v a * conj (v b) := by
  classical
  by_cases h : ∃ j, v j ≠ 0
  · have hp := vectorWeight_pos v h
    have hs : Real.sqrt (vectorWeight v) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    have hsc : (Real.sqrt (vectorWeight v) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hs2 : (Real.sqrt (vectorWeight v) : ℂ) ^ 2 = (vectorWeight v : ℂ) := by
      exact_mod_cast Real.sq_sqrt hp.le
    simp only [conditionalKet, dite_eq_left h, MState.m, MState.pure,
      HermitianMat.mat_mk, Matrix.vecMulVec_apply, Bra.eq_conj, Ket.apply,
      Ket.normalize, ← Complex.normSq_eq_norm_sq]
    change (vectorWeight v : ℂ) *
      ((v a / (Real.sqrt (vectorWeight v) : ℂ)) *
        conj (v b / (Real.sqrt (vectorWeight v) : ℂ))) = _
    simp only [map_div₀, Complex.conj_ofReal]
    rw [← hs2]
    field_simp [hsc]
  · have hz : ∀ j, v j = 0 := by simpa using h
    simp [vectorWeight, hz]

def componentWeight (ψ : Ket (ι × d)) (i : ι) : ℝ :=
  vectorWeight (fun j => ψ (i,j))

theorem componentWeight_sum (ψ : Ket (ι × d)) : ∑ i, componentWeight ψ i = 1 := by
  simpa [componentWeight, vectorWeight, Fintype.sum_prod_type] using ψ.normalized

def conditionalEnsemble (ψ : Ket (ι × d)) : PEnsemble d ι where
  var i := conditionalKet (fun j => ψ (i,j))
  distr := ProbDistribution.mk' (componentWeight ψ)
    (fun _ => vectorWeight_nonneg _) (componentWeight_sum ψ)

theorem conditionalEnsemble_mix [DecidableEq ι] (ψ : Ket (ι × d)) :
    Ensemble.mix (Ensemble.toMEnsemble (conditionalEnsemble ψ)) =
      (MState.pure ψ).traceLeft := by
  apply MState.ext_m
  ext a b
  rw [Ensemble.mix_of]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  change (∑ i, (componentWeight ψ i : ℂ) *
    (MState.pure (conditionalKet (fun j => ψ (i,j)))).m a b) =
    ∑ i, ψ (i,a) * conj (ψ (i,b))
  apply Finset.sum_congr rfl
  intro i _
  exact weighted_conditionalKet_entry _ _ _

end Conditional

section Mixing
variable {ι a b : Type} [Fintype ι] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]

theorem traceRight_mix (e : MEnsemble (a × b) ι) :
    (Ensemble.mix e).traceRight = Ensemble.mix (MState.traceRight <$> e) := by
  apply MState.ext_m
  ext i j
  change (∑ k : b, (Ensemble.mix e).m (i,k) (j,k)) =
    (Ensemble.mix (MState.traceRight <$> e)).m i j
  simp only [Ensemble.mix_of, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  change (∑ k : b, (e.distr l : ℂ) * (e.states l).m (i,k) (j,k)) =
    (e.distr l : ℂ) * ∑ k : b, (e.states l).m (i,k) (j,k)
  rw [Finset.mul_sum]

theorem traceLeft_mix (e : MEnsemble (a × b) ι) :
    (Ensemble.mix e).traceLeft = Ensemble.mix (MState.traceLeft <$> e) := by
  apply MState.ext_m
  ext i j
  change (∑ k : a, (Ensemble.mix e).m (k,i) (k,j)) =
    (Ensemble.mix (MState.traceLeft <$> e)).m i j
  simp only [Ensemble.mix_of, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  change (∑ k : a, (e.distr l : ℂ) * (e.states l).m (k,i) (k,j)) =
    (e.distr l : ℂ) * ∑ k : a, (e.states l).m (k,i) (k,j)
  rw [Finset.mul_sum]

theorem relabel_mix {c : Type} [Fintype c] [DecidableEq c]
    (e : MEnsemble a ι) (f : c ≃ a) :
    (Ensemble.mix e).relabel f = Ensemble.mix ((fun ρ => ρ.relabel f) <$> e) := by
  apply MState.ext_m
  ext i j
  simp only [MState.relabel_m, Ensemble.mix_of, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  rfl

theorem marginalAB_mix (e : MEnsemble ((Q × a) × (Q × b)) ι) :
    marginalAB (Ensemble.mix e) = Ensemble.mix (marginalAB <$> e) := by
  simp only [marginalAB, relabel_mix, traceRight_mix, Functor.map_map]
  rfl

theorem marginalAux_mix (e : MEnsemble ((Q × a) × (Q × b)) ι) :
    marginalAux (Ensemble.mix e) = Ensemble.mix (marginalAux <$> e) := by
  simp only [marginalAux, relabel_mix, traceLeft_mix, Functor.map_map]
  rfl

end Mixing

/-- Uniform local measurement probabilities give exactly the balanced joint weights of Eq. 23. -/
theorem joint_probabilities_balanced (p00 p01 p10 p11 κ : ℝ)
    (hrow0 : p00 + p01 = 1/2) (hrow1 : p10 + p11 = 1/2)
    (hcol0 : p00 + p10 = 1/2) (hcol1 : p01 + p11 = 1/2)
    (hcorr : p00 - p01 - p10 + p11 = κ) :
    p00 = (1+κ)/4 ∧ p11 = (1+κ)/4 ∧
    p01 = (1-κ)/4 ∧ p10 = (1-κ)/4 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end EC2
