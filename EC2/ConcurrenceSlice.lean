import EC2.ConcurrenceContinuity
import EC2.ConcurrenceSupport
import Mathlib.Analysis.Convex.KreinMilman

/-! # Compact convex fixed slice and its actual quantum-state parametrization -/

noncomputable section
open scoped BigOperators ComplexConjugate
open Set
set_option backward.isDefEq.respectTransparency false

namespace EC2.ConcurrenceReduction

@[fun_prop] theorem continuous_sliceEqualities : Continuous sliceEqualities :=
  sliceEqualities.continuous_of_finiteDimensional

@[fun_prop] theorem continuous_signCoordinates : Continuous signCoordinates :=
  signCoordinates.continuous_of_finiteDimensional

theorem fixedSlice_trace {ρ : HermitianMat (Fin 4) ℂ} (hρ : ρ ∈ fixedSlice) :
    ρ.trace = 1 := congrFun hρ.2.1 0

theorem isClosed_fixedSlice : IsClosed fixedSlice := by
  unfold fixedSlice
  exact (isClosed_le continuous_const continuous_id).inter
    ((isClosed_eq continuous_sliceEqualities continuous_const).inter
      ((isClosed_le continuous_const ((continuous_apply 0).comp continuous_signCoordinates)).inter
        (isClosed_le continuous_const ((continuous_apply 1).comp continuous_signCoordinates))))

theorem convex_fixedSlice : Convex ℝ fixedSlice := by
  intro A hA B hB a b ha hb hab
  refine ⟨add_nonneg (smul_nonneg ha hA.1) (smul_nonneg hb hB.1), ?_, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hA.2.1, hB.2.1, ← add_smul, hab, one_smul]
  · simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha hA.2.2.1) (mul_nonneg hb hB.2.2.1)
  · simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha hA.2.2.2) (mul_nonneg hb hB.2.2.2)

theorem isCompact_fixedSlice : IsCompact fixedSlice := by
  apply (isCompact_Icc : IsCompact (Icc (0 : HermitianMat (Fin 4) ℂ) 1)).of_isClosed_subset
    isClosed_fixedSlice
  intro ρ hρ
  refine ⟨hρ.1, ?_⟩
  simpa only [fixedSlice_trace hρ, one_smul] using HermitianMat.le_trace_smul_one hρ.1

/-- Computational order `00,01,10,11` as an actual equivalence. -/
def qubitIndexEquiv : Fin 4 ≃ (Q × Q) where
  toFun := twoQubitIndex
  invFun p := ![![0,1], ![2,3]] p.1 p.2
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl

theorem qubitIndexEquiv_apply (i : Fin 4) : qubitIndexEquiv i = twoQubitIndex i := rfl

/-- Every matrix in the slice is a normalized two-qubit density matrix. -/
def sliceState (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice) : MState (Q × Q) where
  M := ρ.reindex qubitIndexEquiv
  nonneg := by
    rw [HermitianMat.reindex_eq_conj]
    exact HermitianMat.conj_nonneg _ hρ.1
  tr := by rw [HermitianMat.trace_reindex]; exact fixedSlice_trace hρ

@[simp] theorem qubitHermitian_sliceState (ρ : HermitianMat (Fin 4) ℂ)
    (hρ : ρ ∈ fixedSlice) : qubitHermitian (sliceState ρ hρ) = ρ := by
  apply Subtype.ext
  ext i j
  change ρ.mat (qubitIndexEquiv.symm (qubitIndexEquiv i))
    (qubitIndexEquiv.symm (qubitIndexEquiv j)) = ρ.mat i j
  rw [qubitIndexEquiv.symm_apply_apply, qubitIndexEquiv.symm_apply_apply]

theorem concurrence_sliceState (hWootters : WoottersSpectralFormula)
    (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice) :
    concurrence (sliceState ρ hρ) = spectralConcurrence ρ := by
  rw [hWootters _, qubitHermitian_sliceState]

/-- The affine witness appearing in the fixed computational slice. -/
def sliceWitness : HermitianMat (Fin 4) ℂ →ₗ[ℝ] ℝ where
  toFun ρ := 2 * (signCoordinates ρ 0 + signCoordinates ρ 1)
  map_add' A B := by simp [map_add]; ring
  map_smul' c A := by simp [map_smul]; ring

@[fun_prop] theorem continuous_sliceWitness : Continuous sliceWitness :=
  sliceWitness.continuous_of_finiteDimensional

def qubitHermitianLinear : HermitianMat (Q × Q) ℂ →ₗ[ℝ] HermitianMat (Fin 4) ℂ where
  toFun H := ⟨H.mat.submatrix twoQubitIndex twoQubitIndex, H.H.submatrix twoQubitIndex⟩
  map_add' A B := by apply Subtype.ext; rfl
  map_smul' c A := by apply Subtype.ext; rfl

theorem qubitHermitian_mix {ι : Type} [Fintype ι] (e : MEnsemble (Q × Q) ι) :
    qubitHermitian (Ensemble.mix e) = ∑ i, (e.distr i : ℝ) • qubitHermitian (e.states i) := by
  have hmix : (Ensemble.mix e).M = ∑ i, (e.distr i : ℝ) • (e.states i).M := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    exact Ensemble.mix_of e
  change qubitHermitianLinear (Ensemble.mix e).M =
    ∑ i, (e.distr i : ℝ) • qubitHermitianLinear (e.states i).M
  rw [hmix, map_sum]
  simp only [map_smul]

/-- Convexity of the continuous spectral expression is proved by identifying
it with the actual convex roof and using its proved finite Jensen theorem. -/
theorem convexOn_spectralConcurrence (hWootters : WoottersSpectralFormula) :
    ConvexOn ℝ fixedSlice spectralConcurrence := by
  refine ⟨convex_fixedSlice, ?_⟩
  intro A hA B hB a b ha hb hab
  let e : MEnsemble (Q × Q) (Fin 2) :=
    ⟨![sliceState A hA, sliceState B hB], ProbDistribution.mk' ![a,b]
      (by intro i; fin_cases i <;> assumption)
      (by simpa [Fin.sum_univ_two] using hab)⟩
  have hmix : qubitHermitian (Ensemble.mix e) = a • A + b • B := by
    rw [qubitHermitian_mix, Fin.sum_univ_two]
    change a • qubitHermitian (sliceState A hA) + b • qubitHermitian (sliceState B hB) = _
    simp only [qubitHermitian_sliceState]
  have h := concurrence_finite_jensen e
  rw [hWootters _, hmix, Fin.sum_univ_two] at h
  change spectralConcurrence (a • A + b • B) ≤
    a * concurrence (sliceState A hA) + b * concurrence (sliceState B hB) at h
  simpa only [concurrence_sliceState hWootters, smul_eq_mul] using h

/-- A continuous convex bound on the rank-two and zero-face terminals
extends to every point of the actual compact slice. Its geometric input
is the proved supported-perturbation extreme-point classification. -/
theorem fixedSlice_bound_of_terminals (f : HermitianMat (Fin 4) ℂ → ℝ)
    (hf : Continuous f) (hc : ConvexOn ℝ fixedSlice f)
    (hrank : ∀ ρ ∈ fixedSlice, ρ.mat.rank ≤ 2 → f ρ ≤ sliceWitness ρ)
    (hzero : ∀ ρ ∈ fixedSlice,
      signCoordinates ρ 0 = 0 → signCoordinates ρ 1 = 0 → f ρ ≤ sliceWitness ρ) :
    ∀ ρ ∈ fixedSlice, f ρ ≤ sliceWitness ρ := by
  let S : Set (HermitianMat (Fin 4) ℂ) := {ρ | ρ ∈ fixedSlice ∧ f ρ ≤ sliceWitness ρ}
  have hSclosed : IsClosed S := isClosed_fixedSlice.inter
    (isClosed_le hf continuous_sliceWitness)
  have hSconvex : Convex ℝ S := by
    intro A hA B hB a b ha hb hab
    refine ⟨convex_fixedSlice hA.1 hB.1 ha hb hab, ?_⟩
    calc
      f (a • A + b • B) ≤ a * f A + b * f B := hc.2 hA.1 hB.1 ha hb hab
      _ ≤ a * sliceWitness A + b * sliceWitness B :=
        add_le_add (mul_le_mul_of_nonneg_left hA.2 ha) (mul_le_mul_of_nonneg_left hB.2 hb)
      _ = sliceWitness (a • A + b • B) := by simp only [map_add, map_smul, smul_eq_mul]
  have hExt : fixedSlice.extremePoints ℝ ⊆ S := by
    intro ρ hρ
    refine ⟨hρ.1, ?_⟩
    rcases extreme_fixedSlice_rank_or_zero ρ hρ with hr | ⟨hw,hz⟩
    · exact hrank ρ hρ.1 hr
    · exact hzero ρ hρ.1 hw hz
  have hclosure := closure_minimal (convexHull_min hExt hSconvex) hSclosed
  rw [closure_convexHull_extremePoints isCompact_fixedSlice convex_fixedSlice] at hclosure
  intro ρ hρ
  exact (hclosure hρ).2

/-- The all-rank step of EC2 §3.2. The only non-geometric literature input is
the exact Wootters formula. Rank-two and zero-face inputs are separated
terminal results, to be supplied by their constructive EC2 proofs. -/
theorem all_rank_fixedSlice_bound (hWootters : WoottersSpectralFormula)
    (hrank : ∀ (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice),
      ρ.mat.rank ≤ 2 → concurrence (sliceState ρ hρ) ≤ sliceWitness ρ)
    (hzero : ∀ (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice),
      signCoordinates ρ 0 = 0 → signCoordinates ρ 1 = 0 →
        concurrence (sliceState ρ hρ) = 0) :
    ∀ (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice),
      concurrence (sliceState ρ hρ) ≤ sliceWitness ρ := by
  have hbound := fixedSlice_bound_of_terminals spectralConcurrence
    continuous_spectralConcurrence (convexOn_spectralConcurrence hWootters) ?_ ?_
  · intro ρ hρ
    simpa only [concurrence_sliceState hWootters] using hbound ρ hρ
  · intro ρ hρ hr
    simpa only [concurrence_sliceState hWootters] using hrank ρ hρ hr
  · intro ρ hρ hw hz
    have hC : spectralConcurrence ρ = 0 := by
      simpa only [concurrence_sliceState hWootters] using hzero ρ hρ hw hz
    rw [hC]
    exact mul_nonneg (by norm_num) (add_nonneg hρ.2.2.1 hρ.2.2.2)

end EC2.ConcurrenceReduction
