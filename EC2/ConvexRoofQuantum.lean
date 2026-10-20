import EC2.ConvexRoof
import QuantumInfo.States.Entanglement

/-!
# Identification with Physlib's finite-dimensional quantum convex roof

This file identifies the graph-hull infimum with the library definition of
`convex_roof`. Both definitions optimize over finite pure-state ensembles.
Physlib's entropy convention is natural logarithms; bits are obtained by dividing
by `Real.log 2` in the EC2 target definitions.
-/

noncomputable section

open Set Finset Ensemble MState
open scoped BigOperators NNReal

namespace EC2

variable {d : Type} [Fintype d] [DecidableEq d]

/-- A normalized pure ket regarded as a Hermitian density matrix. -/
def pureMatrix (ψ : Ket d) : HermitianMat d ℂ := (MState.pure ψ).M

/-- The matrix underlying an ensemble mixture is its weighted matrix sum. -/
theorem mixture_matrix {ι : Type} [Fintype ι] (e : MEnsemble d ι) :
    (Ensemble.mix e).M = ∑ i, (e.distr i : ℝ) • (e.states i).M := by
  rfl

/-- The real-valued pure ensemble average is the ordinary finite weighted sum. -/
theorem pure_average_real {ι : Type} [Fintype ι]
    (g : KetUpToPhase d → ℝ≥0) (e : PEnsemble d ι) :
    (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ) =
      ∑ i, (e.distr i : ℝ) * (g (KetUpToPhase.mk (e.states i)) : ℝ) := by
  rfl

/-- Every normalized positive matrix belongs to the finite pure-mixture domain. -/
theorem density_mem_pureMatrix_domain (ρ : MState d) :
    ρ.M ∈ ConvexRoof.domain (pureMatrix (d := d)) := by
  let e := spectral_ensemble ρ
  have h : (Ensemble.mix (toMEnsemble e)).M ∈
      ConvexRoof.domain (pureMatrix (d := d)) := by
    rw [mixture_matrix]
    apply (convex_convexHull ℝ (range (pureMatrix (d := d)))).sum_mem
    · intro i _
      exact (e.distr i).zero_le_coe
    · exact e.distr.normalized
    · intro i _
      exact subset_convexHull ℝ _ (mem_range_self (e.states i))
  simpa [e, spectral_ensemble_mix] using h

/-- The finite pure-mixture domain is exactly the full set of density matrices. -/
theorem pureMatrix_domain_eq : ConvexRoof.domain (pureMatrix (d := d)) =
    range (MState.M (d := d)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨ψ, rfl⟩
      exact mem_range_self (MState.pure ψ)
    · exact MState.convex d
  · rintro _ ⟨ρ, rfl⟩
    exact density_mem_pureMatrix_domain ρ

/-- The graph-hull formulation of the phase-invariant pure-state convex roof. -/
def quantumRoof (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) : ℝ :=
  ConvexRoof.roof pureMatrix (fun ψ => (g (KetUpToPhase.mk ψ) : ℝ)) ρ.M

/-- Nonnegativity of the graph-hull quantum roof. -/
theorem quantumRoof_nonneg (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) :
    0 ≤ quantumRoof g ρ :=
  ConvexRoof.roof_nonneg _ _ (fun ψ => (g (KetUpToPhase.mk ψ)).coe_nonneg)
    (density_mem_pureMatrix_domain ρ)

/-- Each Physlib pure ensemble gives an upper bound for the graph-hull roof. -/
theorem quantumRoof_le_pure_average {ι : Type} [Fintype ι]
    (g : KetUpToPhase d → ℝ≥0) (e : PEnsemble d ι) :
    quantumRoof g (Ensemble.mix (toMEnsemble e)) ≤
      (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ) := by
  unfold quantumRoof
  rw [mixture_matrix, pure_average_real]
  exact ConvexRoof.roof_le_of_mem _ _
    (fun ψ => (g (KetUpToPhase.mk ψ)).coe_nonneg)
    (ConvexRoof.sum_mem_values _ _ Finset.univ (fun i => (e.distr i : ℝ)) e.states
      (fun i _ => (e.distr i).zero_le_coe) e.distr.normalized)

/-- One direction of the exact bridge to Physlib's convex roof. -/
theorem quantumRoof_le_convex_roof [Nonempty d]
    (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) :
    quantumRoof g ρ ≤ (convex_roof g ρ : ℝ) := by
  have h : (⟨quantumRoof g ρ, quantumRoof_nonneg g ρ⟩ : ℝ≥0) ≤ convex_roof g ρ := by
    apply le_convex_roof g ρ
    intro n hn e hmix
    change quantumRoof g ρ ≤ (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ)
    rw [← hmix]
    exact quantumRoof_le_pure_average g e
  exact h

/-- Reindexing a pure ensemble preserves its average cost. -/
theorem pure_average_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (g : KetUpToPhase d → ℝ≥0) (e : PEnsemble d ι) (eidx : ι ≃ κ) :
    pure_average_NNReal (g ∘ KetUpToPhase.mk) (congrPEnsemble eidx e) =
      pure_average_NNReal (g ∘ KetUpToPhase.mk) e := by
  apply NNReal.eq
  change ProbDistribution.expect_val ((fun ψ => (g (KetUpToPhase.mk ψ) : ℝ)) <$>
    (ProbDistribution.congrRandVar eidx e)) =
    ProbDistribution.expect_val ((fun ψ => (g (KetUpToPhase.mk ψ) : ℝ)) <$> e)
  rw [ProbDistribution.map_congr_eq_congr_map]
  exact ProbDistribution.expect_val_congr_eq_expect_val eidx _

/-- Physlib's positive-integer indexing covers every finite pure-state ensemble. -/
theorem convex_roof_le_any_ensemble [Nonempty d] {ι : Type} [Fintype ι]
    (g : KetUpToPhase d → ℝ≥0) (e : PEnsemble d ι) :
    convex_roof g (Ensemble.mix (toMEnsemble e)) ≤
      pure_average_NNReal (g ∘ KetUpToPhase.mk) e := by
  letI : Nonempty ι := e.distr.nonempty
  apply convex_roof_le g
  refine ⟨Fintype.card ι, Fintype.card_pos,
    congrPEnsemble (Fintype.equivFin ι) e, ?_, ?_⟩
  · exact mix_congrPEnsemble_eq_mix _ _
  · exact le_of_eq (pure_average_reindex g e _)

/-- Every graph-hull ensemble is an ensemble accepted by Physlib's convex roof. -/
theorem convex_roof_le_quantumRoof [Nonempty d]
    (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) :
    (convex_roof g ρ : ℝ) ≤ quantumRoof g ρ := by
  classical
  apply le_csInf ((ConvexRoof.values_nonempty_iff _ _ _).mpr
    (density_mem_pureMatrix_domain ρ))
  intro c hc
  obtain ⟨s, w, hw, hsum, hstate, hcost⟩ := (ConvexRoof.mem_values_iff _ _ _ _).mp hc
  let prob : ProbDistribution s := ProbDistribution.mk' (fun p => w p)
    (fun p => hw p p.property) (by simpa only [Finset.sum_coe_sort] using hsum)
  let e : PEnsemble d s := ⟨fun p => p.val, prob⟩
  have hmix : Ensemble.mix (toMEnsemble e) = ρ := by
    apply MState.ext
    rw [mixture_matrix]
    change (∑ p : s, w p • pureMatrix p.val) = ρ.M
    exact (Finset.sum_coe_sort s (fun p => w p • pureMatrix p)).trans hstate
  have hc' : (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ) = c := by
    rw [pure_average_real]
    change (∑ p : s, w p * (g (KetUpToPhase.mk p.val) : ℝ)) = c
    exact (Finset.sum_coe_sort s (fun p => w p * (g (KetUpToPhase.mk p) : ℝ))).trans hcost
  rw [← hmix, ← hc']
  exact convex_roof_le_any_ensemble g e

/-- Exact equality of the graph-hull infimum and the imported quantum convex roof. -/
theorem quantumRoof_eq_convex_roof [Nonempty d]
    (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) :
    quantumRoof g ρ = (convex_roof g ρ : ℝ) :=
  le_antisymm (quantumRoof_le_convex_roof g ρ) (convex_roof_le_quantumRoof g ρ)

/-- Finite pure ensembles approximate the actual imported quantum roof arbitrarily well. -/
theorem exists_pure_ensemble_average_lt [Nonempty d]
    (g : KetUpToPhase d → ℝ≥0) (ρ : MState d) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (e : PEnsemble d (Fin n)),
      Ensemble.mix (toMEnsemble e) = ρ ∧
      (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ) < (convex_roof g ρ : ℝ) + ε := by
  classical
  obtain ⟨c, hc, hclt⟩ := ConvexRoof.exists_cost_lt pureMatrix
    (fun ψ => (g (KetUpToPhase.mk ψ) : ℝ)) (density_mem_pureMatrix_domain ρ) hε
  obtain ⟨s, w, hw, hsum, hstate, hcost⟩ := (ConvexRoof.mem_values_iff _ _ _ _).mp hc
  let prob : ProbDistribution s := ProbDistribution.mk' (fun p => w p)
    (fun p => hw p p.property) (by simpa only [Finset.sum_coe_sort] using hsum)
  let e : PEnsemble d s := ⟨fun p => p.val, prob⟩
  letI : Nonempty s := prob.nonempty
  have hmix : Ensemble.mix (toMEnsemble e) = ρ := by
    apply MState.ext
    rw [mixture_matrix]
    change (∑ p : s, w p • pureMatrix p.val) = ρ.M
    exact (Finset.sum_coe_sort s (fun p => w p • pureMatrix p)).trans hstate
  have hc' : (pure_average_NNReal (g ∘ KetUpToPhase.mk) e : ℝ) = c := by
    rw [pure_average_real]
    change (∑ p : s, w p * (g (KetUpToPhase.mk p.val) : ℝ)) = c
    exact (Finset.sum_coe_sort s (fun p => w p * (g (KetUpToPhase.mk p) : ℝ))).trans hcost
  refine ⟨Fintype.card s, Fintype.card_pos,
    congrPEnsemble (Fintype.equivFin s) e, ?_, ?_⟩
  · exact (mix_congrPEnsemble_eq_mix _ _).trans hmix
  · rw [pure_average_reindex, hc']
    change c < quantumRoof g ρ + ε at hclt
    simpa only [quantumRoof_eq_convex_roof] using hclt

/-- Jensen's inequality for Physlib's actual quantum convex roof and any finite mixed ensemble. -/
theorem convex_roof_finite_jensen [Nonempty d] {ι : Type} [Fintype ι]
    (g : KetUpToPhase d → ℝ≥0) (e : MEnsemble d ι) :
    (convex_roof g (Ensemble.mix e) : ℝ) ≤
      ∑ i, (e.distr i : ℝ) * (convex_roof g (e.states i) : ℝ) := by
  rw [← quantumRoof_eq_convex_roof]
  unfold quantumRoof
  rw [mixture_matrix]
  calc
    ConvexRoof.roof pureMatrix (fun ψ => (g (KetUpToPhase.mk ψ) : ℝ))
        (∑ i, (e.distr i : ℝ) • (e.states i).M) ≤
        ∑ i, (e.distr i : ℝ) * quantumRoof g (e.states i) :=
      ConvexRoof.roof_finite_jensen _ _
        (fun ψ => (g (KetUpToPhase.mk ψ)).coe_nonneg)
        Finset.univ (fun i => (e.distr i : ℝ)) (fun i => (e.states i).M)
        (fun i _ => (e.distr i).zero_le_coe) e.distr.normalized
        (fun i _ => density_mem_pureMatrix_domain (e.states i))
    _ = _ := by simp only [quantumRoof_eq_convex_roof]

section QuantumMixedClosure

variable {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂]
  [DecidableEq d₁] [DecidableEq d₂] [Nonempty d] [Nonempty d₁] [Nonempty d₂]

/--
The pure-to-mixed theorem for the actual imported quantum convex roofs. The
marginal maps must be restrictions of real linear matrix maps. No dimension
bound, rank condition, attainment hypothesis, or common pure-ensemble axes occur.
-/
theorem quantum_strong_superadditivity_of_pure
    (g : KetUpToPhase d → ℝ≥0)
    (g₁ : KetUpToPhase d₁ → ℝ≥0) (g₂ : KetUpToPhase d₂ → ℝ≥0)
    (marginal₁ : MState d → MState d₁) (marginal₂ : MState d → MState d₂)
    (linear₁ : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d₁ ℂ)
    (linear₂ : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d₂ ℂ)
    (hlinear₁ : ∀ ρ, (marginal₁ ρ).M = linear₁ ρ.M)
    (hlinear₂ : ∀ ρ, (marginal₂ ρ).M = linear₂ ρ.M)
    (hpure : ∀ ψ : Ket d,
      (convex_roof g₁ (marginal₁ (MState.pure ψ)) : ℝ) +
      (convex_roof g₂ (marginal₂ (MState.pure ψ)) : ℝ) ≤
      (g (KetUpToPhase.mk ψ) : ℝ)) (ρ : MState d) :
    (convex_roof g₁ (marginal₁ ρ) : ℝ) + (convex_roof g₂ (marginal₂ ρ) : ℝ) ≤
      (convex_roof g ρ : ℝ) := by
  have hmap₁ : MapsTo linear₁ (ConvexRoof.domain (pureMatrix (d := d)))
      (ConvexRoof.domain (pureMatrix (d := d₁))) := by
    intro M hM
    rw [pureMatrix_domain_eq] at hM ⊢
    obtain ⟨σ, rfl⟩ := hM
    exact ⟨marginal₁ σ, hlinear₁ σ⟩
  have hmap₂ : MapsTo linear₂ (ConvexRoof.domain (pureMatrix (d := d)))
      (ConvexRoof.domain (pureMatrix (d := d₂))) := by
    intro M hM
    rw [pureMatrix_domain_eq] at hM ⊢
    obtain ⟨σ, rfl⟩ := hM
    exact ⟨marginal₂ σ, hlinear₂ σ⟩
  have hp : ∀ ψ : Ket d,
      ConvexRoof.roof pureMatrix (fun φ => (g₁ (KetUpToPhase.mk φ) : ℝ))
        (linear₁ (pureMatrix ψ)) +
      ConvexRoof.roof pureMatrix (fun φ => (g₂ (KetUpToPhase.mk φ) : ℝ))
        (linear₂ (pureMatrix ψ)) ≤ (g (KetUpToPhase.mk ψ) : ℝ) := by
    intro ψ
    rw [pureMatrix, ← hlinear₁, ← hlinear₂]
    change quantumRoof g₁ (marginal₁ (MState.pure ψ)) +
      quantumRoof g₂ (marginal₂ (MState.pure ψ)) ≤ _
    rw [quantumRoof_eq_convex_roof, quantumRoof_eq_convex_roof]
    exact hpure ψ
  have h := ConvexRoof.strong_superadditivity_of_pure pureMatrix
    (fun ψ => (g (KetUpToPhase.mk ψ) : ℝ)) pureMatrix
    (fun φ => (g₁ (KetUpToPhase.mk φ) : ℝ)) pureMatrix
    (fun φ => (g₂ (KetUpToPhase.mk φ) : ℝ)) linear₁ linear₂
    (fun φ => (g₁ (KetUpToPhase.mk φ)).coe_nonneg)
    (fun φ => (g₂ (KetUpToPhase.mk φ)).coe_nonneg)
    hmap₁ hmap₂ hp (density_mem_pureMatrix_domain ρ)
  rw [← hlinear₁, ← hlinear₂] at h
  change quantumRoof g₁ (marginal₁ ρ) + quantumRoof g₂ (marginal₂ ρ) ≤
    quantumRoof g ρ at h
  simpa only [quantumRoof_eq_convex_roof] using h

end QuantumMixedClosure

end EC2
