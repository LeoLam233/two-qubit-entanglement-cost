import EC2.Quantum
import EC2.ConvexRoofQuantum

/-!
# Unitary transport of pure ensembles and convex roofs

All quantum states and ensembles here are the concrete Physlib objects.
This infrastructure is used for local basis changes in the EC2 proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate Matrix NNReal
open Ensemble

namespace EC2

section General
variable {d : Type} [Fintype d] [DecidableEq d]

theorem unitary_mulVec_norm_sq (U : Matrix.unitaryGroup d ℂ) (v : d → ℂ) :
    (∑ i, ‖U.val.mulVec v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  have hd : star (U.val.mulVec v) ⬝ᵥ U.val.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    have hU : U.val.conjTranspose * U.val = 1 := U.prop.1
    rw [hU, Matrix.vecMul_one]
  have he (w : d → ℂ) : (∑ i, ‖w i‖ ^ 2 : ℝ) =
      (star w ⬝ᵥ w).re := by
    simp [dotProduct, Complex.mul_re, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
  rw [he, he, hd]

/-- The ordinary unitary action on a normalized ket. -/
def unitaryKet (U : Matrix.unitaryGroup d ℂ) (ψ : Ket d) : Ket d where
  vec := U.val.mulVec ψ
  normalized' := (unitary_mulVec_norm_sq U ψ).trans ψ.normalized'

@[simp] theorem unitaryKet_apply (U : Matrix.unitaryGroup d ℂ) (ψ : Ket d) (i : d) :
    unitaryKet U ψ i = U.val.mulVec ψ i := rfl

@[simp] theorem unitaryKet_one (ψ : Ket d) : unitaryKet 1 ψ = ψ := by
  ext i
  change (1 : Matrix d d ℂ).mulVec ψ i = ψ i
  simp

theorem unitaryKet_comp (U V : Matrix.unitaryGroup d ℂ) (ψ : Ket d) :
    unitaryKet V (unitaryKet U ψ) = unitaryKet (V * U) ψ := by
  ext i
  change V.val.mulVec (U.val.mulVec ψ) i = (V.val * U.val).mulVec ψ i
  rw [Matrix.mulVec_mulVec]

/-- The ket action and density-matrix conjugation represent the same state. -/
theorem pure_unitaryKet (U : Matrix.unitaryGroup d ℂ) (ψ : Ket d) :
    MState.pure (unitaryKet U ψ) = (MState.pure ψ).uConj U := by
  apply MState.ext_m
  change Matrix.vecMulVec (U.val.mulVec ψ) (star (U.val.mulVec ψ)) =
    U.val * Matrix.vecMulVec (ψ : d → ℂ) (star (ψ : d → ℂ)) * U.val.conjTranspose
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

@[simp] theorem uConj_one (ρ : MState d) : ρ.uConj 1 = ρ := by
  apply MState.M_Injective
  change ρ.M.conj 1 = ρ.M
  exact HermitianMat.conj_one _

theorem uConj_comp (ρ : MState d) (U V : Matrix.unitaryGroup d ℂ) :
    (ρ.uConj U).uConj V = ρ.uConj (V * U) := by
  apply MState.M_Injective
  change (ρ.M.conj U.val).conj V.val = ρ.M.conj (V.val * U.val)
  exact HermitianMat.conj_conj _ _ _

@[simp] theorem entropyBits_uConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    entropyBits (ρ.uConj U) = entropyBits ρ := by
  simp [entropyBits, Sᵥₙ, MState.uConj_spectrum_eq]

theorem uConj_mix {ι : Type} [Fintype ι] (e : MEnsemble d ι)
    (U : Matrix.unitaryGroup d ℂ) :
    (Ensemble.mix e).uConj U = Ensemble.mix ((fun ρ => ρ.uConj U) <$> e) := by
  apply MState.M_Injective
  change (HermitianMat.conjLinear ℝ U.val) (∑ i, (e.distr i : ℝ) • (e.states i).M) =
    ∑ i, (e.distr i : ℝ) • ((e.states i).M.conj U.val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

theorem unitaryEnsemble_mix {ι : Type} [Fintype ι] (e : PEnsemble d ι)
    (U : Matrix.unitaryGroup d ℂ) :
    Ensemble.mix (toMEnsemble (unitaryKet U <$> e)) =
      (Ensemble.mix (toMEnsemble e)).uConj U := by
  rw [uConj_mix]
  congr 1
  simp only [toMEnsemble, Functor.map_map, pure_unitaryKet]

variable [Nonempty d]

theorem convex_roof_unitary_le (g : KetUpToPhase d → ℝ≥0)
    (U : Matrix.unitaryGroup d ℂ)
    (hcost : ∀ ψ : Ket d, g (KetUpToPhase.mk (unitaryKet U ψ)) = g (KetUpToPhase.mk ψ))
    (ρ : MState d) : convex_roof g (ρ.uConj U) ≤ convex_roof g ρ := by
  apply le_convex_roof g ρ
  intro n hn e hmix
  have hu := convex_roof_le_any_ensemble g (unitaryKet U <$> e)
  rw [unitaryEnsemble_mix, hmix] at hu
  have hc : pure_average_NNReal (g ∘ KetUpToPhase.mk) (unitaryKet U <$> e) =
      pure_average_NNReal (g ∘ KetUpToPhase.mk) e := by
    apply NNReal.eq
    change (∑ i, (e.distr i : ℝ) * (g (KetUpToPhase.mk (unitaryKet U (e.states i))) : ℝ)) =
      ∑ i, (e.distr i : ℝ) * (g (KetUpToPhase.mk (e.states i)) : ℝ)
    simp_rw [hcost]
  rwa [hc] at hu

/-- A phase-invariant pure cost that is unchanged by a unitary has an
unchanged convex roof, for all mixed states and all ranks. -/
theorem convex_roof_unitary_invariant (g : KetUpToPhase d → ℝ≥0)
    (U : Matrix.unitaryGroup d ℂ)
    (hcost : ∀ ψ : Ket d, g (KetUpToPhase.mk (unitaryKet U ψ)) = g (KetUpToPhase.mk ψ))
    (ρ : MState d) : convex_roof g (ρ.uConj U) = convex_roof g ρ := by
  apply le_antisymm (convex_roof_unitary_le g U hcost ρ)
  have hi : ∀ ψ : Ket d,
      g (KetUpToPhase.mk (unitaryKet U⁻¹ ψ)) = g (KetUpToPhase.mk ψ) := by
    intro ψ
    have h := hcost (unitaryKet U⁻¹ ψ)
    simpa only [unitaryKet_comp, mul_inv_cancel, unitaryKet_one] using h.symm
  have hr := convex_roof_unitary_le g U⁻¹ hi (ρ.uConj U)
  simpa only [uConj_comp, inv_mul_cancel, uConj_one] using hr

end General

/-- A local unitary with the `a:b` bipartition explicit. -/
def localConj {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : MState (a × b)) (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    MState (a × b) := ρ.uConj (U ⊗ᵤ V)

end EC2
