import EC2.ConvexRoofClosure
import EC2.QuantumProductEntropy

/-!
# Product ensembles and the standard subadditivity bound

The product-state formation bound is proved from finite product ensembles and
arbitrarily accurate decompositions. No optimal decomposition is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Ensemble MState
open scoped BigOperators ComplexConjugate

namespace EC2

section Product
variable {a b : Type} [Fintype a] [Fintype b]
variable [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]

/-- Tensor product of two bipartite pure states, with the `AA':BB'` bipartition. -/
def partnerKet (ψ : Ket (Q × Q)) (φ : Ket (a × b)) : Ket ((Q × a) × (Q × b)) :=
  (ψ.prod φ).relabel (regroup a b).symm

/-- The product ket induces the exact density-matrix tensor product. -/
theorem pure_partnerKet (ψ : Ket (Q × Q)) (φ : Ket (a × b)) :
    MState.pure (partnerKet ψ φ) = partnerProduct (MState.pure ψ) (MState.pure φ) := by
  rw [partnerKet, ← MState.relabel_pure, MState.pure_prod_pure]
  rfl

/-- Tracing out `BB'` from a product partner state gives the product of the two left marginals. -/
theorem partnerProduct_traceRight (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    (partnerProduct ρ σ).traceRight = ρ.traceRight.prod σ.traceRight := by
  apply MState.ext_m
  ext x y
  change (∑ z : Q × b, ρ.m (x.1, z.1) (y.1, z.1) *
      σ.m (x.2, z.2) (y.2, z.2)) =
    (∑ q : Q, ρ.m (x.1, q) (y.1, q)) * (∑ j : b, σ.m (x.2, j) (y.2, j))
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Pure entanglement in a product ensemble is additive. -/
theorem partnerKet_entropy (ψ : Ket (Q × Q)) (φ : Ket (a × b)) :
    entropyBits (MState.pure (partnerKet ψ φ)).traceRight =
      entropyBits (MState.pure ψ).traceRight + entropyBits (MState.pure φ).traceRight := by
  rw [pure_partnerKet, partnerProduct_traceRight, entropyBits_prod]

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The finite independent product of two pure-state ensembles. -/
def partnerEnsemble (e : PEnsemble (Q × Q) ι) (f : PEnsemble (a × b) κ) :
    PEnsemble ((Q × a) × (Q × b)) (ι × κ) :=
  ⟨fun i => partnerKet (e.states i.1) (f.states i.2), e.distr.prod f.distr⟩

/-- Product ensemble probabilities factor exactly, including zero weights. -/
theorem partnerEnsemble_weight (e : PEnsemble (Q × Q) ι) (f : PEnsemble (a × b) κ)
    (i : ι) (j : κ) :
    ((partnerEnsemble e f).distr (i, j) : ℝ) = (e.distr i : ℝ) * (f.distr j : ℝ) := rfl

/-- Mixing the independent pure-state ensembles gives the density-matrix product. -/
theorem partnerEnsemble_mix (e : PEnsemble (Q × Q) ι) (f : PEnsemble (a × b) κ) :
    Ensemble.mix (toMEnsemble (partnerEnsemble e f)) =
      partnerProduct (Ensemble.mix (toMEnsemble e)) (Ensemble.mix (toMEnsemble f)) := by
  apply MState.ext_m
  ext x y
  rw [Ensemble.mix_of]
  simp only [Matrix.sum_apply, Matrix.smul_apply, toMEnsemble_mk]
  change (∑ ij : ι × κ, (((e.distr ij.1 : ℝ) * (f.distr ij.2 : ℝ)) : ℝ) •
      (MState.pure (partnerKet (e.states ij.1) (f.states ij.2))).m x y) = _
  simp only [pure_partnerKet]
  change (∑ ij : ι × κ, (((e.distr ij.1 : ℝ) * (f.distr ij.2 : ℝ)) : ℝ) •
      ((MState.pure (e.states ij.1)).m (x.1.1, x.2.1) (y.1.1, y.2.1) *
       (MState.pure (f.states ij.2)).m (x.1.2, x.2.2) (y.1.2, y.2.2))) =
    (Ensemble.mix (toMEnsemble e)).m (x.1.1, x.2.1) (y.1.1, y.2.1) *
    (Ensemble.mix (toMEnsemble f)).m (x.1.2, x.2.2) (y.1.2, y.2.2)
  rw [Ensemble.mix_of, Ensemble.mix_of]
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let z : ℂ := (MState.pure (e.states j)).m (x.1.1, x.2.1) (y.1.1, y.2.1)
  let w : ℂ := (MState.pure (f.states i)).m (x.1.2, x.2.2) (y.1.2, y.2.2)
  change ((e.distr j : ℝ) * (f.distr i : ℝ)) • (z * w) =
    ((e.distr j : ℝ) • z) * ((f.distr i : ℝ) • w)
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The product ensemble average is the sum of the two original pure averages. -/
theorem partnerEnsemble_average (e : PEnsemble (Q × Q) ι) (f : PEnsemble (a × b) κ) :
    (∑ ij, ((partnerEnsemble e f).distr ij : ℝ) *
      entropyBits (MState.pure ((partnerEnsemble e f).states ij)).traceRight) =
    (∑ i, (e.distr i : ℝ) * entropyBits (MState.pure (e.states i)).traceRight) +
    (∑ j, (f.distr j : ℝ) * entropyBits (MState.pure (f.states j)).traceRight) := by
  change (∑ ij : ι × κ, ((e.distr ij.1 : ℝ) * (f.distr ij.2 : ℝ)) *
    entropyBits (MState.pure (partnerKet (e.states ij.1) (f.states ij.2))).traceRight) = _
  simp only [partnerKet_entropy, Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
  have hleft : ∀ i, (∑ j, ((e.distr i : ℝ) * (f.distr j : ℝ)) *
      entropyBits (MState.pure (e.states i)).traceRight) =
      (e.distr i : ℝ) * entropyBits (MState.pure (e.states i)).traceRight := by
    intro i
    simp_rw [mul_right_comm (e.distr i : ℝ) _
      (entropyBits (MState.pure (e.states i)).traceRight)]
    rw [← Finset.mul_sum, f.distr.normalized, mul_one]
  have hright : (∑ i, ∑ j, ((e.distr i : ℝ) * (f.distr j : ℝ)) *
      entropyBits (MState.pure (f.states j)).traceRight) =
      ∑ j, (f.distr j : ℝ) * entropyBits (MState.pure (f.states j)).traceRight := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, e.distr.normalized, one_mul]
  simp only [hleft, hright]

/-- Product ensembles prove the actual two-qubit/arbitrary-partner formation subadditivity. -/
theorem formationBits_partner_subadditivity (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    formationBits (partnerProduct ρ σ) ≤ formationBits ρ + formationBits σ := by
  by_contra hbad
  have hgap : 0 < formationBits (partnerProduct ρ σ) - (formationBits ρ + formationBits σ) :=
    sub_pos.mpr (lt_of_not_ge hbad)
  let ε := (formationBits (partnerProduct ρ σ) - (formationBits ρ + formationBits σ)) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨n, hn, e, he, hecost⟩ := exists_pure_ensemble_formationBits_lt ρ hε
  obtain ⟨m, hm, f, hf, hfcost⟩ := exists_pure_ensemble_formationBits_lt σ hε
  have h := formationBits_le_pure_average (partnerEnsemble e f)
  rw [partnerEnsemble_mix, he, hf, partnerEnsemble_average] at h
  dsimp [ε] at hecost hfcost
  linarith

/-- EC2 strong superadditivity implies arbitrary-partner additivity; subadditivity is proved. -/
theorem formationBits_partner_additivity_of_strong
    (hstrong : ∀ Ω : MState ((Q × a) × (Q × b)),
      formationBits (marginalAB Ω) + formationBits (marginalAux Ω) ≤ formationBits Ω)
    (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    formationBits (partnerProduct ρ σ) = formationBits ρ + formationBits σ :=
  le_antisymm (formationBits_partner_subadditivity ρ σ)
    (formationBits_partner_lower_bound hstrong ρ σ)

end Product
end EC2
