import EC2.EntropyHanner

/-!
# Spectral Hanner-to-entropy reduction

The only inequality input to `entropy_le_from_hanner` is the Schatten Hanner
inequality expressed in terms of finite nonnegative squared singular-value
lists. The entropy differentiation, coincident-norm case and zero spectra are
proved here. A separate matrix theorem must identify the spectra of the
diagonal and off-diagonal block parts with the four block spectra.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace EC2.Entropy

def spectralNorm {ι : Type*} [Fintype ι] (p : ι → ℝ) (q : ℝ) : ℝ :=
  moment p q ^ (1 / q)

theorem mass_nonneg {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) : 0 ≤ mass p :=
  Finset.sum_nonneg (fun i _ => hp i)

@[simp] theorem spectralNorm_two {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    spectralNorm p 2 = Real.sqrt (mass p) := by
  simp [spectralNorm, Real.sqrt_eq_rpow]

theorem spectralNorm_two_sq {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) : (spectralNorm p 2) ^ 2 = mass p := by
  rw [spectralNorm_two, Real.sq_sqrt (mass_nonneg hp)]

/-- The norm derivative formula includes zero matrices/spectra. -/
theorem hasDerivAt_spectralNorm_two {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    HasDerivAt (spectralNorm p)
      (-spectralNorm p 2 * normalizedEntropy p / 4) 2 := by
  rcases eq_or_lt_of_le (mass_nonneg hp) with hz | hm
  · have hp0 := eq_zero_of_nonneg_mass_zero p hp hz.symm
    subst p
    have hderiv : HasDerivAt (spectralNorm (0 : ι → ℝ)) 0 2 := by
      apply (hasDerivAt_const (2 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℝ) ≠ 0)] with q hq
      have hhalf : q / 2 ≠ 0 := div_ne_zero hq (by norm_num)
      have hinv : q⁻¹ ≠ 0 := inv_ne_zero hq
      simp [spectralNorm, moment, Real.zero_rpow hhalf, Real.zero_rpow hinv]
    simpa [normalizedEntropy, entropy, mass] using hderiv
  · have hd := (hasDerivAt_logSpectralNorm_two p hp hm.ne').exp
    have hval : Real.exp (logSpectralNorm p 2) = spectralNorm p 2 := by
      rw [spectralNorm_two]
      change Real.exp (Real.log (moment p 2) / 2) = Real.sqrt (mass p)
      rw [moment_two, ← Real.log_sqrt hm.le, Real.exp_log (Real.sqrt_pos.mpr hm)]
    have hpos : ∀ᶠ q in 𝓝 (2 : ℝ), 0 < moment p q :=
      (hasDerivAt_moment_two p hp).continuousAt.eventually
        (lt_mem_nhds (by simpa using hm))
    have heq : spectralNorm p =ᶠ[𝓝 (2 : ℝ)] fun q => Real.exp (logSpectralNorm p q) := by
      filter_upwards [hpos] with q hq
      rw [spectralNorm, Real.rpow_def_of_pos hq, logSpectralNorm]
      congr 1
      ring
    convert hd.congr_of_eventuallyEq heq using 1
    rw [hval]
    ring

/-- Manuscript Eq. (10), with Hanner as the sole inequality input.
No derivative, continuity, zero-block or coincident-norm obligation is assumed. -/
theorem entropy_le_from_hanner {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (p : ι → ℝ) (u : κ → ℝ) (v : τ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hpn : mass p = 1) (huvn : mass u + mass v = 1)
    (hHanner : ∀ q : ℝ, 2 < q →
      2 * moment p q ≤
        (spectralNorm u q + spectralNorm v q) ^ q +
          |spectralNorm u q - spectralNorm v q| ^ q) :
    wNats |mass u - mass v| +
      mass u * normalizedEntropy u + mass v * normalizedEntropy v - Real.log 2 ≤
      entropy p := by
  have hleft : HasDerivWithinAt (fun q => 2 * moment p q) (-entropy p) (Ioi 2) 2 := by
    convert ((hasDerivAt_moment_two p hp).const_mul 2).hasDerivWithinAt (s := Ioi 2) using 1
    ring
  have hright := hasDerivWithinAt_hanner_entropy_rhs
    (hasDerivAt_spectralNorm_two u hu) (hasDerivAt_spectralNorm_two v hv)
    (by rw [spectralNorm_two]; positivity)
    (by rw [spectralNorm_two]; positivity)
    (spectralNorm_two_sq hu) (spectralNorm_two_sq hv) huvn
  have heq : 2 * moment p 2 =
      (spectralNorm u 2 + spectralNorm v 2) ^ (2 : ℝ) +
        |spectralNorm u 2 - spectralNorm v 2| ^ (2 : ℝ) := by
    rw [moment_two, hpn]
    simp only [Real.rpow_two, sq_abs]
    have hu2 := spectralNorm_two_sq hu
    have hv2 := spectralNorm_two_sq hv
    nlinarith
  have hd := right_derivative_le_of_le hleft hright heq hHanner
  linarith

end EC2.Entropy
