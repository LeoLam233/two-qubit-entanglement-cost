import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Scalar spectral entropy infrastructure for EC2

All statements in this file are proved from Mathlib. The finite spectra may
contain zero entries; no rank or strict-positivity restriction is hidden in the
definitions. `entropy` is measured in nats and `entropyBits` in bits.
-/

noncomputable section

open scoped BigOperators Topology
open Finset Filter Set

namespace EC2.Entropy

def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def entropyBits {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  entropy p / Real.log 2

def mass {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, p i

def normalizedEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  entropy (fun i => p i / mass p)

def moment {ι : Type*} [Fintype ι] (p : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ i, (p i) ^ (q / 2)

/-- The logarithm of the Schatten norm expressed through squared singular values. -/
def logSpectralNorm {ι : Type*} [Fintype ι] (p : ι → ℝ) (q : ℝ) : ℝ :=
  Real.log (moment p q) / q

def wNats (c : ℝ) : ℝ :=
  Real.binEntropy ((1 + Real.sqrt (1 - c ^ 2)) / 2)

def wBits (c : ℝ) : ℝ := wNats c / Real.log 2

@[simp] theorem entropy_zero {ι : Type*} [Fintype ι] :
    entropy (fun _ : ι => 0) = 0 := by simp [entropy]

theorem entropy_eq_neg_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -(∑ i, p i * Real.log (p i)) := by
  simp [entropy, Real.negMulLog, ← Finset.sum_neg_distrib]

/-- Exact direct-sum/scaling entropy identity, valid also at zero mass. -/
theorem entropy_scale {ι : Type*} [Fintype ι] (a : ℝ) (p : ι → ℝ) :
    entropy (fun i => a * p i) =
      mass p * Real.negMulLog a + a * entropy p := by
  simp_rw [entropy, Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rfl

theorem entropy_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) :
    entropy (Sum.elim p q) = entropy p + entropy q := by
  simp [entropy, Fintype.sum_sum_type]

theorem entropy_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) :
    entropy (fun ij : ι × κ => p ij.1 * q ij.2) =
      mass q * entropy p + mass p * entropy q := by
  calc
    _ = ∑ i, (mass q * Real.negMulLog (p i) + p i * entropy q) := by
      simp [entropy, mass, Fintype.sum_prod_type, Real.negMulLog_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      simp [entropy, mass, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

theorem entropy_directSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (a b : ℝ)
    (hp : mass p = 1) (hq : mass q = 1) :
    entropy (Sum.elim (fun i => a * p i) (fun j => b * q j)) =
      Real.negMulLog a + Real.negMulLog b + a * entropy p + b * entropy q := by
  rw [entropy_sum, entropy_scale, entropy_scale, hp, hq]
  ring

theorem entropy_normalize {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : mass p ≠ 0) :
    entropy p = Real.negMulLog (mass p) + mass p * normalizedEntropy p := by
  have hsum : mass (fun i => p i / mass p) = 1 := by
    change (∑ i, p i / mass p) = 1
    rw [← Finset.sum_div]
    exact div_self hp
  have h := entropy_scale (mass p) (fun i => p i / mass p)
  simpa only [hsum, one_mul, mul_div_cancel₀ _ hp, normalizedEntropy] using h

/-- A nonnegative finite spectrum of mass zero vanishes entry by entry. -/
theorem eq_zero_of_nonneg_mass_zero {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hm : mass p = 0) : p = 0 := by
  funext i
  have hsum : ∑ j, p j = 0 := hm
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j)).mp hsum i (mem_univ i)
  simpa using this

theorem entropy_of_nonneg_mass_zero {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hm : mass p = 0) : entropy p = 0 := by
  rw [eq_zero_of_nonneg_mass_zero p hp hm]
  exact entropy_zero

theorem entropy_normalize_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    entropy p = Real.negMulLog (mass p) + mass p * normalizedEntropy p := by
  by_cases hm : mass p = 0
  · rw [entropy_of_nonneg_mass_zero p hp hm, hm]
    simp
  · exact entropy_normalize p hm

theorem negMulLog_half (x : ℝ) :
    2 * Real.negMulLog (x / 2) = Real.negMulLog x + x * Real.log 2 := by
  rw [div_eq_mul_inv, Real.negMulLog_mul]
  simp only [Real.negMulLog, Real.log_inv]
  ring

/-- The classical cancellation used by the balanced block entropy proof.
No positivity assumptions are needed for this algebraic identity, so both
`x = 0` and `y = 0` are included. -/
theorem balanced_classical_entropy (x y : ℝ) (hxy : x + y = 1) :
    2 * Real.negMulLog (x / 2) + 2 * Real.negMulLog (y / 2) =
      Real.binEntropy x + Real.log 2 := by
  rw [negMulLog_half, negMulLog_half,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hy : y = 1 - x := by linarith
  rw [hy]
  ring

/-- Equal direct-sum weights contribute one classical bit. -/
theorem entropy_equal_directSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (hp : mass p = 1) (hq : mass q = 1) :
    entropy (Sum.elim (fun i => p i / 2) (fun j => q j / 2)) =
      Real.log 2 + (entropy p + entropy q) / 2 := by
  have heq : (Sum.elim (fun i => p i / 2) (fun j => q j / 2)) =
      Sum.elim (fun i => (1 / 2 : ℝ) * p i) (fun j => (1 / 2 : ℝ) * q j) := by
    funext i
    cases i <;> simp [div_eq_mul_inv, mul_comm]
  rw [heq, entropy_directSum p q _ _ hp hq]
  have hhalf := negMulLog_half (1 : ℝ)
  simp only [Real.negMulLog_one, one_mul, zero_add] at hhalf
  linarith

@[simp] theorem wNats_zero : wNats 0 = 0 := by norm_num [wNats]
@[simp] theorem wNats_one : wNats 1 = Real.log 2 := by
  unfold wNats
  norm_num
  simpa only [one_div] using Real.binEntropy_two_inv
@[simp] theorem wBits_zero : wBits 0 = 0 := by simp [wBits]
@[simp] theorem wBits_one : wBits 1 = 1 := by
  simp [wBits, Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)]

theorem wNats_nonneg {c : ℝ} (hc : c ∈ Set.Icc 0 1) : 0 ≤ wNats c := by
  apply Real.binEntropy_nonneg
  · positivity
  · have hs : Real.sqrt (1 - c ^ 2) ≤ 1 := by
      apply Real.sqrt_le_one.mpr
      nlinarith [sq_nonneg c]
    linarith

theorem wNats_monotoneOn : MonotoneOn wNats (Set.Icc 0 1) := by
  intro a ha b hb hab
  have harg (c : ℝ) (hc : c ∈ Set.Icc 0 1) :
      (1 + Real.sqrt (1 - c ^ 2)) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor
    · have := Real.sqrt_nonneg (1 - c ^ 2)
      norm_num
      linarith
    · have hs : Real.sqrt (1 - c ^ 2) ≤ 1 := by
        apply Real.sqrt_le_one.mpr
        nlinarith [sq_nonneg c]
      linarith
  apply Real.binEntropy_strictAntiOn.antitoneOn (harg b hb) (harg a ha)
  have hs : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - a ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [ha.1, hb.1]
  linarith

theorem wBits_monotoneOn : MonotoneOn wBits (Set.Icc 0 1) := by
  intro a ha b hb hab
  exact div_le_div_of_nonneg_right (wNats_monotoneOn ha hb hab)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

/-- The exact logarithmic identity used in Eq. (9). The formula includes the
balanced point `r = s`: Real.log uses the same zero-weight convention. -/
theorem hanner_logarithmic_identity (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hn : r ^ 2 + s ^ 2 = 1) :
    (r + s) ^ 2 * Real.log (r + s) +
      (r - s) ^ 2 * Real.log |r - s| =
      Real.log 2 - wNats |r ^ 2 - s ^ 2| := by
  have hsqrt : Real.sqrt (1 - |r ^ 2 - s ^ 2| ^ 2) = 2 * r * s := by
    have hid : 1 - |r ^ 2 - s ^ 2| ^ 2 = (2 * r * s) ^ 2 := by
      rw [sq_abs]
      have hn2 := congrArg (fun z : ℝ => z ^ 2) hn
      nlinarith
    rw [hid, Real.sqrt_sq (by positivity)]
  have hw : wNats |r ^ 2 - s ^ 2| = Real.binEntropy ((r + s) ^ 2 / 2) := by
    unfold wNats
    rw [hsqrt]
    congr 1
    nlinarith
  have hcompl : 1 - (r + s) ^ 2 / 2 = (r - s) ^ 2 / 2 := by nlinarith
  have hsum : (r + s) ^ 2 + (r - s) ^ 2 = 2 := by nlinarith
  rw [hw, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hcompl]
  have hp := negMulLog_half ((r + s) ^ 2)
  have hm := negMulLog_half ((r - s) ^ 2)
  simp only [Real.negMulLog, Real.log_pow, Nat.cast_ofNat] at hp hm
  rw [Real.log_abs]
  simp only [Real.negMulLog]
  have hsumlog := congrArg (fun z : ℝ => z * Real.log 2) hsum
  linear_combination hp / 2 + hm / 2 + hsumlog / 2

@[simp] theorem moment_two {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    moment p 2 = mass p := by simp [moment, mass]

/-- Zero spectral values contribute identically zero in a neighborhood of `q = 2`. -/
theorem hasDerivAt_rpow_half (a : ℝ) (ha : 0 ≤ a) :
    HasDerivAt (fun q : ℝ => a ^ (q / 2)) (a * Real.log a / 2) 2 := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    simp only [zero_mul, zero_div]
    apply (hasDerivAt_const (2 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℝ) ≠ 0)] with q hq
    simp [Real.zero_rpow (div_ne_zero hq (by norm_num : (2 : ℝ) ≠ 0))]
  · convert HasDerivAt.const_rpow hpos ((hasDerivAt_id (2 : ℝ)).div_const 2) using 1 <;>
      norm_num [id_eq] <;> ring

theorem hasDerivAt_moment_two {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    HasDerivAt (moment p) (-entropy p / 2) 2 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_rpow_half (p i) (hp i))
  convert h using 1
  · rfl
  · rw [entropy_eq_neg_sum, neg_neg, Finset.sum_div]

/-- The spectral form of manuscript Eq. (8), including zero eigenvalues. -/
theorem hasDerivAt_logSpectralNorm_two {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hm : mass p ≠ 0) :
    HasDerivAt (logSpectralNorm p) (-normalizedEntropy p / 4) 2 := by
  have hlog := (hasDerivAt_moment_two p hp).log (by simpa using hm)
  have hdiv := hlog.div (hasDerivAt_id (2 : ℝ)) (by norm_num)
  convert hdiv using 1
  · rfl
  · rw [moment_two]
    have he := entropy_normalize p hm
    simp only [Real.negMulLog] at he
    dsimp only [id_eq]
    field_simp
    nlinarith [he]

/-- A one-sided inequality tangent at its endpoint orders its right derivatives. -/
theorem right_derivative_le_of_le {f g : ℝ → ℝ} {a f' g' : ℝ}
    (hf : HasDerivWithinAt f f' (Ioi a) a)
    (hg : HasDerivWithinAt g g' (Ioi a) a)
    (heq : f a = g a) (hle : ∀ x, a < x → f x ≤ g x) : f' ≤ g' := by
  have hft := (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi.mpr le_rfl)).mp hf
  have hgt := (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi.mpr le_rfl)).mp hg
  apply le_of_tendsto_of_tendsto hft hgt
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field, slope_def_field, heq]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hle x hx) _) (sub_pos.mpr hx).le

end EC2.Entropy
