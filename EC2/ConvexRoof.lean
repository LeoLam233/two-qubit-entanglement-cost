import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite convex roofs and dimension-independent mixed-state closure

The graph-hull representation is exactly the infimum over finite ensembles;
`mem_values_iff` proves this identification. No optimal ensemble is assumed.
The final lifting theorem is conditional on the pure-state inequality, and does
not claim to prove the EC2 entropy or concurrence lemmas.
-/

noncomputable section

open Set Finset
open scoped BigOperators

namespace EC2.ConvexRoof

variable {P V : Type*} [AddCommGroup V] [Module ℝ V]

/-- All states admitting a finite convex decomposition into the specified pure states. -/
def domain (pure : P → V) : Set V := convexHull ℝ (range pure)

/-- The finite ensemble graph, retaining both the barycenter and its average cost. -/
def graphHull (pure : P → V) (cost : P → ℝ) : Set (V × ℝ) :=
  convexHull ℝ (range (fun p => (pure p, cost p)))

/-- All finite-ensemble average costs at the fixed barycenter `x`. -/
def values (pure : P → V) (cost : P → ℝ) (x : V) : Set ℝ :=
  {c | (x, c) ∈ graphHull pure cost}

/-- The actual finite convex roof: the infimum of all ensemble costs. -/
def roof (pure : P → V) (cost : P → ℝ) (x : V) : ℝ :=
  sInf (values pure cost x)

/-- The graph-hull cost fiber is precisely the usual finite-ensemble cost set. -/
theorem mem_values_iff (pure : P → V) (cost : P → ℝ) (x : V) (c : ℝ) :
    c ∈ values pure cost x ↔
      ∃ (s : Finset P) (w : P → ℝ),
        (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p = 1) ∧
        (∑ p ∈ s, w p • pure p = x) ∧
        (∑ p ∈ s, w p * cost p = c) := by
  classical
  unfold values graphHull
  rw [convexHull_range_eq_exists_affineCombination]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨s, w, hw, hsum, heq⟩
    rw [affineCombination_eq_centerMass hsum,
      Finset.centerMass_eq_of_sum_1 _ _ hsum] at heq
    refine ⟨s, w, hw, hsum, ?_, ?_⟩
    · simpa only [Prod.fst_sum, Prod.smul_fst] using congrArg Prod.fst heq
    · simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd heq
  · rintro ⟨s, w, hw, hsum, hx, hc⟩
    refine ⟨s, w, hw, hsum, ?_⟩
    rw [affineCombination_eq_centerMass hsum,
      Finset.centerMass_eq_of_sum_1 _ _ hsum]
    apply Prod.ext
    · simpa only [Prod.fst_sum, Prod.smul_fst] using hx
    · simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using hc

/-- A supplied finite ensemble is a valid point in the cost fiber. -/
theorem sum_mem_values (pure : P → V) (cost : P → ℝ)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (p : ι → P)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * cost (p i)) ∈
      values pure cost (∑ i ∈ s, w i • pure (p i)) := by
  have h := (convex_convexHull ℝ (range (fun p => (pure p, cost p)))).sum_mem
    hw hsum (fun i _ => subset_convexHull ℝ _ (mem_range_self (p i)))
  change (_, _) ∈ graphHull pure cost
  have heq : (∑ i ∈ s, w i • (pure (p i), cost (p i))) =
      (∑ i ∈ s, w i • pure (p i), ∑ i ∈ s, w i * cost (p i)) := by
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← heq]
  exact h

/-- A state is in the finite-mixture domain exactly when its cost fiber is nonempty. -/
theorem values_nonempty_iff (pure : P → V) (cost : P → ℝ) (x : V) :
    (values pure cost x).Nonempty ↔ x ∈ domain pure := by
  have himage : (LinearMap.fst ℝ V ℝ) '' graphHull pure cost = domain pure := by
    unfold graphHull domain
    rw [LinearMap.image_convexHull]
    congr 1
    ext x
    simp
  rw [← himage]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(x, c), hc, rfl⟩
  · rintro ⟨⟨y, c⟩, h, heq⟩
    change y = x at heq
    subst y
    exact ⟨c, h⟩

/-- Every ensemble average of a nonnegative pure-state cost is nonnegative. -/
theorem values_nonneg (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) {x : V} {c : ℝ}
    (hc : c ∈ values pure cost x) : 0 ≤ c := by
  obtain ⟨s, w, hw, _, _, rfl⟩ := (mem_values_iff pure cost x c).mp hc
  exact Finset.sum_nonneg (fun p hp => mul_nonneg (hw p hp) (hcost p))

/-- The cost set has a uniform lower bound, including empty fibers. -/
theorem values_bddBelow (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) (x : V) : BddBelow (values pure cost x) :=
  ⟨0, fun _ hc => values_nonneg pure cost hcost hc⟩

/-- Every actual finite ensemble gives an upper bound for the infimum. -/
theorem roof_le_of_mem (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) {x : V} {c : ℝ}
    (hc : c ∈ values pure cost x) : roof pure cost x ≤ c :=
  csInf_le (values_bddBelow pure cost hcost x) hc

/-- A nonempty finite convex roof is nonnegative. -/
theorem roof_nonneg (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) {x : V} (hx : x ∈ domain pure) :
    0 ≤ roof pure cost x :=
  le_csInf ((values_nonempty_iff pure cost x).mpr hx)
    (fun _ hc => values_nonneg pure cost hcost hc)

/-- Approximate optimal ensembles exist for every positive tolerance. -/
theorem exists_cost_lt (pure : P → V) (cost : P → ℝ)
    {x : V} (hx : x ∈ domain pure) {ε : ℝ} (hε : 0 < ε) :
    ∃ c ∈ values pure cost x, c < roof pure cost x + ε := by
  exact exists_lt_of_csInf_lt ((values_nonempty_iff pure cost x).mpr hx)
    (lt_add_of_pos_right _ hε)

/-- Convexity follows from mixing arbitrarily accurate finite ensembles. -/
theorem convexOn_roof (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) : ConvexOn ℝ (domain pure) (roof pure cost) := by
  refine ⟨convex_convexHull ℝ _, ?_⟩
  intro x hx y hy a b ha hb hab
  change roof pure cost (a • x + b • y) ≤ a * roof pure cost x + b * roof pure cost y
  by_contra hbad
  have hgap : 0 < roof pure cost (a • x + b • y) -
      (a * roof pure cost x + b * roof pure cost y) := sub_pos.mpr (lt_of_not_ge hbad)
  let ε := (roof pure cost (a • x + b • y) -
      (a * roof pure cost x + b * roof pure cost y)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨cx, hcx, hxlt⟩ := exists_cost_lt pure cost hx hε
  obtain ⟨cy, hcy, hylt⟩ := exists_cost_lt pure cost hy hε
  have hmix : a * cx + b * cy ∈ values pure cost (a • x + b • y) := by
    exact (convex_convexHull ℝ _ hcx hcy ha hb hab)
  have hupper := roof_le_of_mem pure cost hcost hmix
  have hax := mul_le_mul_of_nonneg_left (le_of_lt hxlt) ha
  have hby := mul_le_mul_of_nonneg_left (le_of_lt hylt) hb
  have hεsum : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  have hbound : roof pure cost (a • x + b • y) ≤
      a * roof pure cost x + b * roof pure cost y + ε := by
    nlinarith [hupper, hax, hby, hεsum]
  dsimp [ε] at hbound
  linarith

/-- Any convex function bounded by the pure costs is bounded by their finite convex roof. -/
theorem convex_lower_bound (pure : P → V) (cost : P → ℝ) (f : V → ℝ)
    (hf : ConvexOn ℝ (domain pure) f)
    (hpure : ∀ p, f (pure p) ≤ cost p) {x : V} (hx : x ∈ domain pure) :
    f x ≤ roof pure cost x := by
  apply le_csInf ((values_nonempty_iff pure cost x).mpr hx)
  intro c hc
  obtain ⟨s, w, hw, hsum, hstate, hcost⟩ := (mem_values_iff pure cost x c).mp hc
  calc
    f x = f (∑ p ∈ s, w p • pure p) := congrArg f hstate.symm
    _ ≤ ∑ p ∈ s, w p * f (pure p) :=
      hf.map_sum_le hw hsum (fun p _ => subset_convexHull ℝ _ (mem_range_self p))
    _ ≤ ∑ p ∈ s, w p * cost p :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hpure p) (hw p hp))
    _ = c := hcost

/-- Every finite mixed ensemble obeys Jensen's inequality for the defined convex roof. -/
theorem roof_finite_jensen (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (x : ι → V) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, x i ∈ domain pure) :
    roof pure cost (∑ i ∈ s, w i • x i) ≤
      ∑ i ∈ s, w i * roof pure cost (x i) :=
  (convexOn_roof pure cost hcost).map_sum_le hw hsum hx

/-- The one-element ensemble bounds the roof at a pure state. -/
theorem roof_le_pure (pure : P → V) (cost : P → ℝ)
    (hcost : ∀ p, 0 ≤ cost p) (p : P) : roof pure cost (pure p) ≤ cost p := by
  apply roof_le_of_mem pure cost hcost
  exact subset_convexHull ℝ _ (mem_range_self p)

section MixedClosure

variable {P₁ P₂ V₁ V₂ : Type*}
variable [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]

/--
Pure-state superadditivity lifts to every finite mixed state, in arbitrary real
state spaces and hence with unrestricted finite auxiliary dimensions. The only
substantive hypothesis is the explicitly displayed pure-state inequality.
-/
theorem strong_superadditivity_of_pure
    (pure : P → V) (cost : P → ℝ)
    (pure₁ : P₁ → V₁) (cost₁ : P₁ → ℝ)
    (pure₂ : P₂ → V₂) (cost₂ : P₂ → ℝ)
    (marginal₁ : V →ₗ[ℝ] V₁) (marginal₂ : V →ₗ[ℝ] V₂)
    (hnonneg₁ : ∀ p, 0 ≤ cost₁ p) (hnonneg₂ : ∀ p, 0 ≤ cost₂ p)
    (hmap₁ : MapsTo marginal₁ (domain pure) (domain pure₁))
    (hmap₂ : MapsTo marginal₂ (domain pure) (domain pure₂))
    (hpure : ∀ p, roof pure₁ cost₁ (marginal₁ (pure p)) +
      roof pure₂ cost₂ (marginal₂ (pure p)) ≤ cost p)
    {x : V} (hx : x ∈ domain pure) :
    roof pure₁ cost₁ (marginal₁ x) + roof pure₂ cost₂ (marginal₂ x) ≤
      roof pure cost x := by
  apply convex_lower_bound pure cost
    (fun x => roof pure₁ cost₁ (marginal₁ x) + roof pure₂ cost₂ (marginal₂ x))
    _ hpure hx
  have h₁ : ConvexOn ℝ (domain pure) (roof pure₁ cost₁ ∘ marginal₁) :=
    ((convexOn_roof pure₁ cost₁ hnonneg₁).comp_linearMap marginal₁).subset
      hmap₁ (convex_convexHull ℝ _)
  have h₂ : ConvexOn ℝ (domain pure) (roof pure₂ cost₂ ∘ marginal₂) :=
    ((convexOn_roof pure₂ cost₂ hnonneg₂).comp_linearMap marginal₂).subset
      hmap₂ (convex_convexHull ℝ _)
  exact h₁.add h₂

end MixedClosure

end EC2.ConvexRoof
