module

public import HarmonicMaps.Analysis.InnerVariationEnergyMinimum
public import HarmonicMaps.Analysis.InnerVariationEnergyAlgebraBounds
public import HarmonicMaps.Analysis.InnerVariationStressIntegrability
public import HarmonicMaps.Analysis.DominatedEnergyDerivative
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Inner stationarity from local energy minimality

Genuine Sobolev competitors give a two-sided minimum of the substituted
energy. Uniform difference-quotient domination by the original HS density
permits differentiation under the integral. The derivative at the minimum
is zero, yielding the source stress identity for the same weak gradient.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

namespace HarmonicMaps

/-- Every locally energy-minimizing Sobolev map satisfies the actual inner
stationarity identity. No stationarity or variation conclusion is an input. -/
theorem IsLocallyEnergyMinimizing.innerVariation_stationarity {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {ζ : Domain n → Domain n} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Metric.ball a R) :
    IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) * (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j)
      (Metric.ball a R) ∧
    (∫ x in Metric.ball a R, hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) * (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j) = 0 := by
  let μ := volume.restrict (Metric.ball a R)
  let F : ℝ → Domain n → ℝ := fun t x => |(1 + t • fderiv ℝ ζ x).det| *
    hsNormSq (fun i => ∑ j : Fin n,
      (Ring.inverse (1 + t • fderiv ℝ ζ x) (EuclideanSpace.single i 1)) j • Du x j)
  let D : Domain n → ℝ := fun x => hsNormSq (Du x) *
    (∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i) -
    2 * ∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (Du x i) (Du x j) * (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j
  have hw := hu.memW12_ball hball
  refine ⟨hw.integrable_innerVariation_stress hζ, ?_⟩
  have hF0 : F 0 = fun x => hsNormSq (Du x) := by
    funext x
    have hz : (1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • fderiv ℝ ζ x = 1 := by
      ext v i
      simp
    have hA : (fun i => ∑ j : Fin n,
        (Ring.inverse (1 + (0 : ℝ) • fderiv ℝ ζ x) (EuclideanSpace.single i 1)) j • Du x j) = Du x := by
      funext i
      exact innerVariation_inverse_column_zero (fderiv ℝ ζ x) (Du x) i
    dsimp only [F]
    rw [hA, hz]
    simp [ContinuousLinearMap.det]
  obtain ⟨ε₀, hε₀, hcomp⟩ := hmin.innerVariation_transformed_energy_minimum hu hN hR hball hζ hc hs
  obtain ⟨L, hL, hDbound⟩ := innerVariation_exists_derivative_bound hζ hc
  obtain ⟨ε₁, hε₁, C, _hC, hquot⟩ := innerVariation_energy_density_difference_quotient_bound n L hL.le
  have hε : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < min ε₀ ε₁ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have hFn : ∀ᶠ t : ℝ in 𝓝[≠] 0, Integrable (F t) μ := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    exact (hcomp t (ht.trans_le (min_le_left _ _))).1
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂μ,
      ‖t⁻¹ * (F t x - F 0 x)‖ ≤ C * hsNormSq (Du x) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    apply Filter.Eventually.of_forall
    intro x
    have h := (hquot q (fderiv ℝ ζ x) (Du x) (hDbound x) t
      (ht.trans_le (min_le_right _ _)) ht0).2
    rw [hF0]
    change |t⁻¹ * (F t x - hsNormSq (Du x))| ≤ _
    rw [mul_comm t⁻¹, ← div_eq_mul_inv]
    exact h
  have hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (D x) 0 :=
    Filter.Eventually.of_forall fun x =>
      innerVariation_energy_density_hasDerivAt (fderiv ℝ ζ x) (Du x)
  have hzI : Integrable (F 0) μ := by rw [hF0]; exact hw.integrable_hsNormSq
  have hder := hasDerivAt_integral_of_dominated_slopes hzI hFn
    (hw.integrable_hsNormSq.const_mul C) hb hd
  have hlocal : IsLocalMin (fun t => ∫ x, F t x ∂μ) 0 := by
    filter_upwards [hnear] with t ht
    rw [hF0]
    exact (hcomp t (ht.trans_le (min_le_left _ _))).2
  exact hlocal.hasDerivAt_eq_zero hder

end HarmonicMaps
