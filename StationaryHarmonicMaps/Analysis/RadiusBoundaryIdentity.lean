module

public import StationaryHarmonicMaps.Analysis.RadiusBoundaryIdentityCutoff
public import HarmonicMaps.Analysis.RadialCutoffIntegral
public import HarmonicMaps.Analysis.RadialCutoffWeightedIntegral
public import HarmonicMaps.Analysis.BallEnergyAbsoluteContinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The radius boundary identity from domain stationarity -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators Topology

namespace StationaryHarmonicMaps

theorem IsDomainStationary.radius_boundary_identity {n q : ℕ}
    (hn : 2 ≤ n) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hstationary : IsDomainStationary Ω Du) (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    let e := fun r : ℝ => ∫ x in Metric.ball a r, hsNormSq (Du x)
    let p := fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
        ∂(volume : Measure (Domain n)).toSphere
    let g := fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ‖‖(a + r • θ.val) - a‖⁻¹ • ∑ i : Fin n,
          ((a + r • θ.val) - a) i • Du (a + r • θ.val) i‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere
    AbsolutelyContinuousOnInterval e 0 R ∧
      ∀ᵐ t : ℝ, t ∈ Ioo 0 R →
        HasDerivAt e (p t) t ∧ ((n : ℝ) - 2) * e t - t * p t = -2 * t * g t := by
  let e := fun r : ℝ => ∫ x in Metric.ball a r, hsNormSq (Du x)
  let p := fun r : ℝ => r ^ (n - 1) *
    ∫ θ : Metric.sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
      ∂(volume : Measure (Domain n)).toSphere
  let g := fun r : ℝ => r ^ (n - 1) *
    ∫ θ : Metric.sphere (0 : Domain n) 1,
      ‖‖(a + r • θ.val) - a‖⁻¹ • ∑ i : Fin n,
        ((a + r • θ.val) - a) i • Du (a + r • θ.val) i‖ ^ 2
      ∂(volume : Measure (Domain n)).toSphere
  change AbsolutelyContinuousOnInterval e 0 R ∧
    ∀ᵐ t : ℝ, t ∈ Ioo 0 R →
      HasDerivAt e (p t) t ∧ ((n : ℝ) - 2) * e t - t * p t = -2 * t * g t
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have he := hu.integrable_hsNormSq_ball hball
  have hpolar := hu.integrable_polar_energy_densities hn0 hball
  have hp : IntegrableOn p (Ioo 0 R) volume := hpolar.1
  have hg : IntegrableOn g (Ioo 0 R) volume := hpolar.2
  refine ⟨absolutelyContinuousOnInterval_integral_ball hn0 hR.le he, ?_⟩
  filter_upwards [ae_hasDerivAt_integral_ball hn0 hR.le he,
    ae_tendsto_integral_radius_mul_radialCutoff_derivative hp,
    ae_tendsto_integral_radius_mul_radialCutoff_derivative hg] with t hder hpLimit hgLimit
  intro htR
  refine ⟨hder htR, ?_⟩
  let δ : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  have hδ : Tendsto (fun k => (δ k).val) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδright : Tendsto (fun k => (δ k).val) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, Filter.Eventually.of_forall fun k => (δ k).property⟩
  have heLimit : Tendsto (fun k => ∫ x in Metric.ball a R,
      radialCutoffProfile ⟨t, htR.1⟩ (δ k) ‖x - a‖ * hsNormSq (Du x))
      atTop (𝓝 (e t)) :=
    (tendsto_integral_radialCutoff hn0 ⟨t, htR.1⟩ htR.2 he).comp hδright
  have hleft := (heLimit.const_mul ((n : ℝ) - 2)).add (hpLimit htR δ hδ)
  have hright := (hgLimit htR δ hδ).const_mul 2
  have hsmall : ∀ᶠ k : ℕ in atTop, (δ k).val < R - t :=
    hδ (Iio_mem_nhds (sub_pos.mpr htR.2))
  have heq : (fun k => ((n : ℝ) - 2) * (∫ x in Metric.ball a R,
      radialCutoffProfile ⟨t, htR.1⟩ (δ k) ‖x - a‖ * hsNormSq (Du x)) +
      (∫ r in Ioo (0 : ℝ) R, r * deriv (radialCutoffProfile ⟨t, htR.1⟩ (δ k)) r * p r)) =ᶠ[atTop]
      (fun k => 2 * (∫ r in Ioo (0 : ℝ) R,
        r * deriv (radialCutoffProfile ⟨t, htR.1⟩ (δ k)) r * g r)) := by
    filter_upwards [hsmall] with k hk
    exact hstationary.cutoff_radial_stationarity_polar hn0 hu hball ⟨t, htR.1⟩ (δ k)
      (by dsimp only; linarith only [hk])
  have hlim := tendsto_nhds_unique_of_eventuallyEq hleft hright heq
  linarith only [hlim]

end StationaryHarmonicMaps
