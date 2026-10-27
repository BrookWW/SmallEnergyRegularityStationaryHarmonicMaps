module

public import HarmonicMaps.Analysis.RadiusBoundaryIdentityPolar
public import HarmonicMaps.Analysis.RadialStationarity
public import HarmonicMaps.Analysis.RadialCutoffProfile
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Polar stationarity for the explicit shrinking cutoff

Local minimality supplies the radial identity. Genuine Sobolev integrability
then permits the exact polar conversion of both derivative-weighted terms.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- The actual minimizer's radial stationarity, specialized to the explicit
cutoff and expressed in polar boundary densities for the same Du. -/
theorem IsLocallyEnergyMinimizing.cutoff_radial_stationarity_polar {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) (t δ : PositiveRadius)
    (hδR : t.val + δ.val < R) :
    let p := fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
        ∂(volume : Measure (Domain n)).toSphere
    let g := fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ‖‖(a + r • θ.val) - a‖⁻¹ • ∑ i : Fin n,
          ((a + r • θ.val) - a) i • Du (a + r • θ.val) i‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere
    ((n : ℝ) - 2) * (∫ x in Metric.ball a R, radialCutoffProfile t δ ‖x - a‖ * hsNormSq (Du x)) +
      (∫ r in Ioo (0 : ℝ) R, r * deriv (radialCutoffProfile t δ) r * p r) =
      2 * (∫ r in Ioo (0 : ℝ) R, r * deriv (radialCutoffProfile t δ) r * g r) := by
  dsimp only
  have hs := radialCutoffProfile_contDiff t δ
  have hc : Continuous (fun r : ℝ => r * deriv (radialCutoffProfile t δ) r) :=
    continuous_id.mul (hs.continuous_deriv (by norm_num))
  have he := hu.integrable_hsNormSq_ball hball
  have hg := hu.integrable_radial_columns_ball hball
  have ha := integrableOn_radial_mul he hs.continuous
  have hb := integrableOn_radial_mul he hc
  have hstat := (hmin.radial_stationarity hu hN hR hball hs
    (radialCutoffProfile_plateau t δ) hδR
    (fun _ hr => radialCutoffProfile_eq_zero t δ hr)).2.2
  have heq : (∫ x in Metric.ball a R,
      (((n : ℝ) - 2) * radialCutoffProfile t δ ‖x - a‖ +
        ‖x - a‖ * deriv (radialCutoffProfile t δ) ‖x - a‖) * hsNormSq (Du x)) =
      ((n : ℝ) - 2) * (∫ x in Metric.ball a R, radialCutoffProfile t δ ‖x - a‖ * hsNormSq (Du x)) +
        (∫ x in Metric.ball a R, (‖x - a‖ * deriv (radialCutoffProfile t δ) ‖x - a‖) * hsNormSq (Du x)) := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (ha.const_mul _) (by simpa only [IntegrableOn, mul_assoc] using hb), integral_const_mul]
  rw [heq] at hstat
  rw [integral_radial_mul_eq_polar hn he hc,
    integral_radial_mul_eq_polar hn hg hc] at hstat
  exact hstat

end HarmonicMaps
