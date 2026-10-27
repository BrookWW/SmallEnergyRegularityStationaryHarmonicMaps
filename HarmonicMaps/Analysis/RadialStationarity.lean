module

public import HarmonicMaps.Analysis.RadialStressCentered
public import HarmonicMaps.Analysis.InnerVariationStationarity

/-!
# Radial stationarity from local energy minimality

A source radial profile supplies an admissible centered vector field. The
proved inner-variation identity then yields the exact radial integral
identity, with genuine L1 terms and the original gradient witness.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- The complete radial-test consequence of local minimality on an arbitrary
centered ball. Stationarity, test admissibility, and integrability are all
proved from the original map, gradient, and radial-profile assumptions. -/
theorem IsLocallyEnergyMinimizing.radial_stationarity {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) {eta : ℝ → ℝ}
    (hsProfile : ContDiff ℝ ∞ eta)
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0)
    {ρ : ℝ} (hρR : ρ < R) (hvanish : ∀ t : ℝ, ρ ≤ t → eta t = 0) :
    IntegrableOn (fun x =>
      (((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) * hsNormSq (Du x))
      (Metric.ball a R) volume ∧
    IntegrableOn (fun x => ‖x - a‖ * deriv eta ‖x - a‖ *
      ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) (Metric.ball a R) volume ∧
    (∫ x in Metric.ball a R,
      (((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) * hsNormSq (Du x)) =
      2 * (∫ x in Metric.ball a R, ‖x - a‖ * deriv eta ‖x - a‖ *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) := by
  have hw := hu.memW12_ball hball
  have hi := hw.integrable_radial_stress_terms_centered hsProfile
  obtain ⟨hζ, hcζ, hsζ⟩ := radialVectorField_admissible hsProfile hplateau hρR hvanish a
  have hstationary := (hmin.innerVariation_stationarity hu hN hR hball hζ hcζ hsζ).2
  have halgebra := hw.radial_stress_integral_identity_centered hsProfile hplateau
  refine ⟨hi.1, hi.2, sub_eq_zero.mp ?_⟩
  exact halgebra.symm.trans hstationary

end HarmonicMaps
