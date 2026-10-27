module

public import HarmonicMaps.Analysis.RadialStressCentered
public import StationaryHarmonicMaps.Analysis.DomainStressLocality

/-! # Radial stress identity for domain-stationary Sobolev maps -/

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

theorem IsDomainStationary.radial_stationarity {n q : ℕ}
    {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hstationary : IsDomainStationary Ω Du) (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ}
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
  have hstationary := (hstationary.test_ball hball hζ hcζ hsζ).2
  have halgebra := hw.radial_stress_integral_identity_centered hsProfile hplateau
  refine ⟨hi.1, hi.2, sub_eq_zero.mp ?_⟩
  exact halgebra.symm.trans hstationary

end StationaryHarmonicMaps
