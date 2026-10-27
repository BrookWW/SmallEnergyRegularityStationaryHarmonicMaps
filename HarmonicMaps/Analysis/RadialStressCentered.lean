module

public import HarmonicMaps.Analysis.RadialStressIntegral
public import HarmonicMaps.Analysis.RadialTestAdmissibility

/-!
# Radial stress at an arbitrary center

Translation has identity derivative, so the existing all-point radial stress
algebra applies to the actual centered test field and the original gradient.
Both radial terms are integrable on the same arbitrary-center Sobolev ball.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- Translating the radial field changes its evaluation point and leaves the
tangent vector unchanged in the actual derivative. -/
theorem radialVectorField_centered_fderiv {n : ℕ} {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) (a x : Domain n) :
    fderiv ℝ (fun y => radialVectorField eta (y - a)) x =
      fderiv ℝ (radialVectorField eta) (x - a) := by
  have hd := ((radialVectorField_contDiff hs hp).differentiable (by simp) (x - a)).hasFDerivAt
  have hc := hd.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using hc.fderiv

/-- The actual centered stress identity holds everywhere, including the
center, without assigning a radial direction there. -/
theorem radialStressEnergyIdentity_centered {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) (a x : Domain n) :
    hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ (fun y => radialVectorField eta (y - a)) x
        (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ (fun y => radialVectorField eta (y - a)) x
            (EuclideanSpace.single i 1)) j) =
      (((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) * hsNormSq (Du x) -
        2 * (‖x - a‖ * deriv eta ‖x - a‖ *
          ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) := by
  rw [radialVectorField_centered_fderiv hs hp a x]
  have h := radialStressEnergyIdentity_all (fun _ => Du x) hs hp (x - a)
  simpa only [mul_assoc] using h

/-- Both centered radial stress terms are genuinely L1 for the original
finite Sobolev map and its same displayed gradient. -/
theorem MemW12.integrable_radial_stress_terms_centered {n q : ℕ}
    {a : Domain n} {R : ℝ} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 (ballDomain a R) u Du) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta) :
    IntegrableOn (fun x =>
      (((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) * hsNormSq (Du x))
      (Metric.ball a R) volume ∧
    IntegrableOn (fun x => ‖x - a‖ * deriv eta ‖x - a‖ *
      ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) (Metric.ball a R) volume := by
  have hd : Continuous (deriv eta) := hs.continuous_deriv (by norm_num)
  have hc : Continuous (fun x : Domain n =>
      ((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) := by fun_prop
  have hc' : Continuous (fun x : Domain n => ‖x - a‖ * deriv eta ‖x - a‖) := by fun_prop
  have he : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball a R) volume :=
    h.integrable_hsNormSq
  have hr : IntegrableOn (fun x => ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      (Metric.ball a R) volume := h.integrable_radial_columns a
  exact ⟨IntegrableOn.continuousOn_mul_of_subset hc.continuousOn he
      (isCompact_closedBall a R) Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall,
    IntegrableOn.continuousOn_mul_of_subset hc'.continuousOn hr
      (isCompact_closedBall a R) Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall⟩

/-- Integration of the centered pointwise algebra retains the exact factor
two and uses actual integrable terms, with no stationarity assumption. -/
theorem MemW12.radial_stress_integral_identity_centered {n q : ℕ}
    {a : Domain n} {R : ℝ} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 (ballDomain a R) u Du) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    (∫ x in Metric.ball a R,
      hsNormSq (Du x) *
        (∑ i : Fin n, (fderiv ℝ (fun y => radialVectorField eta (y - a)) x
          (EuclideanSpace.single i 1)) i) -
        2 * (∑ i : Fin n, ∑ j : Fin n,
          inner ℝ (Du x i) (Du x j) *
            (fderiv ℝ (fun y => radialVectorField eta (y - a)) x
              (EuclideanSpace.single i 1)) j)) =
      (∫ x in Metric.ball a R,
        (((n : ℝ) - 2) * eta ‖x - a‖ + ‖x - a‖ * deriv eta ‖x - a‖) * hsNormSq (Du x)) -
      2 * (∫ x in Metric.ball a R, ‖x - a‖ * deriv eta ‖x - a‖ *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) := by
  simp_rw [radialStressEnergyIdentity_centered Du hs hp a]
  have hi := h.integrable_radial_stress_terms_centered hs
  rw [integral_sub hi.1 (hi.2.const_mul 2), integral_const_mul]

end HarmonicMaps
