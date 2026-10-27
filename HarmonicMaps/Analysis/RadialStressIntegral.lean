module

public import HarmonicMaps.Analysis.RadialStressGeometry
public import HarmonicMaps.Analysis.RadialIntegrability
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Integration of the radial stress algebra

The Sobolev assumptions supply all required integrability. These equalities
integrate the actual stress integrand; they do not assert stationarity.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- The pointwise stress identity uses the literal radial column expression
at all points, including the true plateau differential at the origin. -/
theorem radialStressEnergyIdentity_all {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) (x : Domain n) :
    hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j) =
      (((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) * hsNormSq (Du x) -
        2 * ‖x‖ * deriv eta ‖x‖ *
          ‖‖x‖⁻¹ • ∑ i : Fin n, x i • Du x i‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    rw [radialStressEnergyIdentity_zero Du hp]
    simp only [norm_zero, zero_mul, add_zero, mul_zero, sub_zero]
  · exact radialStressEnergyIdentity Du ((hs.differentiable (by norm_num)) ‖x‖) hx

/-- Smooth radial coefficients preserve the genuine L1 energy densities on
a Sobolev ball. -/
theorem MemW12.integrable_radial_stress_terms {n q : ℕ} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 (ballDomain 0 R) u Du) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta) :
    IntegrableOn (fun x =>
      (((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) * hsNormSq (Du x))
      (Metric.ball 0 R) volume ∧
    IntegrableOn (fun x => 2 * ‖x‖ * deriv eta ‖x‖ *
      ‖‖x‖⁻¹ • ∑ i : Fin n, x i • Du x i‖ ^ 2) (Metric.ball 0 R) volume := by
  have hd : Continuous (deriv eta) := hs.continuous_deriv (by norm_num)
  have hc : Continuous (fun x : Domain n =>
      ((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) := by fun_prop
  have hc' : Continuous (fun x : Domain n => 2 * ‖x‖ * deriv eta ‖x‖) := by fun_prop
  have he : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball 0 R) volume :=
    h.integrable_hsNormSq
  have hr : IntegrableOn (fun x => ‖‖x‖⁻¹ • ∑ i : Fin n, x i • Du x i‖ ^ 2)
      (Metric.ball 0 R) volume := by
    simpa only [sub_zero, ballDomain] using h.integrable_radial_columns 0
  exact ⟨IntegrableOn.continuousOn_mul_of_subset hc.continuousOn he
      (isCompact_closedBall 0 R) Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall,
    IntegrableOn.continuousOn_mul_of_subset hc'.continuousOn hr
      (isCompact_closedBall 0 R) Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall⟩

/-- The actual radial stress integrand is integrable for the same Sobolev
gradient, including at the center. -/
theorem MemW12.integrable_radial_stress {n q : ℕ} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 (ballDomain 0 R) u Du) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j))
      (Metric.ball (0 : Domain n) R) volume := by
  have ht := h.integrable_radial_stress_terms hs
  exact (ht.1.sub ht.2).congr
    (Filter.Eventually.of_forall fun x => (radialStressEnergyIdentity_all Du hs hp x).symm)

/-- Integrating the radial algebra produces the exact two energy terms from
actual Sobolev integrability, without assuming any stationarity equation. -/
theorem MemW12.radial_stress_integral_identity {n q : ℕ} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 (ballDomain 0 R) u Du) {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hp : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    (∫ x in Metric.ball (0 : Domain n) R,
      hsNormSq (Du x) *
        (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) -
        2 * (∑ i : Fin n, ∑ j : Fin n,
          inner ℝ (Du x i) (Du x j) *
            (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j)) =
      (∫ x in Metric.ball (0 : Domain n) R,
        (((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) * hsNormSq (Du x)) -
      (∫ x in Metric.ball (0 : Domain n) R,
        2 * ‖x‖ * deriv eta ‖x‖ * ‖‖x‖⁻¹ • ∑ i : Fin n, x i • Du x i‖ ^ 2) := by
  simp_rw [radialStressEnergyIdentity_all Du hs hp]
  exact integral_sub (h.integrable_radial_stress_terms hs).1
    (h.integrable_radial_stress_terms hs).2

end HarmonicMaps
