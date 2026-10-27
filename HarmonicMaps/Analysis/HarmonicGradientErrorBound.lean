module

public import HarmonicMaps.Analysis.HarmonicGradientErrorGreen

/-!
# Bounding the harmonic replacement gradient error

The signed Green identity and the real inner-product bound reduce the gradient
error to a pointwise difference bound times the actual L1 Laplacian norm.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- A conditional quantitative form of the genuine Green error identity. -/
theorem harmonic_gradientError_le_of_pointwise_distance {n q : ℕ}
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m w : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (hw : ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val))
    (hharm : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0)
    (hzero : HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
      (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1)))
    (δ : ℝ) (hδ : ∀ x ∈ Metric.ball (0 : Domain n) R.val, ‖m x - w x‖ ≤ δ)
    (hLap : IntegrableOn (fun x => ‖Laplacian.laplacian m x‖)
      (Metric.ball (0 : Domain n) R.val) volume) :
    (∫ x in Metric.ball (0 : Domain n) R.val,
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
      δ * (∫ x in Metric.ball (0 : Domain n) R.val, ‖Laplacian.laplacian m x‖) := by
  let B : Set (Domain n) := Metric.ball 0 R.val
  have hGreen := harmonic_gradientError_green R U hU hclosed m w hm hw hharm hzero
  obtain ⟨_, hRight, _⟩ :=
    dirichlet_zeroBoundary_green_laplacian R U hU hclosed m hm (m - w)
      (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1)) hzero
  have hpoint (x : Domain n) (hx : x ∈ B) :
      -inner ℝ (Laplacian.laplacian m x) (m x - w x) ≤
        δ * ‖Laplacian.laplacian m x‖ := by
    calc
      _ ≤ |inner ℝ (Laplacian.laplacian m x) (m x - w x)| := neg_le_abs _
      _ ≤ ‖Laplacian.laplacian m x‖ * ‖m x - w x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖Laplacian.laplacian m x‖ * δ :=
        mul_le_mul_of_nonneg_left (hδ x hx) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hIntegral := setIntegral_mono_on hRight.neg (hLap.const_mul δ)
    measurableSet_ball hpoint
  change (∫ x in B, hsNormSq (fun i =>
    fderiv ℝ m x (EuclideanSpace.single i 1) -
      fderiv ℝ w x (EuclideanSpace.single i 1))) =
    -(∫ x in B, inner ℝ (Laplacian.laplacian m x) ((m - w) x)) at hGreen
  calc
    _ = -(∫ x in B, inner ℝ (Laplacian.laplacian m x) ((m - w) x)) := hGreen
    _ = (∫ x in B, -inner ℝ (Laplacian.laplacian m x) ((m - w) x)) := by
      rw [integral_neg]
    _ ≤ (∫ x in B, δ * ‖Laplacian.laplacian m x‖) := hIntegral
    _ = _ := by rw [integral_const_mul]

end HarmonicMaps
end
