module

public import HarmonicMaps.Analysis.HarmonicEnergyOrthogonality
public import HarmonicMaps.Analysis.DirichletZeroBoundaryGreen

/-!
# Signed gradient-error identity

The same zero-boundary difference tests the smooth datum and its harmonic
replacement. Subtracting their Green identities gives the exact negative
Laplacian formula for the difference energy.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- The source gradient-error equality uses the genuine zero-boundary test,
the same classical difference columns and the negative Laplacian sign. -/
theorem harmonic_gradientError_green {n q : ℕ}
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m w : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (hw : ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val))
    (hharm : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0)
    (hzero : HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
      (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1))) :
    let Ddiff : Domain n → Gradient n q := fun x i =>
      fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1)
    (∫ x in Metric.ball (0 : Domain n) R.val, hsNormSq (Ddiff x)) =
      -(∫ x in Metric.ball (0 : Domain n) R.val,
        inner ℝ (Laplacian.laplacian m x) ((m - w) x)) := by
  let B : Set (Domain n) := Metric.ball 0 R.val
  let Ddiff : Domain n → Gradient n q := fun x i =>
    fderiv ℝ m x (EuclideanSpace.single i 1) - fderiv ℝ w x (EuclideanSpace.single i 1)
  obtain ⟨hmixedInt, _, hmGreen⟩ :=
    dirichlet_zeroBoundary_green_laplacian R U hU hclosed m hm (m - w) Ddiff hzero
  obtain ⟨hwmixedInt, _, hwGreen⟩ :=
    closed_dirichlet_zeroBoundary_green_laplacian R w hw (m - w) Ddiff hzero
  have hzeroLap (x : Domain n) (hx : x ∈ B) :
      inner ℝ (Laplacian.laplacian w x) ((m - w) x) = 0 := by
    rw [hharm x hx, inner_zero_left]
  have hwMixedZero :
      (∫ x in B, ∑ i : Fin n,
        inner ℝ (fderiv ℝ w x (EuclideanSpace.single i 1)) (Ddiff x i)) = 0 := by
    calc
      _ = -(∫ x in B, inner ℝ (Laplacian.laplacian w x) ((m - w) x)) := hwGreen
      _ = 0 := by
        rw [setIntegral_congr_fun measurableSet_ball hzeroLap]
        simp
  have hpoint (x : Domain n) :
      hsNormSq (Ddiff x) =
      (∑ i : Fin n, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Ddiff x i)) -
      (∑ i : Fin n, inner ℝ (fderiv ℝ w x (EuclideanSpace.single i 1)) (Ddiff x i)) := by
    simp only [hsNormSq]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hinner := inner_sub_left (𝕜 := ℝ)
      (fderiv ℝ m x (EuclideanSpace.single i 1))
      (fderiv ℝ w x (EuclideanSpace.single i 1)) (Ddiff x i)
    change inner ℝ (Ddiff x i) (Ddiff x i) = _ at hinner
    rw [real_inner_self_eq_norm_sq] at hinner
    exact hinner
  calc
    (∫ x in B, hsNormSq (Ddiff x)) =
        ∫ x in B,
          (∑ i : Fin n, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Ddiff x i)) -
          (∑ i : Fin n, inner ℝ (fderiv ℝ w x (EuclideanSpace.single i 1)) (Ddiff x i)) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x _
      exact hpoint x
    _ = (∫ x in B, ∑ i : Fin n,
          inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Ddiff x i)) -
        (∫ x in B, ∑ i : Fin n,
          inner ℝ (fderiv ℝ w x (EuclideanSpace.single i 1)) (Ddiff x i)) :=
      integral_sub hmixedInt hwmixedInt
    _ = _ := by rw [hmGreen, hwMixedZero, sub_zero]

end HarmonicMaps
end
