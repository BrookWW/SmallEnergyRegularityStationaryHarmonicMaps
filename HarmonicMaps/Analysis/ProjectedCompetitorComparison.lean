module

public import HarmonicMaps.Analysis.SobolevAECollar
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.Minimizer
public import HarmonicMaps.SobolevRestriction

/-!
# Minimality comparison for an annular competitor

Almost-everywhere equality on the open outer collar identifies the original
weak gradients there. Native zero-boundary graph closure makes the competitor
admissible. Integrable energy decomposition and null spheres cancel the equal
outer energies without any continuity assumption on the original map.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- Null spheres give an exact integrable decomposition into a ball and its
open outer collar. -/
theorem ball_integral_split_closed_collar {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (f : Domain n → ℝ) (hf : IntegrableOn f (Metric.ball (0 : Domain n) R) volume) :
    (∫ x in Metric.ball (0 : Domain n) R, f x) =
      (∫ x in Metric.ball (0 : Domain n) r, f x) +
      (∫ x in Metric.ball (0 : Domain n) R \ Metric.closedBall 0 r, f x) := by
  have h := setIntegral_sdiff measurableSet_closedBall hf
    (Metric.closedBall_subset_ball hrR)
  rw [← setIntegral_congr_set (ball_ae_eq_closedBall (0 : Domain n) hr)] at h
  linarith only [h]

/-- Native finite Sobolev data and actual collar equality yield zero-boundary
admissibility and the inner-ball energy comparison. -/
theorem projectedCompetitor_collar_comparison {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q)
    (u v : Domain n → Ambient q) (Du Dv : Domain n → Gradient n q)
    (theta delta : ℝ) (hd : 0 < delta) (ht : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2)
    (hu : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) u Du)
    (hv : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) v Dv)
    (hNv : TakesValuesIn N (ballDomain (0 : Domain n) (theta + 2 * delta)) v)
    (hmin : IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du)
    (heq : u =ᵐ[volume.restrict
      (Metric.ball (0 : Domain n) (theta + 2 * delta) \ Metric.closedBall 0 (theta + delta))] v) :
    HasZeroBoundaryDifference (ballDomain (0 : Domain n) (theta + 2 * delta)) u Du v Dv ∧
    dirichletEnergy Du (Metric.ball (0 : Domain n) (theta + 2 * delta)) ≤
      dirichletEnergy Dv (Metric.ball (0 : Domain n) (theta + 2 * delta)) ∧
    (∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Du x)) ≤
      ∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Dv x) := by
  let U : Set (Domain n) := Metric.ball 0 (theta + 2 * delta)
  let V : Set (Domain n) := U \ Metric.closedBall 0 (theta + delta)
  have ht0 : 0 < theta := hd.trans ht
  have hr : 0 < theta + delta := add_pos ht0 hd
  have hR : 0 < theta + 2 * delta := by linarith only [ht0, hd]
  have hrR : theta + delta < theta + 2 * delta := by linarith only [hd]
  have hV : IsOpen V := Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
  have hzero : HasZeroBoundaryDifference (ballDomain (0 : Domain n) (theta + 2 * delta))
      u Du v Dv := by
    apply (hv.sub hu).zeroBoundary_of_ae_zero_collar_ball hR hr.le hrR
    filter_upwards [heq] with x hx
    exact sub_eq_zero.mpr hx.symm
  have hclosed : Metric.closedBall (0 : Domain n) (theta + 2 * delta) ⊆
      Metric.ball 0 1 := Metric.closedBall_subset_ball (by linarith only [hhalf])
  have hminimal := hmin 0 (theta + 2 * delta) hR hclosed v Dv hv hNv hzero
  have hgradient : Du =ᵐ[volume.restrict V] Dv :=
    (hu.1.mono (Ω' := ⟨V, hV⟩) sdiff_subset).ae_eq_of_ae_eq_map
      (hv.1.mono (Ω' := ⟨V, hV⟩) sdiff_subset) heq
  have houter : (∫ x in V, hsNormSq (Du x)) = ∫ x in V, hsNormSq (Dv x) :=
    integral_congr_ae (hgradient.fun_comp hsNormSq)
  have hreal := ENNReal.toReal_le_toReal hu.dirichletEnergy_ne_top hv.dirichletEnergy_ne_top
  have hineq := hreal.mpr hminimal
  rw [dirichletEnergy_toReal hu.integrable_hsNormSq,
    dirichletEnergy_toReal hv.integrable_hsNormSq] at hineq
  change (∫ x in Metric.ball (0 : Domain n) (theta + 2 * delta), hsNormSq (Du x)) ≤
    (∫ x in Metric.ball (0 : Domain n) (theta + 2 * delta), hsNormSq (Dv x)) at hineq
  rw [
    ball_integral_split_closed_collar hr hrR _ hu.integrable_hsNormSq,
    ball_integral_split_closed_collar hr hrR _ hv.integrable_hsNormSq] at hineq
  change (∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Du x)) +
      (∫ x in V, hsNormSq (Du x)) ≤
    (∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Dv x)) +
      (∫ x in V, hsNormSq (Dv x)) at hineq
  rw [houter] at hineq
  exact ⟨hzero, hminimal, (add_le_add_iff_right _).mp hineq⟩

end HarmonicMaps
end
