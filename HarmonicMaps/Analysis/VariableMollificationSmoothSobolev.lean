module

public import HarmonicMaps.Analysis.VariableMollificationWeak

/-!
# Sobolev membership of the actual smooth-input variable average

The local differential formula and sharp map and tensor L2 bounds supply
the genuine weak columns of the literal average on the source outer ball.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- Local smoothness and finite classical graph data produce the actual
averaged Sobolev map and tensor columns. Smooth density supplies these
classical graph data in the original Sobolev limit application. -/
theorem variableMollification_smooth_memW12 {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) (theta + 2 * delta)))
    (hf2 : MemLp f 2 (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (hDf2 : ∀ i : Fin n, MemLp
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict (Metric.ball 0 (theta + 2 * delta)))) :
    MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta))
      (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f (x - s x • y))
      (fun x i => ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j •
          fderiv ℝ f (x - s x • y) (EuclideanSpace.single j 1)) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) (theta + 2 * delta))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hK : 0 ≤ (1 - L)⁻¹ := inv_nonneg.mpr (by linarith only [hL])
  have hbound (y : Domain n) (hy : y ∈ Metric.ball 0 1) :=
    (variableShift_map_restrict_le hdelta htheta hhalf hs hradial hvalues hplateau hoff
      hhbar hDs hL y hy).1
  have hMap := (variableMollification_map_bounds hs hK hbound hf2).2.2.1
  have hTensor := (variableMollification_tensor_bounds hs hDs hK hbound hDf2).2.2.1
  obtain ⟨_, _, hDifferential⟩ := variableMollification_smooth_formula hdelta htheta hhalf hs
    hradial hvalues hplateau hoff hhbar hDs hL f hf
  apply memW12_ball_of_differentiableAt
    (fun x hx => (hDifferential x hx).differentiableAt) _ hMap hTensor
  intro x hx i
  exact variableMollification_smooth_column hdelta htheta hhalf hs hradial hvalues hplateau
    hoff hhbar hDs hL f hf hx i

end HarmonicMaps
