module

public import HarmonicMaps.Analysis.VariableMollificationL2
public import HarmonicMaps.Analysis.VariableMollificationSmoothSobolev
public import HarmonicMaps.Analysis.SobolevSmoothDensity

/-!
# Smooth density and identification of the actual variable-average limits

Whole-ball Euclidean smooth density and the proved square estimates identify
the literal averaged map and original-gradient tensor averages as the L2
limits. The actual weak Sobolev graph then closes for those same functions.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

/-- The source assumptions produce an actual smooth density sequence whose
literal map and tensor averages converge to the displayed original-input
averages in every coordinate L2 norm. -/
theorem variableMollification_actual_L2_limits {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (hf : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) f Df) :
    let U := Metric.ball (0 : Domain n) (theta + 2 * delta)
    let B := fun x y : Domain n =>
      ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y
    let T := fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - s x • y)
    let DT := fun x (i : Fin n) => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • ∑ j : Fin n,
        (B x y (EuclideanSpace.single i 1)) j • Df (x - s x • y) j
    ∃ m : ℕ → Domain n → Ambient q, ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ k, MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) (m k)
        (fun x i => coordinateDerivative (m k) (hm k) i x)) ∧
      Tendsto (fun k => eLpNorm (m k - f) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      (∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - Df x i)
          2 (volume.restrict U)) atTop (𝓝 0)) ∧
      (∀ k, MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta))
        (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • m k (x - s x • y))
        (fun x i => ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • ∑ j : Fin n,
            (B x y (EuclideanSpace.single i 1)) j •
              coordinateDerivative (m k) (hm k) j (x - s x • y))) ∧
      Tendsto (fun k => eLpNorm
        ((fun x => ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • m k (x - s x • y)) - T)
          2 (volume.restrict U)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => (∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • ∑ j : Fin n,
            (B x y (EuclideanSpace.single i 1)) j •
              coordinateDerivative (m k) (hm k) j (x - s x • y)) - DT x i)
        2 (volume.restrict U)) atTop (𝓝 0) := by
  have hR : 0 < theta + 2 * delta := by linarith only [hdelta, htheta]
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hf.smoothDensity_memW12_ball hR
  have hK : 0 ≤ (1 - L)⁻¹ := inv_nonneg.mpr (by linarith only [hL])
  have hbound (y : Domain n) (hy : y ∈ Metric.ball 0 1) :=
    (variableShift_map_restrict_le hdelta htheta hhalf hs hradial hvalues hplateau hoff
      hhbar hDs hL y hy).1
  refine ⟨m, hm, hmW, hconv, hDconv, ?_, ?_, ?_⟩
  · intro k
    exact variableMollification_smooth_memW12 hdelta htheta hhalf hs hradial hvalues hplateau
      hoff hhbar hDs hL (m k) (hm k).contDiffOn (hmW k).2.1 (hmW k).2.2
  · exact variableMollification_tendsto_map (f := m) (g := f)
      hs hvalues hhbar hoff hK hbound
      (fun k => (hmW k).2.1) hf.2.1 hconv
  · exact variableMollification_tendsto_tensor
      (D := fun k x i => coordinateDerivative (m k) (hm k) i x) (Dg := Df)
      hs hvalues hhbar hoff hDs hK hbound
      (fun k => (hmW k).2.2) hf.2.2 hDconv

/-- The actual original-input integral has its literal original-gradient
tensor average as a weak gradient on the source ball. -/
theorem MemW12.variableMollification {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) f Df) :
    MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta))
      (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f (x - s x • y))
      (fun x i => ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • Df (x - s x • y) j) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) (theta + 2 * delta))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hK : 0 ≤ (1 - L)⁻¹ := inv_nonneg.mpr (by linarith only [hL])
  have hbound (y : Domain n) (hy : y ∈ Metric.ball 0 1) :=
    (variableShift_map_restrict_le hdelta htheta hhalf hs hradial hvalues hplateau hoff
      hhbar hDs hL y hy).1
  obtain ⟨m, hm, _, _, _, hTm, hTconv, hDTconv⟩ :=
    variableMollification_actual_L2_limits hdelta htheta hhalf hs hradial hvalues hplateau
      hoff hhbar hDs hL f Df hf
  have hMap := (variableMollification_map_bounds hs hK hbound hf.2.1).2.2.1
  have hTensor := (variableMollification_tensor_bounds hs hDs hK hbound hf.2.2).2.2.1
  exact MemW12.of_L2_limit_ball (0 : Domain n) (theta + 2 * delta)
    hTm hMap hTensor hTconv hDTconv

end HarmonicMaps
