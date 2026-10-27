module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Center continuity and open maximal superlevels

For the original extended L1 density, ball indicators converge as their
center moves away from the null sphere. The original density is the true
dominated-convergence bound. Every fixed-radius average is finite and
continuous. Their literal full integer-scale supremum is lower
semicontinuous, including its possible infinite point values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- An original extended L1 density gives finite continuous ball averages at every center, with continuous real values only after that finiteness is proved. -/
theorem continuous_centeredBallAverageENN_of_lintegral_ne_top {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume)
    (hFinite : (∫⁻ y,f y)≠∞) (r : PositiveRadius) :
    Continuous (fun x=>centeredBallAverageENN f x r) ∧
      (∀ x,centeredBallAverageENN f x r≠∞) ∧
      Continuous (fun x=>(centeredBallAverageENN f x r).toReal) := by
  have hPoint (a : Domain n) : ∀ᵐ y ∂volume,
      Tendsto (fun x : Domain n=>(Metric.ball x r.val).indicator f y) (𝓝 a)
        (𝓝 ((Metric.ball a r.val).indicator f y)) := by
    filter_upwards [HarmonicMaps.ball_ae_eq_closedBall a r.property] with y hy
    have hSphere : dist y a≠r.val := by
      intro hEq
      have hCB : y∈Metric.closedBall a r.val := by rw [Metric.mem_closedBall,hEq]
      have hBall : y∈Metric.ball a r.val := Eq.mpr hy hCB
      change dist y a<r.val at hBall
      rw [hEq] at hBall
      exact (lt_irrefl _) hBall
    by_cases hIn : dist y a<r.val
    · have hNear : ∀ᶠ x in 𝓝 a,dist y x<r.val :=
        (isOpen_lt (continuous_const.dist continuous_id) continuous_const).mem_nhds hIn
      rw [indicator_of_mem (s:=Metric.ball a r.val) hIn]
      apply tendsto_const_nhds.congr'
      filter_upwards [hNear] with x hx
      exact (indicator_of_mem (s:=Metric.ball x r.val) hx f).symm
    · have hOut : r.val<dist y a := lt_of_le_of_ne (le_of_not_gt hIn) hSphere.symm
      have hNear : ∀ᶠ x in 𝓝 a,r.val<dist y x :=
        (isOpen_lt continuous_const (continuous_const.dist continuous_id)).mem_nhds hOut
      rw [indicator_of_notMem (s:=Metric.ball a r.val) hIn]
      apply tendsto_const_nhds.congr'
      filter_upwards [hNear] with x hx
      exact (indicator_of_notMem (s:=Metric.ball x r.val) (not_lt_of_ge hx.le) f).symm
  have hIntegral : Continuous (fun x : Domain n=>∫⁻ y in Metric.ball x r.val,f y) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    have H := tendsto_lintegral_filter_of_dominated_convergence' f
      (Eventually.of_forall fun x : Domain n=>hf.indicator measurableSet_ball)
      (Eventually.of_forall fun x : Domain n=>Eventually.of_forall fun y=>by
        by_cases hy : y∈Metric.ball x r.val
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy];exact zero_le)
      hFinite (hPoint a)
    change Tendsto (fun x : Domain n=>∫⁻ y in Metric.ball x r.val,f y) (𝓝 a) (𝓝 (∫⁻ y in Metric.ball a r.val,f y))
    simpa only [lintegral_indicator measurableSet_ball] using H
  have hVolume (x : Domain n) : volume (Metric.ball x r.val)=volume (Metric.ball (0 : Domain n) r.val) := by
    rw [Measure.addHaar_ball_of_pos volume x r.property,
      Measure.addHaar_ball_of_pos volume (0 : Domain n) r.property]
  have hContinuous : Continuous (fun x=>centeredBallAverageENN f x r) := by
    unfold centeredBallAverageENN
    simp_rw [hVolume]
    exact (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr
      (Metric.measure_ball_pos volume (0 : Domain n) r.property).ne')).comp hIntegral
  have hAverageFinite (x : Domain n) : centeredBallAverageENN f x r≠∞ := by
    have hI : (∫⁻ y in Metric.ball x r.val,f y)≤∫⁻ y,f y := by
      simpa only [Measure.restrict_univ] using lintegral_mono_set (f:=f) (μ:=volume) (subset_univ (Metric.ball x r.val))
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (Metric.measure_ball_pos volume x r.property).ne')
      (ne_of_lt (hI.trans_lt (lt_top_iff_ne_top.mpr hFinite)))
  exact ⟨hContinuous,hAverageFinite,continuous_iff_continuousAt.mpr fun x=>
    (ENNReal.continuousAt_toReal (hAverageFinite x)).comp (f:=fun z : Domain n=>centeredBallAverageENN f z r) (hContinuous.continuousAt (x:=x))⟩

/-- The literal full dyadic maximal function of the original L1 density is lower semicontinuous; its supremum need not be finite at every center. -/
theorem lowerSemicontinuous_dyadicBallMaximal_of_lintegral_ne_top {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (hFinite : (∫⁻ y,f y)≠∞) :
    LowerSemicontinuous (dyadicBallMaximal f) := by
  exact lowerSemicontinuous_iSup fun j : ℤ=>
    (continuous_centeredBallAverageENN_of_lintegral_ne_top f hf hFinite
      ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩).1.lowerSemicontinuous

/-- Every actual strict superlevel of the same extended dyadic maximal function is open. -/
theorem isOpen_dyadicBallMaximal_superlevel_of_lintegral_ne_top {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (hFinite : (∫⁻ y,f y)≠∞)
    (L : ℝ≥0∞) : IsOpen {x | L<dyadicBallMaximal f x} :=
  (lowerSemicontinuous_dyadicBallMaximal_of_lintegral_ne_top f hf hFinite).isOpen_preimage L

end StationaryHarmonicMaps.Analysis

end
