module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Original density values under the literal dyadic maximal function

The actual dyadic radii approach zero. Native Lebesgue differentiation,
null spheres and the true nonnegative average identity show that the
original L1 density is bounded almost everywhere by the same extended
maximal function, with constant one. Infinite maximal values are retained.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original integrable AE-nonnegative real densities are dominated almost everywhere by their literal full integer-scale maximal function. -/
theorem ae_ofReal_le_dyadicBallMaximal {n : ℕ}
    (f : Domain n → ℝ) (hf : Integrable f volume) (hf0 : ∀ᵐ x ∂volume,0≤f x) :
    ∀ᵐ x ∂volume,ENNReal.ofReal (f x)≤dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x := by
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average volume hf.locallyIntegrable 1
  let r := fun k : ℕ=>(1/2 : ℝ)^k
  have hr (k : ℕ) : 0<r k := pow_pos (by norm_num) k
  have hRadius : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall hr⟩
  filter_upwards [hLeb] with x hx
  have hCenter : ∀ᶠ k : ℕ in atTop,x∈Metric.closedBall x (1*r k) :=
    Eventually.of_forall fun k=>by
      simp only [Metric.mem_closedBall,dist_self,one_mul]
      exact (hr k).le
  have hLimitClosed := hx (fun _k : ℕ=>x) r hRadius hCenter
  have hAverageEq (k : ℕ) : (⨍ y in Metric.ball x (r k),f y)=
      ⨍ y in Metric.closedBall x (r k),f y :=
    setAverage_congr (ball_ae_eq_closedBall x (hr k))
  have hLimit : Tendsto (fun k=>ENNReal.ofReal (⨍ y in Metric.ball x (r k),f y))
      atTop (𝓝 (ENNReal.ofReal (f x))) := by
    simpa only [Function.comp_def,hAverageEq] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hLimitClosed
  apply le_of_tendsto hLimit
  apply Eventually.of_forall
  intro k
  have hScale : r k=(2 : ℝ)^(-(k : ℤ)) := by
    simp only [r,zpow_neg,zpow_natCast,one_div,inv_pow]
  have hMean : ENNReal.ofReal (⨍ y in Metric.ball x (r k),f y)=
      centeredBallAverageENN (fun y=>ENNReal.ofReal (f y)) x ⟨r k,hr k⟩ := by
    rw [ofReal_setAverage hf.integrableOn (ae_restrict_of_ae hf0),
      centeredBallAverageENN,ENNReal.div_eq_inv_mul]
  rw [hMean]
  unfold dyadicBallMaximal
  have hRad : (⟨r k,hr k⟩ : PositiveRadius)=⟨(2 : ℝ)^(-(k : ℤ)),zpow_pos (by norm_num) _⟩ :=
    Subtype.ext hScale
  rw [hRad]
  exact le_iSup (fun j : ℤ=>centeredBallAverageENN
    (fun y=>ENNReal.ofReal (f y)) x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩) (-(k : ℤ))

end StationaryHarmonicMaps.Analysis

end
