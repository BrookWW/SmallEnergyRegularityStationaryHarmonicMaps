module

public import StationaryHarmonicMaps.Analysis.DyadicMaximalLocalization
public import StationaryHarmonicMaps.Analysis.DyadicMaximalWeakOne

/-!
# Genuine local maximal control from near and far densities

A supplied nearby good point controls all large scales. On the remaining
small scales the original ball lies in the same sixfold neighborhood.
The actual local near/far density inequality and actual far bound then
force a large original average to be a large near average. The genuine
full-scale weak L1 theorem supplies the resulting local measure bound.
This lemma does not assume a desired maximal level-measure estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem average_le_near_add_constant {n : ℕ}
    (f g : Domain n → ℝ≥0∞) (hg : AEMeasurable g volume)
    (a x : Domain n) (r : ℝ) (hx : x∈Metric.ball a (5*r))
    (R : PositiveRadius) (hR : R.val≤r) (Q : ℝ≥0∞)
    (hLocal : ∀ᵐ z ∂volume.restrict (Metric.ball a (6*r)),f z≤2*g z+Q) :
    centeredBallAverageENN f x R≤2*centeredBallAverageENN g x R+Q := by
  have hSub : Metric.ball x R.val⊆Metric.ball a (6*r) := by
    intro z hz
    have hzDist : dist z x<R.val := hz
    have hxDist : dist x a<5*r := hx
    exact lt_of_le_of_lt (dist_triangle z x a) (by linarith)
  have hRestrict : volume.restrict (Metric.ball x R.val)≤volume.restrict (Metric.ball a (6*r)) :=
    Measure.restrict_mono_set volume hSub
  have hI : (∫⁻ z in Metric.ball x R.val,f z)≤
      2*(∫⁻ z in Metric.ball x R.val,g z)+Q*volume (Metric.ball x R.val) := by
    calc
      _ ≤ ∫⁻ z in Metric.ball x R.val,2*g z+Q :=
        lintegral_mono_ae (hLocal.filter_mono (ae_mono hRestrict))
      _ = _ := by
        have hMeas : AEMeasurable (fun z=>2*g z) (volume.restrict (Metric.ball x R.val)) :=
          aemeasurable_const.mul (hg.mono_measure Measure.restrict_le_self)
        rw [lintegral_add_left' hMeas,lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞)≠∞),
          lintegral_const,Measure.restrict_apply_univ]
  unfold centeredBallAverageENN
  calc
    _ ≤ (volume (Metric.ball x R.val))⁻¹*
        (2*(∫⁻ z in Metric.ball x R.val,g z)+Q*volume (Metric.ball x R.val)) :=
      mul_le_mul_of_nonneg_left hI zero_le
    _ = 2*((volume (Metric.ball x R.val))⁻¹*∫⁻ z in Metric.ball x R.val,g z)+
        Q*((volume (Metric.ball x R.val))⁻¹*volume (Metric.ball x R.val)) := by rw [mul_add];ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume x R.property).ne' measure_ball_ne_top,mul_one]

/-- Actual local near/far densities and an original nearby maximal good point produce both high-level localization and a genuine local weak measure bound. -/
theorem local_dyadic_maximal_superlevel_measure_of_near_far {n : ℕ}
    (f g h : Domain n → ℝ≥0∞) (hg : AEMeasurable g volume)
    (a y : Domain n) (r : ℝ) (hr : 0<r) (hy : dist y a≤20*r)
    (L A B : ℝ) (hL : 0<L) (hB : 0≤B) (hA : (64 : ℝ)^n≤A) (hAB : 4*B≤A)
    (hGood : dyadicBallMaximal f y≤ENNReal.ofReal L)
    (hSplit : ∀ᵐ z ∂volume.restrict (Metric.ball a (6*r)),f z≤2*g z+2*h z)
    (hFar : ∀ᵐ z ∂volume.restrict (Metric.ball a (6*r)),h z≤ENNReal.ofReal (B*L)) :
    (Metric.ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x})⊆
        {x | ENNReal.ofReal (A*L/4)<dyadicBallMaximal g x} ∧
      volume (Metric.ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x})≤
        ENNReal.ofReal (4*(5 : ℝ)^n/(A*L))*(∫⁻ z,g z) := by
  have hA0 : 0<A := (pow_pos (by norm_num : (0 : ℝ)<64) n).trans_le hA
  have hLevel : 0<A*L/4 := by positivity
  have hLocal : ∀ᵐ z ∂volume.restrict (Metric.ball a (6*r)),f z≤2*g z+2*ENNReal.ofReal (B*L) := by
    filter_upwards [hSplit,hFar] with z hz hhz
    exact hz.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hhz zero_le))
  have hNumeric : (2 : ℝ≥0∞)*ENNReal.ofReal (A*L/4)+2*ENNReal.ofReal (B*L)≤ENNReal.ofReal (A*L) := by
    rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),
      ← ENNReal.ofReal_add (by positivity : 0≤2*(A*L/4)) (by positivity : 0≤2*(B*L))]
    apply ENNReal.ofReal_le_ofReal
    have H := mul_le_mul_of_nonneg_right hAB hL.le
    nlinarith only [H]
  have hSub : (Metric.ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x})⊆
      {x | ENNReal.ofReal (A*L/4)<dyadicBallMaximal g x} := by
    intro x hx
    have hxHigh : ENNReal.ofReal (A*L)<dyadicBallMaximal f x := hx.2
    unfold dyadicBallMaximal at hxHigh
    obtain ⟨j,hj⟩ := lt_iSup_iff.mp hxHigh
    let R : PositiveRadius := ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩
    change ENNReal.ofReal (A*L)<centeredBallAverageENN f x R at hj
    by_cases hLarge : r≤R.val
    · have Hlarge := dyadicBallAverage_large_radius_le_of_goodpoint f a x y r hr hy hx.1
        (ENNReal.ofReal L) hGood j hLarge
      have Hlevel : ENNReal.ofReal ((64 : ℝ)^n)*ENNReal.ofReal L≤ENNReal.ofReal (A*L) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ)≤64) n)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hA hL.le)
      exact False.elim ((not_lt_of_ge (Hlarge.trans Hlevel)) hj)
    · by_contra hBad
      have hMax : dyadicBallMaximal g x≤ENNReal.ofReal (A*L/4) := le_of_not_gt hBad
      have hNear : centeredBallAverageENN g x R≤ENNReal.ofReal (A*L/4) :=
        (le_iSup (fun k : ℤ=>centeredBallAverageENN g x
          ⟨(2 : ℝ)^k,zpow_pos (by norm_num) k⟩) j).trans hMax
      have H := average_le_near_add_constant f g hg a x r hx.1 R (le_of_not_ge hLarge) _ hLocal
      have Htotal : centeredBallAverageENN f x R≤ENNReal.ofReal (A*L) :=
        H.trans ((add_le_add (mul_le_mul_of_nonneg_left hNear zero_le) le_rfl).trans hNumeric)
      exact (not_lt_of_ge Htotal) hj
  refine ⟨hSub,?_⟩
  have Hweak := dyadicBallMaximal_weak_one g (A*L/4) hLevel
  have hCoefficient : (5 : ℝ)^n/(A*L/4)=4*(5 : ℝ)^n/(A*L) := by ring
  rw [hCoefficient] at Hweak
  exact (measure_mono hSub).trans Hweak

end StationaryHarmonicMaps.Analysis

end
