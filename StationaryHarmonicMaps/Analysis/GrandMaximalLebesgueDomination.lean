module

public import StationaryHarmonicMaps.Analysis.CutoffAverageLebesgue

/-!
# Original L1 values are dominated by their actual smooth grand maximal field

Actual cutoff averages approach the original value at Lebesgue points.
The same original grand maximal field bounds every such average. Its
infinite values are retained; a real value is used only after actual
finiteness at the selected point has been proved.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original integrable scalar fields have their actual values bounded almost everywhere by the same literal smooth grand maximal field. -/
theorem exists_ae_value_le_smooth_grand_kernel_explicit (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ C = grandGoodPointCutoffMajorant n ∧ ∀ (f : Domain n → ℝ), Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      ∀ᵐ a ∂volume, ENNReal.ofReal |f a|≤ENNReal.ofReal C*J a := by
  obtain ⟨C,hC,hFormula,Hcut⟩ := exists_grand_good_point_cutoff_piece_majorant n
  refine ⟨C,hC,hFormula,?_⟩
  intro f hf J
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf.locallyIntegrable 1
  filter_upwards [hLeb] with a ha
  by_cases hTop : J a=(∞ : ℝ≥0∞)
  · have hC0 : ENNReal.ofReal C≠0 := (ENNReal.ofReal_pos.mpr hC).ne'
    rw [hTop,ENNReal.mul_top hC0]
    exact le_top
  · let L : ℝ := (J a).toReal
    have hL : 0≤L := ENNReal.toReal_nonneg
    have hGood : J a≤ENNReal.ofReal L := (ENNReal.ofReal_toReal hTop).symm.le
    let r := fun k : ℕ => 1/((k : ℝ)+1)
    have hr (k : ℕ) : 0<r k := by dsimp only [r];positivity
    have hChoices (k : ℕ) := Hcut f hf a a (r k) L (hr k) hL
      (by simp only [dist_self];positivity) hGood
    choose η hη hcη hsη hOne hBound hAverage _hBadI _hZero _hSupp using hChoices
    let c := fun k : ℕ => (∫ x,η k x*f x)/(∫ x,η k x)
    have hError (k : ℕ) : |c k-f a|≤(2 : ℝ)^n*
        (⨍ x in Metric.ball a (2*r k),|f x-f a|) :=
      (cutoff_average_error_le_ball_average f hf a (hr k) (η k) (hη k) (hcη k)
        (hsη k) (hOne k) (hBound k) (f a)).2
    have hRadius : Tendsto (fun k => 2*r k) atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,Eventually.of_forall fun k=>mul_pos (by norm_num) (hr k)⟩
      simpa only [r,mul_zero] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
    have hCenter : ∀ᶠ k : ℕ in atTop, a∈Metric.closedBall a (1*(2*r k)) :=
      Eventually.of_forall fun k=>by
        simp only [Metric.mem_closedBall,dist_self,one_mul]
        exact (mul_pos (by norm_num : (0 : ℝ)<2) (hr k)).le
    have hMeanClosed := ha (fun _k : ℕ=>a) (fun k=>2*r k) hRadius hCenter
    have hMeansEq (k : ℕ) : (⨍ x in Metric.ball a (2*r k),|f x-f a|)=
        ⨍ x in Metric.closedBall a (2*r k),‖f x-f a‖ := by
      rw [setAverage_congr (ball_ae_eq_closedBall a (mul_pos (by norm_num) (hr k)))]
      simp only [Real.norm_eq_abs]
    have hMean : Tendsto (fun k=>⨍ x in Metric.ball a (2*r k),|f x-f a|) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hMeansEq] using hMeanClosed
    have hErrorLimit : Tendsto (fun k=>|c k-f a|) atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun _=>abs_nonneg _) hError (by
        simpa only [mul_zero] using hMean.const_mul ((2 : ℝ)^n))
    have hLimit : Tendsto c atTop (𝓝 (f a)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hErrorLimit)
    have hValue : |f a|≤C*L := le_of_tendsto hLimit.abs (Eventually.of_forall hAverage)
    calc
      _ ≤ ENNReal.ofReal (C*L) := ENNReal.ofReal_le_ofReal hValue
      _ = _ := by rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_toReal hTop]

theorem exists_ae_value_le_smooth_grand_kernel (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (f : Domain n → ℝ), Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      ∀ᵐ a ∂volume, ENNReal.ofReal |f a|≤ENNReal.ofReal C*J a := by
  obtain ⟨C, hC, _hFormula, H⟩ := exists_ae_value_le_smooth_grand_kernel_explicit n
  exact ⟨C, hC, H⟩

end StationaryHarmonicMaps.Analysis

end
