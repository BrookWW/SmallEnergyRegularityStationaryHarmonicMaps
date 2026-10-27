module

public import StationaryHarmonicMaps.Analysis.SobolevTranslationBound
public import StationaryHarmonicMaps.Analysis.MollificationErrorIntegrability

/-!
# A uniform interior L2 rate for actual Sobolev mollification

The outer-ball indicator supplies the globally integrable convolution input.
Its values agree with the original map at every sampled interior point.
Jensen, Fubini and the actual weak-gradient translation estimate give the
rate h² times the outer-ball gradient energy.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The literal smooth convolution has actual global L2 data and the uniform interior error rate. -/
theorem sobolev_mollification_L2_rate {n q : ℕ} (a : Domain n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (h : PositiveRadius) (hh : h.val ≤ R - r) :
    let F : Domain n → Ambient q := (Metric.ball a R).indicator u
    let m := fun x => ∫ y, fixedMollifierKernel n y • F (x - h.val • y)
    ContDiff ℝ ∞ m ∧ MemLp m 2 volume ∧
      (∫ x in Metric.ball a r, ‖m x - u x‖ ^ 2) ≤
        h.val ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  classical
  dsimp only
  let F : Domain n → Ambient q := (Metric.ball a R).indicator u
  have hFI : Integrable F volume := hu.integrable_ball.integrable_indicator measurableSet_ball
  have hF2 : MemLp F 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).mpr hu.2.1
  refine ⟨fixedKernelAverage_contDiff hFI h, fixedKernelAverage_memLp hFI hF2 h, ?_⟩
  have H := fixed_kernel_average_restricted_error_sq_le hFI hF2 h (Metric.ball a r)
  have hpoint (y : Domain n) :
      fixedMollifierKernel n y * (∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2) ≤
      fixedMollifierKernel n y * (h.val ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x)) := by
    by_cases hyzero : fixedMollifierKernel n y = 0
    · simp only [hyzero, zero_mul, le_refl]
    · have hysupport : y ∈ tsupport (fixedMollifierKernel n) := subset_tsupport _ hyzero
      have hyhalf := fixedMollifierKernel_tsupport_subset_halfBall n hysupport
      have hynormHalf : ‖y‖ ≤ (1 / 2 : ℝ) := by
        simpa only [mem_closedBall, dist_zero_right] using hyhalf
      have hynorm : ‖y‖ ≤ 1 := hynormHalf.trans (by norm_num)
      let δ : Domain n := -(h.val • y)
      have hδ : ‖δ‖ ≤ h.val := by
        dsimp only [δ]
        rw [norm_neg, norm_smul, Real.norm_of_nonneg h.property.le]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hynorm h.property.le
      have hδmargin : ‖δ‖ ≤ R - r := hδ.trans hh
      have heq : (∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2) =
          ∫ x in Metric.ball a r, ‖u (x + δ) - u x‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        have hxB : x ∈ Metric.ball a R := Metric.ball_subset_ball hrR.le hx
        have hxδ : x - h.val • y ∈ Metric.ball a R := by
          simpa only [δ, sub_eq_add_neg] using add_mem_ball_of_norm_le_margin hx hδmargin
        have hFx : F x = u x := indicator_of_mem hxB u
        have hFshift : F (x - h.val • y) = u (x - h.val • y) := indicator_of_mem hxδ u
        dsimp only
        rw [hFx, hFshift]
        rfl
      have hbound : (∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2) ≤
          h.val ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
        calc
          _ = ∫ x in Metric.ball a r, ‖u (x + δ) - u x‖ ^ 2 := heq
          _ ≤ ‖δ‖ ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) :=
            integral_translation_sub_sq_le a hr hrR hu δ hδmargin
          _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hδ 2)
            (integral_nonneg fun x => hsNormSq_nonneg (Du x))
      exact mul_le_mul_of_nonneg_left hbound (fixedMollifierKernel_nonneg n y)
  calc
    _ = ∫ x in Metric.ball a r,
        ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      dsimp only
      change ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - u x‖ ^ 2 = _
      rw [show F x = u x from indicator_of_mem (Metric.ball_subset_ball hrR.le hx) u]
    _ ≤ ∫ y, fixedMollifierKernel n y *
        ∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2 := H.2
    _ ≤ ∫ y, fixedMollifierKernel n y *
        (h.val ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x)) :=
      integral_mono H.1 ((fixedMollifierKernel_integrable n).mul_const _) hpoint
    _ = _ := by rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]

end StationaryHarmonicMaps.Analysis

end
