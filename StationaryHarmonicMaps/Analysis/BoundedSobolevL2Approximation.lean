module

public import StationaryHarmonicMaps.Analysis.BoundedMollification
public import StationaryHarmonicMaps.Analysis.BallBoundaryLayer
public import StationaryHarmonicMaps.Analysis.SobolevMollificationRate

/-!
# Actual uniform whole-ball approximation of bounded Sobolev sequences

The outer-ball indicator is used only as an L1 and L2 convolution input.
The actual value bound controls the original map and its averages on the
boundary layer. Interior weak-gradient estimates and the small actual
boundary volume give uniformly small whole-ball L2 errors.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem bounded_unitBall_indicator_data {n q : ℕ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖u x‖ ≤ B) :
    let F := (Metric.ball (0 : Domain n) 1).indicator u
    Integrable F volume ∧ MemLp F 2 volume ∧ (∀ᵐ x ∂volume, ‖F x‖ ≤ B) ∧
      (∫ x, ‖F x‖) ≤ B * volume.real (Metric.ball (0 : Domain n) 1) := by
  classical
  let F : Domain n → Ambient q := (Metric.ball (0 : Domain n) 1).indicator u
  have hFI : Integrable F volume := hu.integrable_unitBall.integrable_indicator measurableSet_ball
  have hF2 : MemLp F 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).mpr hu.2.1
  have hFbound : ∀ᵐ x ∂volume, ‖F x‖ ≤ B := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hbound] with x hx
    by_cases hxB : x ∈ Metric.ball (0 : Domain n) 1
    · exact (show F x = u x from indicator_of_mem hxB u) ▸ hx hxB
    · rw [show F x = 0 from indicator_of_notMem hxB u, norm_zero]
      exact hB
  have hnorm : (fun x => ‖F x‖) =
      (Metric.ball (0 : Domain n) 1).indicator (fun x => ‖u x‖) := by
    funext x
    by_cases hx : x ∈ Metric.ball (0 : Domain n) 1
    · simp only [F, indicator_of_mem hx]
    · simp only [F, indicator_of_notMem hx, norm_zero]
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  refine ⟨hFI, hF2, hFbound, ?_⟩
  change (∫ x, ‖F x‖) ≤ _
  rw [hnorm, integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫ _x in Metric.ball (0 : Domain n) 1, B :=
      integral_mono_ae hu.integrable_unitBall.norm (integrable_const _) hbound
    _ = _ := by rw [integral_const]; simp [measureReal_def, smul_eq_mul, mul_comm]

private theorem bounded_whole_ball_error_le {n q : ℕ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    {B : ℝ} (hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖u x‖ ≤ B)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (h : PositiveRadius) (hh : h.val ≤ 1 - r)
    (hmbound : ∀ x, ‖∫ y, fixedMollifierKernel n y •
      (Metric.ball (0 : Domain n) 1).indicator u (x - h.val • y)‖ ≤ B) :
    let m := fun x => ∫ y, fixedMollifierKernel n y •
      (Metric.ball (0 : Domain n) 1).indicator u (x - h.val • y)
    (∫ x in Metric.ball (0 : Domain n) 1, ‖m x - u x‖ ^ 2) ≤
      h.val ^ 2 * (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) +
        4 * B ^ 2 * volume.real (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r) := by
  dsimp only
  let m : Domain n → Ambient q := fun x => ∫ y, fixedMollifierKernel n y •
    (Metric.ball (0 : Domain n) 1).indicator u (x - h.val • y)
  obtain ⟨_hsmooth, hmGlobal, hinner⟩ := sobolev_mollification_L2_rate (0 : Domain n) hr hr1 hu h hh
  have hm2 : MemLp m 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    hmGlobal.mono_measure Measure.restrict_le_self
  have hErrorI : IntegrableOn (fun x => ‖m x - u x‖ ^ 2) (Metric.ball (0 : Domain n) 1) volume :=
    (hm2.sub hu.2.1).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  let D : Set (Domain n) := Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r
  have hDI : IntegrableOn (fun x => ‖m x - u x‖ ^ 2) D volume := hErrorI.mono_set sdiff_subset
  letI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (sdiff_subset : D ⊆ Metric.ball (0 : Domain n) 1)))
  have hBoundD : ∀ᵐ x ∂volume.restrict D, ‖u x‖ ≤ B :=
    hbound.filter_mono (ae_mono (Measure.restrict_mono_set volume
      (sdiff_subset : D ⊆ Metric.ball (0 : Domain n) 1)))
  have hDbound : (∫ x in D, ‖m x - u x‖ ^ 2) ≤ 4 * B ^ 2 * volume.real D := by
    calc
      _ ≤ ∫ _x in D, (4 * B ^ 2) := by
        apply integral_mono_ae hDI (integrable_const _)
        filter_upwards [hBoundD] with x hx
        have hn : ‖m x - u x‖ ≤ 2 * B :=
          (norm_sub_le _ _).trans (by linarith only [hmbound x, hx])
        have H := pow_le_pow_left₀ (norm_nonneg _) hn 2
        nlinarith only [H]
      _ = _ := by rw [integral_const]; simp [measureReal_def, smul_eq_mul, mul_comm]
  have hsplit := setIntegral_sdiff measurableSet_ball hErrorI (Metric.ball_subset_ball hr1.le)
  change (∫ x in D, ‖m x - u x‖ ^ 2) = _ at hsplit
  linarith only [hinner, hDbound, hsplit]

/-- AE value bounds and actual weak-gradient energy give uniform whole-ball smooth approximations. -/
theorem exists_bounded_sobolev_uniform_L2_approximation {n q : ℕ}
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (u k) (Du k))
    (B Mgrad : ℝ) (hB : 0 ≤ B) (hMgrad : 0 ≤ Mgrad)
    (hbound : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖u k x‖ ≤ B)
    (hgrad : ∀ k, (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du k x)) ≤ Mgrad)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ → Domain n → Ambient q) (L : ℝ), 0 ≤ L ∧
      (∀ k, ContDiff ℝ ∞ (m k)) ∧ (∀ k, MemLp (m k) 2 volume) ∧
      (∀ k x, ‖m k x‖ ≤ B) ∧
      (∀ k x y, dist (m k x) (m k y) ≤ L * dist x y) ∧
      ∀ k, (∫ x in Metric.ball (0 : Domain n) 1, ‖m k x - u k x‖ ^ 2) < ε ^ 2 := by
  obtain ⟨r, hr, hr1, hstrip⟩ := exists_inner_unitBall_scaled_boundary_lt n (4 * B ^ 2)
    (by positivity) (ε ^ 2 / 2) (by positivity)
  let t : ℝ := min (1 - r) (ε / (2 * Real.sqrt (Mgrad + 1)))
  have hroot : 0 < Real.sqrt (Mgrad + 1) := Real.sqrt_pos.mpr (by linarith)
  have ht : 0 < t := lt_min (sub_pos.mpr hr1) (div_pos hε (mul_pos (by norm_num) hroot))
  let h : PositiveRadius := ⟨t / 2, half_pos ht⟩
  have hhalf : h.val < t := by change t / 2 < t; linarith
  have hmargin : h.val ≤ 1 - r := hhalf.le.trans (min_le_left _ _)
  have hsmall : h.val < ε / (2 * Real.sqrt (Mgrad + 1)) := hhalf.trans_le (min_le_right _ _)
  have hprod : h.val * (2 * Real.sqrt (Mgrad + 1)) < ε :=
    (lt_div_iff₀ (mul_pos (by norm_num) hroot)).mp hsmall
  have hsquare : (h.val * (2 * Real.sqrt (Mgrad + 1))) ^ 2 < ε ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg h.property.le (by positivity)) hε.le).mpr hprod
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Mgrad + 1)] at hsquare
  have hscale : h.val ^ 2 * Mgrad < ε ^ 2 / 2 := by
    nlinarith only [hsquare, sq_nonneg h.val, hMgrad]
  let M : ℝ := B * volume.real (Metric.ball (0 : Domain n) 1)
  have hM : 0 ≤ M := mul_nonneg hB ENNReal.toReal_nonneg
  obtain ⟨L, hL, H⟩ := exists_bounded_fixed_mollification_bounds n h B M hB hM
  let m : ℕ → Domain n → Ambient q := fun k x => ∫ y, fixedMollifierKernel n y •
    (Metric.ball (0 : Domain n) 1).indicator (u k) (x - h.val • y)
  have Hk (k : ℕ) := by
    obtain ⟨hFI, hF2, hFbound, hFnorm⟩ := bounded_unitBall_indicator_data (hu k) hB (hbound k)
    exact H q _ hFI hF2 hFbound hFnorm
  refine ⟨m, L, hL, fun k => (Hk k).1, fun k => (Hk k).2.1,
    fun k => (Hk k).2.2.1, fun k => (Hk k).2.2.2, ?_⟩
  intro k
  have herror := bounded_whole_ball_error_le (hu k) (hbound k) hr hr1 h hmargin (Hk k).2.2.1
  have hmain : h.val ^ 2 * (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du k x)) ≤
      h.val ^ 2 * Mgrad := mul_le_mul_of_nonneg_left (hgrad k) (sq_nonneg _)
  linarith only [herror, hmain, hscale, hstrip]

end StationaryHarmonicMaps.Analysis

end
