module

public import HolderToCK.Analysis.HolderMollification
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Smooth compact approximations of globally Holder data -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology Pointwise

namespace HolderToCK

@[expose] noncomputable def compactDataMollification {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Domain n → E) (h : PositiveRadius) (x : Domain n) : E :=
  ∫ z, scaledMollifierKernel n h z • g (x - z)

theorem compactDataMollification_contDiff {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Domain n → E} (hg : Continuous g) (h : PositiveRadius) :
    ContDiff ℝ ∞ (compactDataMollification g h) := by
  change ContDiff ℝ ∞
    (scaledMollifierKernel n h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
  exact (scaledMollifierKernel_hasCompactSupport n h).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h)
    hg.locallyIntegrable

theorem compactDataMollification_hasCompactSupport {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Domain n → E} (hcg : HasCompactSupport g) (h : PositiveRadius) :
    HasCompactSupport (compactDataMollification g h) := by
  exact (scaledMollifierKernel_hasCompactSupport n h).convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hcg

theorem compactDataMollification_tsupport_subset {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Domain n → E} {R : ℝ}
    (hgR : tsupport g ⊆ Metric.closedBall (0 : Domain n) R) (h : PositiveRadius) :
    tsupport (compactDataMollification g h) ⊆
      Metric.closedBall (0 : Domain n) (R + h.val / 2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hx' := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (Domain n))) hx
  obtain ⟨z, hz, y, hy, rfl⟩ := hx'
  have hz' := scaledMollifierKernel_tsupport_subset_halfBall n h (subset_tsupport _ hz)
  have hy' := hgR (subset_tsupport _ hy)
  rw [Metric.mem_closedBall, dist_zero_right] at hz' hy' ⊢
  calc
    ‖z + y‖ ≤ ‖z‖ + ‖y‖ := norm_add_le _ _
    _ ≤ h.val / 2 + R := add_le_add hz' hy'
    _ = R + h.val / 2 := add_comm _ _

theorem compactDataMollification_integrable {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Domain n → E} (hg : Continuous g) (h : PositiveRadius) (x : Domain n) :
    Integrable (fun z => scaledMollifierKernel n h z • g (x - z)) volume :=
  ((scaledMollifierKernel_hasCompactSupport n h).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h).continuous
    hg.locallyIntegrable x).integrable

theorem compactDataMollification_holderBound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Domain n → E} {η H : ℝ} (hη : 0 < η) (_hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (h : PositiveRadius) :
    HolderBoundOn univ (compactDataMollification g h) η H := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  intro x _ y _
  rw [compactDataMollification, compactDataMollification,
    ← integral_sub (compactDataMollification_integrable hg h x)
      (compactDataMollification_integrable hg h y)]
  have hbound (z : Domain n) :
      ‖scaledMollifierKernel n h z • g (x - z) -
        scaledMollifierKernel n h z • g (y - z)‖ ≤
        scaledMollifierKernel n h z * (H * Real.rpow (dist x y) η) := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (scaledMollifierKernel_nonneg n h z)]
    apply mul_le_mul_of_nonneg_left _ (scaledMollifierKernel_nonneg n h z)
    simpa only [dist_sub_right] using hHolder (x - z) (mem_univ _) (y - z) (mem_univ _)
  calc
    _ ≤ ∫ z, scaledMollifierKernel n h z * (H * Real.rpow (dist x y) η) :=
      norm_integral_le_of_norm_le ((scaledMollifierKernel_integrable n h).mul_const _)
        (Eventually.of_forall hbound)
    _ = _ := by rw [integral_mul_const, scaledMollifierKernel_integral_one, one_mul]

theorem compactDataMollification_dist_le {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Domain n → E} {η H : ℝ} (hη : 0 < η) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (h : PositiveRadius) (x : Domain n) :
    dist (compactDataMollification g h x) (g x) ≤ H * Real.rpow h.val η := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hsupport : Function.support (scaledMollifierKernel n h) ⊆
      Metric.ball (0 : Domain n) h.val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall n h).trans
      (Metric.closedBall_subset_ball (by linarith only [h.property])))
  apply dist_convolution_le (mul_nonneg hH (Real.rpow_nonneg h.property.le _))
    hsupport (scaledMollifierKernel_nonneg n h) (scaledMollifierKernel_integral_one n h)
    hg.aestronglyMeasurable
  intro y hy
  rw [dist_eq_norm]
  exact (hHolder y (mem_univ _) x (mem_univ _)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hy.le hη.le) hH)

theorem compactDataMollification_tendstoUniformly {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Domain n → E} {η H : ℝ} (hη : 0 < η) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H)
    (h : ℕ → PositiveRadius) (hh : Tendsto (fun k => (h k).val) atTop (𝓝 0)) :
    TendstoUniformly (fun k => compactDataMollification g (h k)) g atTop := by
  have hAt : ContinuousAt (fun t : ℝ => H * Real.rpow t η) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hη.le))
  have herror : Tendsto (fun k => H * Real.rpow (h k).val η) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hη.ne', mul_zero] using
      hAt.tendsto.comp hh
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds hε)] with k hk x
  rw [dist_comm]
  exact (compactDataMollification_dist_le hη hH hHolder (h k) x).trans_lt hk

end HolderToCK
end
