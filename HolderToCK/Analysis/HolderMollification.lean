module

public import HolderToCK.Foundation.HolderContinuity
public import HolderToCK.Analysis.MollificationForcingBound
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Uniform mollification of the same Holder representative

The positive unit-mass kernel preserves the input map at vanishing scale with
the explicit error `H * h^alpha`. The support and domain margins are stated
geometrically; no global regularity of the zero extension is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

theorem euclideanMollification_dist_le_of_holder {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hHolder : HolderBoundOn Ω.val u α H)
    (h : PositiveRadius) (x : Domain n) (hSample : Metric.ball x h.val ⊆ Ω.val) :
    dist (euclideanMollification Ω u hu h x) (u x) ≤ H * Real.rpow h.val α := by
  have hx : x ∈ Ω.val := hSample (Metric.mem_ball_self h.property)
  have hsupport : Function.support (scaledMollifierKernel n h) ⊆
      Metric.ball (0 : Domain n) h.val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall n h).trans
      (Metric.closedBall_subset_ball (by linarith only [h.property])))
  have hbound : ∀ y ∈ Metric.ball x h.val,
      dist (zeroExtensionOn Ω u y) (u x) ≤ H * Real.rpow h.val α := by
    intro y hy
    rw [zeroExtensionOn, indicator_of_mem (hSample hy), dist_eq_norm]
    exact (hHolder y (hSample hy) x hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (dist_nonneg : 0 ≤ dist y x) hy.le hα) hH)
  exact dist_convolution_le (mul_nonneg hH (Real.rpow_nonneg h.property.le _)) hsupport
    (scaledMollifierKernel_nonneg n h) (scaledMollifierKernel_integral_one n h)
    (zeroExtensionOn_integrable Ω u hu).aestronglyMeasurable hbound

theorem euclideanMollification_dist_le_on_closedBall {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hHolder : HolderBoundOn Ω.val u α H)
    (a : Domain n) (r : ℝ) (h : PositiveRadius)
    (hMargin : Metric.ball a (r + h.val) ⊆ Ω.val) :
    ∀ x ∈ Metric.closedBall a r,
      dist (euclideanMollification Ω u hu h x) (u x) ≤ H * Real.rpow h.val α := by
  intro x hx
  apply euclideanMollification_dist_le_of_holder Ω u hu hα hH hHolder h x
  intro y hy
  apply hMargin
  have hxa : dist x a ≤ r := hx
  have hyx : dist y x < h.val := hy
  change dist y a < r + h.val
  exact lt_of_le_of_lt (dist_triangle y x a) (by linarith only [hxa, hyx])

theorem euclideanMollification_tendstoUniformlyOn_of_holder {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {α H : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (hHolder : HolderBoundOn Ω.val u α H)
    (K : Set (Domain n)) {ρ : ℝ} (hρ : 0 < ρ)
    (hMargin : ∀ x ∈ K, Metric.ball x ρ ⊆ Ω.val)
    (h : ℕ → PositiveRadius) (hh : Tendsto (fun k => (h k).val) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun k => euclideanMollification Ω u hu (h k)) u atTop K := by
  have hAt : ContinuousAt (fun t : ℝ => H * Real.rpow t α) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hα.le))
  have herror : Tendsto (fun k => H * Real.rpow (h k).val α) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hα.ne', mul_zero] using
      hAt.tendsto.comp hh
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hh.eventually (gt_mem_nhds hρ), herror.eventually (gt_mem_nhds hε)] with k hk he
  intro x hx
  have hSample : Metric.ball x (h k).val ⊆ Ω.val :=
    (Metric.ball_subset_ball hk.le).trans (hMargin x hx)
  rw [dist_comm]
  exact (euclideanMollification_dist_le_of_holder Ω u hu hα.le hH hHolder (h k) x hSample).trans_lt he

end HolderToCK
end
