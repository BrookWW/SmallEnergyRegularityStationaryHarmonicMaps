module

public import HolderToCK.Analysis.HolderMollification
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-! # Uniform interior mollification of continuous data

Continuity on a compact containing ball gives uniform convergence on every
strictly smaller closed ball. The same domain zero extension and normalized
kernel are used; only samples in the original domain enter the estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

theorem tendsto_setIntegral_of_uniformlyOn_compact
    {X E : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) {K : Set X} (hK : IsCompact K) (hμ : μ K ≠ ⊤)
    {f : X → E} {F : ℕ → X → E} (hf : ContinuousOn f K)
    (hF : ∀ k, ContinuousOn (F k) K) (hlim : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun k => ∫ x in K, F k x ∂μ) atTop (𝓝 (∫ x in K, f x ∂μ)) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm
  letI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hμ
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C + 1)
  · exact Eventually.of_forall fun k => (hF k).aestronglyMeasurable hK.measurableSet
  · have hbound : ∀ᶠ k in atTop, ∀ x ∈ K, ‖F k x‖ ≤ C + 1 :=
      (uniformContinuous_norm.comp_tendstoUniformlyOn hlim).eventually_forall_le
        (by linarith only : C < C + 1) (fun x hx => hC ⟨x, hx, rfl⟩)
    filter_upwards [hbound] with k hk
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hk x hx
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hlim.tendsto_at hx

theorem euclideanMollification_tendstoUniformlyOn_closedBall_of_continuous
    {n q : ℕ} (Ω : OpenDomain n) (u : Domain n → Ambient q)
    (hu : IntegrableOn u Ω.val) (a : Domain n) {r R : ℝ} (hrR : r < R)
    (hclosed : Metric.closedBall a R ⊆ Ω.val)
    (hcont : ContinuousOn u (Metric.closedBall a R))
    (h : ℕ → PositiveRadius) (hh : Tendsto (fun k => (h k).val) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun k => euclideanMollification Ω u hu (h k)) u atTop
      (Metric.closedBall a r) := by
  have hUC := (isCompact_closedBall a R).uniformContinuousOn_of_continuous hcont
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδdist⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ k in atTop, (h k).val < min δ (R - r) :=
    hh.eventually (gt_mem_nhds (lt_min hδ (sub_pos.mpr hrR)))
  filter_upwards [hsmall] with k hk x hx
  have hxR : x ∈ Metric.closedBall a R :=
    (Metric.closedBall_subset_closedBall hrR.le) hx
  have hsample : ∀ y ∈ Metric.ball x (h k).val, y ∈ Metric.closedBall a R := by
    intro y hy
    have hyx : dist y x < (h k).val := hy
    have hxa : dist x a ≤ r := hx
    change dist y a ≤ R
    exact (dist_triangle y x a).trans (by linarith only [hyx, hxa, (lt_min_iff.mp hk).2])
  have hsupport : Function.support (scaledMollifierKernel n (h k)) ⊆
      Metric.ball (0 : Domain n) (h k).val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall n (h k)).trans
      (Metric.closedBall_subset_ball (by linarith only [(h k).property])))
  have hbound : ∀ y ∈ Metric.ball x (h k).val,
      dist (zeroExtensionOn Ω u y) (u x) ≤ ε / 2 := by
    intro y hy
    rw [zeroExtensionOn, indicator_of_mem (hclosed (hsample y hy))]
    apply le_of_lt
    apply hδdist y (hsample y hy) x hxR
    exact (show dist y x < (h k).val from hy).trans (lt_min_iff.mp hk).1
  have herror := dist_convolution_le (half_pos hε).le hsupport
    (scaledMollifierKernel_nonneg n (h k)) (scaledMollifierKernel_integral_one n (h k))
    (zeroExtensionOn_integrable Ω u hu).aestronglyMeasurable hbound
  rw [dist_comm]
  exact herror.trans_lt (half_lt_self hε)

end HolderToCK
end
