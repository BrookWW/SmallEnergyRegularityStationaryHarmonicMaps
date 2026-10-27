module

public import HolderToCK.Analysis.HolderMollification
public import HolderToCK.Analysis.GradientLinearAlgebra

/-! # Uniform convergence of the actual convolution derivative

Weak-gradient convolution commutation identifies every column. The native
Hilbert--Schmidt to operator-norm estimate combines their Holder error bounds
into uniform convergence of the full continuous linear derivative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem MemW12.holderMollification_fderiv_tendstoUniformlyOn {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {β H : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (hHolder : ∀ i : Fin n, HolderBoundOn Ω.val (fun x => Du x i) β H)
    (K : Set (Domain n)) {ρ : ℝ} (hρ : 0 < ρ)
    (hMargin : ∀ x ∈ K, Metric.ball x ρ ⊆ Ω.val)
    (h : ℕ → PositiveRadius) (hh : Tendsto (fun k => (h k).val) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun k => fderiv ℝ (euclideanMollification Ω u (hu.integrable_domain hΩ) (h k)))
      (fun x => ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (Du x i))
      atTop K := by
  have hAt : ContinuousAt (fun t : ℝ => (Real.sqrt (n : ℝ) * H) * Real.rpow t β) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hβ.le))
  have herror : Tendsto (fun k => (Real.sqrt (n : ℝ) * H) * Real.rpow (h k).val β)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hβ.ne', mul_zero] using
      hAt.tendsto.comp hh
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hh.eventually (gt_mem_nhds hρ), herror.eventually (gt_mem_nhds hε)] with k hk he
  intro x hx
  have hSample : Metric.ball x (h k).val ⊆ Ω.val :=
    (Metric.ball_subset_ball hk.le).trans (hMargin x hx)
  have hSampleKernel : ∀ y ∈ tsupport (scaledMollifierKernel n (h k)), x - y ∈ Ω.val := by
    intro y hy
    apply hSample
    have hyN : ‖y‖ ≤ (h k).val / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        scaledMollifierKernel_tsupport_subset_halfBall n (h k) hy
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hyN.trans_lt (by linarith only [(h k).property])
  have hcolEq (i : Fin n) :
      fderiv ℝ (euclideanMollification Ω u (hu.integrable_domain hΩ) (h k)) x
        (EuclideanSpace.single i 1) =
      euclideanMollification Ω (fun z => Du z i) (hu.column_integrable_domain hΩ i) (h k) x :=
    hu.1.kernelConvolution_coordinateDerivative (hu.integrable_domain hΩ)
      (scaledMollifierKernel_contDiff n (h k)) (scaledMollifierKernel_hasCompactSupport n (h k))
      x hSampleKernel i
  let T : Domain n →L[ℝ] Ambient q :=
    ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (Du x i)
  let L : Domain n →L[ℝ] Ambient q :=
    fderiv ℝ (euclideanMollification Ω u (hu.integrable_domain hΩ) (h k)) x - T
  have hcolBound (i : Fin n) : ‖L (EuclideanSpace.single i 1)‖ ≤ H * Real.rpow (h k).val β := by
    dsimp only [L, T]
    rw [sub_apply, columnLinearMap_single, hcolEq]
    simpa only [dist_eq_norm] using
      euclideanMollification_dist_le_of_holder Ω (fun z => Du z i)
        (hu.column_integrable_domain hΩ i) hβ.le hH (hHolder i) (h k) x hSample
  have hM : 0 ≤ H * Real.rpow (h k).val β :=
    mul_nonneg hH (Real.rpow_nonneg (h k).property.le _)
  have hbound := norm_linearMap_le_of_columns_bound L hM hcolBound
  rw [dist_eq_norm, norm_sub_rev]
  exact hbound.trans_lt (by simpa only [mul_assoc] using he)

end HolderToCK
end
