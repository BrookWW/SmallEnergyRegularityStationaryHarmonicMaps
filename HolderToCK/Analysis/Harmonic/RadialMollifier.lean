module

public import HolderToCK.Analysis.Harmonic.RadialMean
public import HolderToCK.Analysis.MollificationForcingBound

/-! # Exact radial mollification of smooth harmonic maps

The scaled fixed kernel has an explicit radial profile. Spherical means and
radial integration identify its interior convolution with the original map.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

noncomputable section

@[expose] def scaledMollifierProfile (n : ℕ) (h : PositiveRadius) (t : ℝ) : ℝ :=
  (h.val ^ n)⁻¹ * (Real.smoothTransition (1 - 4 * (h.val⁻¹ * t) ^ 2) /
    ∫ y, rawMollifierKernel n y)

theorem scaledMollifierProfile_continuous (n : ℕ) (h : PositiveRadius) :
    Continuous (scaledMollifierProfile n h) :=
  continuous_const.mul ((Real.smoothTransition.continuous.comp
    (continuous_const.sub (continuous_const.mul
      ((continuous_const.mul continuous_id).pow 2)))).div_const _)

theorem scaledMollifierKernel_eq_profile_norm (n : ℕ) (h : PositiveRadius)
    (z : Domain n) :
    scaledMollifierKernel n h z = scaledMollifierProfile n h ‖z‖ := by
  simp only [scaledMollifierKernel, fixedMollifierKernel, rawMollifierKernel,
    scaledMollifierProfile, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h.property.le)]

theorem scaledMollifierProfile_zero (n : ℕ) (h : PositiveRadius)
    {t : ℝ} (ht : h.val ≤ t) : scaledMollifierProfile n h t = 0 := by
  have hratio : 1 ≤ h.val⁻¹ * t := by
    rw [← div_eq_inv_mul, le_div_iff₀ h.property, one_mul]
    exact ht
  have hsmooth : Real.smoothTransition (1 - 4 * (h.val⁻¹ * t) ^ 2) = 0 :=
    Real.smoothTransition.zero_iff_nonpos.mpr (by nlinarith only [hratio])
  rw [scaledMollifierProfile, hsmooth, zero_div, mul_zero]

theorem scaledMollifier_integral_eq_of_sphereMean {n q : ℕ} (hn : 0 < n)
    (a : Domain n) (h : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContinuousOn f (Metric.closedBall a h.val))
    (hmean : ∀ r ∈ Ioo (0 : ℝ) h.val,
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • f a) :
    (∫ z, scaledMollifierKernel n h z • f (a - z)) = f a := by
  simp_rw [scaledMollifierKernel_eq_profile_norm]
  rw [radial_kernel_convolution_eq_of_sphereMean hn a h f hf
    (scaledMollifierProfile n h) (scaledMollifierProfile_continuous n h)
    (fun _ ht => scaledMollifierProfile_zero n h ht) hmean]
  simp_rw [← scaledMollifierKernel_eq_profile_norm]
  rw [scaledMollifierKernel_integral_one, one_smul]

theorem harmonic_scaledMollifier_integral_eq {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (h : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall a h.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ U, Laplacian.laplacian f x = 0) :
    (∫ z, scaledMollifierKernel n h z • f (a - z)) = f a := by
  apply scaledMollifier_integral_eq_of_sphereMean (by omega : 0 < n) a h f
    (hf.continuousOn.mono hclosed)
  intro r hr
  have hsmall : Metric.closedBall a r ⊆ U :=
    (Metric.closedBall_subset_closedBall hr.2.le).trans hclosed
  exact harmonic_sphere_integral_eq hn a ⟨r, hr.1⟩ U hU hsmall f hf
    (fun x hx => hharm x (hsmall (Metric.ball_subset_closedBall hx)))


theorem euclideanMollification_eq_integral_of_ball_subset {n q : ℕ}
    (Ω : OpenDomain n) (f : Domain n → Ambient q) (hfi : IntegrableOn f Ω.val)
    (h : PositiveRadius) (a : Domain n) (hSample : Metric.ball a h.val ⊆ Ω.val) :
    euclideanMollification Ω f hfi h a =
      ∫ z, scaledMollifierKernel n h z • f (a - z) := by
  unfold euclideanMollification
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : scaledMollifierKernel n h z = 0
  · rw [hz, zero_smul, zero_smul]
  · have hnorm : ‖z‖ ≤ h.val / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        scaledMollifierKernel_tsupport_subset_halfBall n h
          (subset_tsupport _ (Function.mem_support.mpr hz))
    have hmem : a - z ∈ Ω.val := by
      apply hSample
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hnorm.trans_lt (by linarith only [h.property])
    rw [zeroExtensionOn, indicator_of_mem hmem]


theorem euclideanMollification_eq_of_sphereMean {n q : ℕ} (hn : 0 < n)
    (Ω : OpenDomain n) (a : Domain n) (h : PositiveRadius)
    (f : Domain n → Ambient q) (hfi : IntegrableOn f Ω.val)
    (hSample : Metric.ball a h.val ⊆ Ω.val)
    (hf : ContinuousOn f (Metric.closedBall a h.val))
    (hmean : ∀ r ∈ Ioo (0 : ℝ) h.val,
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • f a) :
    euclideanMollification Ω f hfi h a = f a := by
  rw [euclideanMollification_eq_integral_of_ball_subset Ω f hfi h a hSample]
  exact scaledMollifier_integral_eq_of_sphereMean hn a h f hf hmean

end
end HolderToCK
end
