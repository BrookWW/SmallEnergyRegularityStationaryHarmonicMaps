module

public import HolderToCK.Foundation.WeakPoisson
public import HolderToCK.Analysis.ConvolutionDerivatives
public import HarmonicMaps.Analysis.MollificationEnergy

/-! # Interior mollification of the signed weak Poisson equation

The translated kernel is a genuine compactly supported test. Its negative
coordinate derivative cancels the negative sign in the weak equation. The
same input gradient and forcing are used throughout.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

noncomputable section

theorem kernelConvolution_laplacian_gradient {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {W : Set (Domain n)} (hW : IsOpen W)
    (hSample : ∀ z ∈ W, ∀ y ∈ tsupport χ, z - y ∈ Ω.val)
    {x : Domain n} (hx : x ∈ W) :
    Laplacian.laplacian (fun z => ∫ y, χ y • zeroExtensionOn Ω u (z - y)) x =
      ∑ i : Fin n, ∫ z in Ω.val,
        fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • Du z i := by
  have hInt := hu.integrable_domain hΩ
  rw [laplacian_eq_sum_coordinateDerivatives _ (kernelConvolution_contDiff Ω u hInt hχ hcχ)]
  apply Finset.sum_congr rfl
  intro i _
  have hlocal : (fun z => fderiv ℝ (fun z => ∫ y, χ y •
      zeroExtensionOn Ω u (z - y)) z (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => ∫ y, χ y • zeroExtensionOn Ω (fun z => Du z i) (z - y)) := by
    filter_upwards [hW.mem_nhds hx] with z hz
    exact hu.1.kernelConvolution_coordinateDerivative hInt hχ hcχ z (hSample z hz) i
  rw [hlocal.fderiv_eq, kernelConvolution_fderiv Ω _
    (hu.column_integrable_domain hΩ i) hχ hcχ]
  simp only [zeroExtensionOn, ← indicator_smul]
  exact integral_indicator Ω.property.measurableSet

theorem WeakPoissonOn.kernelConvolution_laplacian {n q : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hu : MemW12 Ω u Du)
    (hΩ : volume Ω.val ≠ ⊤) (hF : IntegrableOn F Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {W : Set (Domain n)} (hW : IsOpen W)
    (hSample : ∀ z ∈ W, ∀ y ∈ tsupport χ, z - y ∈ Ω.val)
    {x : Domain n} (hx : x ∈ W) :
    Laplacian.laplacian (fun z => ∫ y, χ y • zeroExtensionOn Ω u (z - y)) x =
      ∫ z in Ω.val, χ (x - z) • F z := by
  have hI : ∀ i : Fin n, IntegrableOn (fun z =>
      fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • Du z i) Ω.val := by
    intro i
    have hdc : Continuous (fun z => fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) :=
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    have hcc : HasCompactSupport (fun z => fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) :=
      (hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)).comp_homeomorph (Homeomorph.subLeft x)
    exact (hu.column_integrable_domain hΩ i).smul_of_top_right
      (hdc.memLp_top_of_hasCompactSupport hcc _)
  have hsumI := integrable_finsetSum Finset.univ (fun i _ => hI i)
  have hψ : ContDiff ℝ ∞ (translatedKernelTest χ x) := translatedKernelTest_contDiff hχ x
  have hcψ := translatedKernelTest_hasCompactSupport hcχ x
  have hsψ := translatedKernelTest_tsupport_subset Ω x (hSample x hx)
  have hFI : IntegrableOn (fun z => χ (x - z) • F z) Ω.val :=
    hF.smul_of_top_right (hψ.continuous.memLp_top_of_hasCompactSupport hcψ _)
  rw [kernelConvolution_laplacian_gradient Ω hu hΩ hχ hcχ hW hSample hx,
    ← integral_finsetSum _ (fun i _ => hI i)]
  apply ext_inner_left ℝ
  intro v
  let ψ : Domain n → Ambient q := fun z => translatedKernelTest χ x z • v
  have hψv : ContDiff ℝ ∞ ψ := hψ.smul contDiff_const
  have hcψv : HasCompactSupport ψ := hcψ.smul_right
  have hsψv : tsupport ψ ⊆ Ω.val := (tsupport_smul_subset_left _ _).trans hsψ
  have hdψ : ∀ z i, fderiv ℝ ψ z (EuclideanSpace.single i 1) =
      -(fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) • v := by
    intro z i
    rw [fderiv_smul_const (hψ.differentiable (by simp)).differentiableAt v]
    simp only [ContinuousLinearMap.smulRight_apply]
    exact congrArg (fun a : ℝ => a • v) (translatedKernelTest_coordinateDerivative hχ x z i)
  have htest : ∀ z, (∑ i : Fin n,
      inner ℝ (Du z i) (fderiv ℝ ψ z (EuclideanSpace.single i 1))) =
      -inner ℝ v (∑ i : Fin n,
        fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • Du z i) := by
    intro z
    simp only [hdψ, inner_smul_right, inner_sum, inner_smul_right, neg_mul,
      Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
  have htestF : ∀ z, inner ℝ (F z) (ψ z) = inner ℝ v (χ (x - z) • F z) := by
    intro z
    simp only [ψ, translatedKernelTest, inner_smul_right, real_inner_comm]
  have heq := (hEq.2 ψ hψv hcψv hsψv).2.2
  simp_rw [htest, htestF] at heq
  rw [integral_neg, integral_inner hsumI v, integral_inner hFI v] at heq
  exact neg_injective heq

/-- The quadratic domination and actual L2 columns give global L1 forcing. -/
theorem WeakPoissonOn.integrable_of_quadratic_bound {n q : ℕ} {Ω : OpenDomain n}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hu : MemW12 Ω u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ K * hsNormSq (Du x)) :
    IntegrableOn F Ω.val := by
  exact ((integrable_hsNormSq_of_memLp_columns hu.2.2).const_mul K).mono'
    hEq.1.aestronglyMeasurable hBound

/-- On every interior sampling ball the smooth convolution solves Δu_h = F_h. -/
theorem WeakPoissonOn.mollification_laplacian_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u F : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain a R) Du F)
    (hu : MemW12 (ballDomain a R) u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖F x‖ ≤ K * hsNormSq (Du x))
    (h : PositiveRadius) (hMargin : r + h.val / 2 ≤ R) :
    ContDiff ℝ ∞ (euclideanMollification (ballDomain a R) u hu.integrable_ball h) ∧
    ∀ x ∈ Metric.ball a r,
      Laplacian.laplacian (euclideanMollification (ballDomain a R) u hu.integrable_ball h) x =
        ∫ y, scaledMollifierKernel n h y • F (x - y) := by
  have hF := hEq.integrable_of_quadratic_bound hu K hBound
  have hSample : ∀ x ∈ Metric.ball a r,
      ∀ y ∈ tsupport (scaledMollifierKernel n h), x - y ∈ Metric.ball a R := by
    intro x hx
    apply scaledMollifierKernel_sampling_ball h a x R
    have hxr : dist x a < r := hx
    linarith only [hxr, hMargin]
  refine ⟨euclideanMollification_contDiff _ u hu.integrable_ball h, ?_⟩
  intro x hx
  change Laplacian.laplacian (fun z => ∫ y, scaledMollifierKernel n h y •
    zeroExtensionOn (ballDomain a R) u (z - y)) x = _
  rw [hEq.kernelConvolution_laplacian _ hu measure_ball_ne_top hF
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
    Metric.isOpen_ball hSample hx, ← kernelConvolution_eq_setIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : scaledMollifierKernel n h y = 0
    · simp only [hy, zero_smul]
    · have hxy := hSample x hx y (subset_tsupport _ (Function.mem_support.mpr hy))
      have hxyΩ : x - y ∈ (ballDomain a R).val := hxy
      simp only [zeroExtensionOn, indicator_of_mem hxyΩ]

/-- The literal fixed-kernel averages satisfy the same signed Poisson equation. -/
theorem WeakPoissonOn.sourceMollification_laplacian {n q : ℕ}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain (0 : Domain n) 1) Du F)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖F x‖ ≤ K * hsNormSq (Du x))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    Laplacian.laplacian (fun z : Domain n =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (z - h.val • y)) x =
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • F (x - h.val • y) := by
  have hF := hEq.integrable_of_quadratic_bound hu K hBound
  have hlocal : (fun z : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (z - h.val • y)) =ᶠ[𝓝 x]
      zeroExtendedMollification u hu.integrable_unitBall h := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact sourceMollification_eq_zeroExtended u hu.integrable_unitBall h hh z hz
  rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
  change Laplacian.laplacian (fun z => ∫ y, scaledMollifierKernel n h y •
    zeroExtensionOn (ballDomain (0 : Domain n) 1) u (z - y)) x = _
  rw [hEq.kernelConvolution_laplacian _ hu measure_ball_ne_top hF
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
    Metric.isOpen_ball (fun z hz => scaledMollifierKernel_sampling_unitBall h hh hz) hx]
  calc
    _ = ∫ z, scaledMollifierKernel n h (x - z) • unitBallZeroExtension F z := by
      simp only [unitBallZeroExtension, ← indicator_smul]
      exact (integral_indicator measurableSet_ball).symm
    _ = ∫ z, scaledMollifierKernel n h z • unitBallZeroExtension F (x - z) := by
      rw [← integral_sub_left_eq_self
        (fun z => scaledMollifierKernel n h z • unitBallZeroExtension F (x - z)) volume x]
      simp only [sub_sub_cancel]
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • F (x - h.val • y) :=
      (sourceMollification_eq_zeroExtended F hF h hh x hx).symm

end
end HolderToCK
end
