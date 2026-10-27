module

public import HolderToCK.Analysis.WeakPoissonMollification
public import HarmonicMaps.Analysis.MollificationChangeVariables

/-! # Local L1 bounds for mollified forcing

A nonnegative unit-mass kernel is an L1 contraction. On a ball, zero extension
from the enlarged sampling ball gives the bound by its original forcing.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff Convolution

namespace HolderToCK

noncomputable section

theorem kernelConvolution_norm_integral_le {n q : ℕ} (Ω : OpenDomain n)
    (F : Domain n → Ambient q) (hF : IntegrableOn F Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hNonneg : ∀ y, 0 ≤ χ y) (hMass : (∫ y, χ y) = 1) :
    Integrable (fun x => ‖∫ y, χ y • zeroExtensionOn Ω F (x - y)‖) volume ∧
    (∫ x, ‖∫ y, χ y • zeroExtensionOn Ω F (x - y)‖) ≤
      ∫ z in Ω.val, ‖F z‖ := by
  have hχInt : Integrable χ volume := hχ.continuous.integrable_of_hasCompactSupport hcχ
  have hzero := zeroExtensionOn_integrable Ω F hF
  have hconv := hχInt.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hzero
  have hnorm := hχInt.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hzero.norm
  refine ⟨hconv.norm, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, χ y * ‖zeroExtensionOn Ω F (x - y)‖ := by
      apply integral_mono hconv.norm hnorm
      intro x
      change ‖∫ y, χ y • zeroExtensionOn Ω F (x - y)‖ ≤
        ∫ y, χ y * ‖zeroExtensionOn Ω F (x - y)‖
      simpa only [norm_smul, Real.norm_of_nonneg (hNonneg _)] using
        norm_integral_le_integral_norm (fun y => χ y • zeroExtensionOn Ω F (x - y))
    _ = (∫ y, χ y) * ∫ z, ‖zeroExtensionOn Ω F z‖ :=
      integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hχInt hzero.norm
    _ = ∫ z, ‖zeroExtensionOn Ω F z‖ := by rw [hMass, one_mul]
    _ = ∫ z in Ω.val, ‖F z‖ := by
      have heq : (fun z => ‖zeroExtensionOn Ω F z‖) = Ω.val.indicator (fun z => ‖F z‖) := by
        funext z
        by_cases hz : z ∈ Ω.val
        · simp only [zeroExtensionOn, indicator_of_mem hz]
        · simp only [zeroExtensionOn, indicator_of_notMem hz, norm_zero]
      rw [heq, integral_indicator Ω.property.measurableSet]

theorem scaledMollifierKernel_integral_one (n : ℕ) (h : PositiveRadius) :
    (∫ z, scaledMollifierKernel n h z) = 1 := by
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (scaledMollifierKernel n h) h.val (hR := h.property.le)
  simp only [scaledMollifierKernel_smul, integral_const_mul,
    fixedMollifierKernel_integral, mul_one, finrank_euclideanSpace_fin] at hchange
  have heq : (h.val ^ n)⁻¹ * 1 = (h.val ^ n)⁻¹ * ∫ z, scaledMollifierKernel n h z := by
    simpa only [smul_eq_mul, mul_one] using hchange
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero n h.property.ne')) heq).symm

/-- Every local average samples only the enlarged ball, even if F is merely local. -/
theorem mollifiedForcing_L1_ball_le {n q : ℕ} (F : Domain n → Ambient q)
    (a : Domain n) (r : ℝ) (h : PositiveRadius)
    (hF : IntegrableOn F (Metric.ball a (r + h.val))) :
    IntegrableOn (fun x => ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖)
      (Metric.ball a r) ∧
    (∫ x in Metric.ball a r, ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖) ≤
      ∫ z in Metric.ball a (r + h.val), ‖F z‖ := by
  let Ω := ballDomain a (r + h.val)
  have hglobal := kernelConvolution_norm_integral_le Ω F hF
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
    (scaledMollifierKernel_nonneg n h) (scaledMollifierKernel_integral_one n h)
  have heq : EqOn (fun x => ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖)
      (fun x => ‖∫ y, scaledMollifierKernel n h y • zeroExtensionOn Ω F (x - y)‖)
      (Metric.ball a r) := by
    intro x hx
    apply congrArg norm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : scaledMollifierKernel n h y = 0
      · simp only [hy, zero_smul]
      · have hmargin : dist x a + h.val / 2 < r + h.val := by
          have hxr : dist x a < r := hx
          linarith only [hxr, h.property]
        have hxy := scaledMollifierKernel_sampling_ball h a x (r + h.val) hmargin y
          (subset_tsupport _ (Function.mem_support.mpr hy))
        have hxyΩ : x - y ∈ Ω.val := hxy
        simp only [zeroExtensionOn, indicator_of_mem hxyΩ]
  refine ⟨hglobal.1.integrableOn.congr_fun heq.symm measurableSet_ball, ?_⟩
  calc
    _ = ∫ x in Metric.ball a r,
        ‖∫ y, scaledMollifierKernel n h y • zeroExtensionOn Ω F (x - y)‖ :=
      setIntegral_congr_fun measurableSet_ball heq
    _ ≤ ∫ x, ‖∫ y, scaledMollifierKernel n h y • zeroExtensionOn Ω F (x - y)‖ :=
      setIntegral_le_integral hglobal.1 (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := hglobal.2

theorem WeakPoissonOn.mollifiedForcing_L1_energy_le {n q : ℕ} {Ω : OpenDomain n}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hu : MemW12 Ω u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ K * hsNormSq (Du x))
    (a : Domain n) (r : ℝ) (h : PositiveRadius)
    (hBall : Metric.ball a (r + h.val) ⊆ Ω.val) :
    IntegrableOn (fun x => ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖)
      (Metric.ball a r) ∧
    (∫ x in Metric.ball a r, ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖) ≤
      K * ∫ z in Metric.ball a (r + h.val), hsNormSq (Du z) := by
  have hF := (hEq.integrable_of_quadratic_bound hu K hBound).mono_set hBall
  have hlocal := mollifiedForcing_L1_ball_le F a r h hF
  refine ⟨hlocal.1, hlocal.2.trans ?_⟩
  rw [← integral_const_mul]
  have hEnergy : IntegrableOn (fun z => hsNormSq (Du z)) Ω.val :=
    integrable_hsNormSq_of_memLp_columns hu.2.2
  apply integral_mono_ae hF.norm ((hEnergy.mono_set hBall).const_mul K)
  exact ae_restrict_of_ae_restrict_of_subset hBall hBound

/-- Smoothness, the actual Poisson identity, and the local forcing bound use one convolution. -/
theorem WeakPoissonOn.mollification_poisson_and_forcing_energy {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u F : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain a R) Du F)
    (hu : MemW12 (ballDomain a R) u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖F x‖ ≤ K * hsNormSq (Du x))
    (h : PositiveRadius) (hMargin : r + h.val ≤ R) :
    ContDiff ℝ ∞ (euclideanMollification (ballDomain a R) u hu.integrable_ball h) ∧
    (∀ x ∈ Metric.ball a r,
      Laplacian.laplacian (euclideanMollification (ballDomain a R) u hu.integrable_ball h) x =
        ∫ y, scaledMollifierKernel n h y • F (x - y)) ∧
    IntegrableOn (fun x => ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖)
      (Metric.ball a r) ∧
    (∫ x in Metric.ball a r, ‖∫ y, scaledMollifierKernel n h y • F (x - y)‖) ≤
      K * ∫ z in Metric.ball a (r + h.val), hsNormSq (Du z) := by
  have hHalfMargin : r + h.val / 2 ≤ R := by linarith only [hMargin, h.property]
  have hPoisson := hEq.mollification_laplacian_ball hu K hBound h hHalfMargin
  have hForce := hEq.mollifiedForcing_L1_energy_le hu K hBound a r h
    (Metric.ball_subset_ball hMargin)
  exact ⟨hPoisson.1, hPoisson.2, hForce.1, hForce.2⟩

end
end HolderToCK
end
