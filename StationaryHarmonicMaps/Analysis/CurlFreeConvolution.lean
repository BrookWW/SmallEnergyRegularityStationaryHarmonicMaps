module

public import HolderToCK.Analysis.ConvolutionDerivatives
public import HolderToCK.Foundation.WeakPoisson

/-!
# Actual curl-free smoothing from planar distribution tests

The original zero-divergence predicate for the negative planar rotation
produces the scalar-test Bochner curl identity. Reflected compact kernel
tests then identify the actual mixed first derivatives of the original
L² field's zero-extension convolution. No weak derivative of that zero
extension or primitive of the original field is assumed.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The original full vector weak curl equation gives the actual scalar-test Bochner equality. -/
theorem planar_weak_curl_scalar_test {q : ℕ} (a : Domain 2) (R : ℝ)
    (F : Domain 2 → Gradient 2 q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R)))
    (hcurl : HolderToCK.WeakPoissonOn (ballDomain a R)
      (fun x i => -(![-F x 1,F x 0] : Gradient 2 q) i) (fun _ => 0))
    (η : Domain 2 → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball a R) :
    IntegrableOn (fun x => fderiv ℝ η x (EuclideanSpace.single (0 : Fin 2) 1) • F x 1)
      (Metric.ball a R) volume ∧
    IntegrableOn (fun x => fderiv ℝ η x (EuclideanSpace.single (1 : Fin 2) 1) • F x 0)
      (Metric.ball a R) volume ∧
    (∫ x in Metric.ball a R, fderiv ℝ η x (EuclideanSpace.single (0 : Fin 2) 1) • F x 1) =
      ∫ x in Metric.ball a R, fderiv ℝ η x (EuclideanSpace.single (1 : Fin 2) 1) • F x 0 := by
  let Ω := ballDomain a R
  let μ := volume.restrict Ω.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let d (i : Fin 2) (x : Domain 2) := fderiv ℝ η x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : Continuous (d i) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcd (i : Fin 2) : HasCompactSupport (d i) := hcη.fderiv_apply ℝ _
  have hInt (i j : Fin 2) : Integrable (fun x => d i x • F x j) μ :=
    ((show MemLp (fun x => F x j) 2 μ from hF j).integrable (by norm_num)).smul_of_top_right
      ((hd i).memLp_top_of_hasCompactSupport (hcd i) μ)
  refine ⟨hInt 0 1,hInt 1 0,?_⟩
  ext j
  let v : Ambient q := EuclideanSpace.single j 1
  let ψ := fun x => η x • v
  have hψ : ContDiff ℝ ∞ ψ := hη.smul contDiff_const
  have hcψ : HasCompactSupport ψ := hcη.smul_right
  have hsψ : tsupport ψ ⊆ Ω.val := (tsupport_smul_subset_left η (fun _ => v)).trans hsη
  have hDψ (x : Domain 2) (i : Fin 2) :
      fderiv ℝ ψ x (EuclideanSpace.single i 1) = d i x • v := by
    exact congrArg (fun L : Domain 2 →L[ℝ] Ambient q => L (EuclideanSpace.single i 1))
      ((hη.differentiable (by simp) x).hasFDerivAt.smul_const v).fderiv
  have H := ((hcurl.2 ψ hψ hcψ hsψ).2.2)
  have hpoint (x : Domain 2) :
      (∑ i : Fin 2, inner ℝ (-(![-F x 1,F x 0] : Gradient 2 q) i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = d 0 x * F x 1 j - d 1 x * F x 0 j := by
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      neg_neg,hDψ,inner_neg_left,real_inner_smul_right,v,
      EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.neg_apply,mul_neg,neg_neg,sub_eq_add_neg]
  have hI₀ : Integrable (fun x => d 0 x * F x 1 j) μ := by
    simpa only [v,EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.smul_apply,smul_eq_mul]
      using (hInt 0 1).inner_const (𝕜 := ℝ) v
  have hI₁ : Integrable (fun x => d 1 x * F x 0 j) μ := by
    simpa only [v,EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.smul_apply,smul_eq_mul]
      using (hInt 1 0).inner_const (𝕜 := ℝ) v
  have hscalar : (∫ x, d 0 x * F x 1 j ∂μ) = ∫ x, d 1 x * F x 0 j ∂μ := by
    rw [integral_congr_ae (Eventually.of_forall hpoint),integral_sub hI₀ hI₁] at H
    simpa only [inner_zero_left,integral_zero,neg_zero,sub_eq_zero] using H
  have hcoord₀ := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).integral_comp_comm (hInt 0 1)
  have hcoord₁ := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).integral_comp_comm (hInt 1 0)
  exact hcoord₀.symm.trans (hscalar.trans hcoord₁)

/-- Reflected kernel tests make the genuine smooth zero-extension convolution curl-free at every interior sample point. -/
theorem planar_kernelConvolution_curl_free {q : ℕ} (a : Domain 2) (R : ℝ)
    (F : Domain 2 → Gradient 2 q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R)))
    (hcurl : HolderToCK.WeakPoissonOn (ballDomain a R)
      (fun x i => -(![-F x 1,F x 0] : Gradient 2 q) i) (fun _ => 0))
    {χ : Domain 2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Domain 2) (hSample : ∀ y ∈ tsupport χ, x-y ∈ Metric.ball a R) :
    (∀ i : Fin 2, ContDiff ℝ ∞ (fun y => ∫ z, χ z •
      zeroExtensionOn (ballDomain a R) (fun w => F w i) (y-z))) ∧
    fderiv ℝ (fun y => ∫ z, χ z • zeroExtensionOn (ballDomain a R) (fun w => F w 1) (y-z)) x
      (EuclideanSpace.single (0 : Fin 2) 1) =
    fderiv ℝ (fun y => ∫ z, χ z • zeroExtensionOn (ballDomain a R) (fun w => F w 0) (y-z)) x
      (EuclideanSpace.single (1 : Fin 2) 1) := by
  let Ω := ballDomain a R
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hI (i : Fin 2) : IntegrableOn (fun y => F y i) Ω.val volume :=
    (show MemLp (fun y => F y i) 2 (volume.restrict Ω.val) from hF i).integrable (by norm_num)
  refine ⟨fun i => kernelConvolution_contDiff Ω (fun y => F y i) (hI i) hχ hcχ,?_⟩
  have H := (planar_weak_curl_scalar_test a R F hF hcurl (translatedKernelTest χ x)
    (translatedKernelTest_contDiff hχ x) (translatedKernelTest_hasCompactSupport hcχ x)
    (translatedKernelTest_tsupport_subset Ω x hSample)).2.2
  have hRef (z : Domain 2) (i : Fin 2) :
      fderiv ℝ (translatedKernelTest χ x) z (EuclideanSpace.single i 1) =
        -(fderiv ℝ χ (x-z) (EuclideanSpace.single i 1)) :=
    translatedKernelTest_coordinateDerivative hχ x z i
  simp only [hRef,neg_smul,integral_neg] at H
  have Hpos := neg_injective H
  rw [HolderToCK.kernelConvolution_fderiv Ω _ (hI 1) hχ hcχ,
    HolderToCK.kernelConvolution_fderiv Ω _ (hI 0) hχ hcχ]
  simp only [zeroExtensionOn,← indicator_smul]
  rw [integral_indicator Ω.property.measurableSet,integral_indicator Ω.property.measurableSet]
  exact Hpos

end StationaryHarmonicMaps.Analysis

end
