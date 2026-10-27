module

public import HolderToCK.Analysis.ConvolutionDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Interior smoothing of a distribution-harmonic L² field

The second derivatives of a compact kernel are admissible distributional
Laplacian tests. Differentiation of the actual zero-extension convolution
therefore makes its interior mollifications classically harmonic, without
assuming continuity or a weak gradient of the original field.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology Convolution

namespace StationaryHarmonicMaps.Analysis

/-- The native Laplacian is the sum of the actual second coordinate derivatives. -/
theorem laplacian_eq_sum_second_coordinate {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain n → F) (hf : ContDiff ℝ ∞ f) (x : Domain n) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) univ :=
    hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDf.contDiffAt (isOpen_univ.mem_nhds (mem_univ x))).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

/-- Reflection and translation preserve the native scalar kernel Laplacian. -/
theorem laplacian_translatedKernelTest {n : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (x z : Domain n) :
    Laplacian.laplacian (translatedKernelTest χ x) z =
      Laplacian.laplacian χ (x - z) := by
  let dχ (i : Fin n) (y : Domain n) := fderiv ℝ χ y (EuclideanSpace.single i 1)
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfirst (i : Fin n) :
      (fun y => fderiv ℝ (translatedKernelTest χ x) y (EuclideanSpace.single i 1)) =
        -(translatedKernelTest (dχ i) x) := by
    funext y
    exact translatedKernelTest_coordinateDerivative hχ x y i
  rw [laplacian_eq_sum_second_coordinate _ (translatedKernelTest_contDiff hχ x),
    laplacian_eq_sum_second_coordinate _ hχ]
  apply Finset.sum_congr rfl
  intro i _
  rw [hfirst i, fderiv_neg]
  change -(fderiv ℝ (translatedKernelTest (dχ i) x) z (EuclideanSpace.single i 1)) = _
  rw [show fderiv ℝ (translatedKernelTest (dχ i) x) z (EuclideanSpace.single i 1) =
      -(fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1)) from
        translatedKernelTest_coordinateDerivative (hdχ i) x z i, neg_neg]

/-- Kernel differentiation computes the actual convolution Laplacian from L¹ data alone. -/
theorem kernelConvolution_laplacian_eq_kernel_laplacian {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val volume)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Domain n) :
    Laplacian.laplacian (fun y => ∫ z, χ z • zeroExtensionOn Ω u (y - z)) x =
      ∫ z in Ω.val, Laplacian.laplacian χ (x - z) • u z := by
  let dχ (i : Fin n) (y : Domain n) := fderiv ℝ χ y (EuclideanSpace.single i 1)
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcdχ (i : Fin n) : HasCompactSupport (dχ i) :=
    hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hfirst (i : Fin n) :
      (fun y => fderiv ℝ (fun y => ∫ z, χ z • zeroExtensionOn Ω u (y - z)) y
        (EuclideanSpace.single i 1)) =
      (fun y => ∫ z, dχ i z • zeroExtensionOn Ω u (y - z)) := by
    funext y
    rw [HolderToCK.kernelConvolution_fderiv Ω u hu hχ hcχ]
    have H := integral_sub_left_eq_self
      (fun z => dχ i z • zeroExtensionOn Ω u (y - z)) volume y
    simpa only [sub_sub_cancel] using H
  have hInt (i : Fin n) : Integrable (fun z =>
      fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1) • zeroExtensionOn Ω u z) volume := by
    have hcont : Continuous (fun z => fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1)) :=
      (((hdχ i).continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    have hcompact : HasCompactSupport
        (fun z => fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1)) :=
      ((hcdχ i).fderiv_apply ℝ (EuclideanSpace.single i 1)).comp_homeomorph (Homeomorph.subLeft x)
    exact (zeroExtensionOn_integrable Ω u hu).smul_of_top_right
      (hcont.memLp_top_of_hasCompactSupport hcompact volume)
  rw [laplacian_eq_sum_second_coordinate _ (kernelConvolution_contDiff Ω u hu hχ hcχ)]
  calc
    _ = ∑ i : Fin n, ∫ z,
        fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1) • zeroExtensionOn Ω u z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hfirst i, HolderToCK.kernelConvolution_fderiv Ω u hu (hdχ i) (hcdχ i)]
    _ = ∫ z, ∑ i : Fin n,
        fderiv ℝ (dχ i) (x - z) (EuclideanSpace.single i 1) • zeroExtensionOn Ω u z :=
      (integral_finsetSum _ (fun i _ => hInt i)).symm
    _ = ∫ z, Laplacian.laplacian χ (x - z) • zeroExtensionOn Ω u z := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      rw [laplacian_eq_sum_second_coordinate _ hχ, Finset.sum_smul]
    _ = _ := by
      simp only [zeroExtensionOn, ← indicator_smul]
      exact integral_indicator Ω.property.measurableSet

/-- An actual distributional Laplacian identity makes the interior kernel convolution harmonic. -/
theorem distribution_harmonic_kernelConvolution {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val volume)
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ω.val → (∫ z in Ω.val, Laplacian.laplacian η z • u z) = 0)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Domain n) (hSample : ∀ y ∈ tsupport χ, x - y ∈ Ω.val) :
    Laplacian.laplacian (fun y => ∫ z, χ z • zeroExtensionOn Ω u (y - z)) x = 0 := by
  rw [kernelConvolution_laplacian_eq_kernel_laplacian Ω u hu hχ hcχ]
  have H := hharm (translatedKernelTest χ x) (translatedKernelTest_contDiff hχ x)
    (translatedKernelTest_hasCompactSupport hcχ x) (translatedKernelTest_tsupport_subset Ω x hSample)
  simpa only [laplacian_translatedKernelTest hχ] using H

/-- Actual ball L² data and the distributional identity produce smooth harmonic mollifications. -/
theorem memLp_two_distribution_harmonic_mollification_ball {n q : ℕ}
    (a : Domain n) (R r : ℝ) (u : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (Metric.ball a R)))
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball a R →
        (∫ z in Metric.ball a R, Laplacian.laplacian η z • u z) = 0)
    (h : PositiveRadius) (hMargin : r + h.val / 2 ≤ R) :
    ContDiff ℝ ∞ (fun x => ∫ z, scaledMollifierKernel n h z •
      zeroExtensionOn (ballDomain a R) u (x - z)) ∧
    ∀ x ∈ Metric.ball a r, Laplacian.laplacian
      (fun y => ∫ z, scaledMollifierKernel n h z • zeroExtensionOn (ballDomain a R) u (y - z)) x = 0 := by
  have hI : IntegrableOn u (Metric.ball a R) volume := by
    letI : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    exact hu.integrable (by norm_num)
  refine ⟨kernelConvolution_contDiff (ballDomain a R) u hI
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h), ?_⟩
  intro x hx
  apply distribution_harmonic_kernelConvolution (ballDomain a R) u hI hharm
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h) x
  apply scaledMollifierKernel_sampling_ball h a x R
  have hxr : dist x a < r := hx
  linarith only [hxr, hMargin]

end StationaryHarmonicMaps.Analysis

end
