module

public import HarmonicMaps.Analysis.SobolevMollificationGradient
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # Derivatives of compact-kernel convolutions

The convolution uses the literal domain zero extension of integrable data.
The Laplacian is the sum of second coordinate derivatives.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff Convolution

namespace HolderToCK

noncomputable section

theorem kernelConvolution_eq_setIntegral {n q : ℕ} (Ω : OpenDomain n)
    (F : Domain n → Ambient q) (χ : Domain n → ℝ) (x : Domain n) :
    (∫ y, χ y • zeroExtensionOn Ω F (x - y)) =
      ∫ z in Ω.val, χ (x - z) • F z := by
  calc
    _ = ∫ z, χ (x - z) • zeroExtensionOn Ω F z := by
      rw [← integral_sub_left_eq_self
        (fun y => χ y • zeroExtensionOn Ω F (x - y)) volume x]
      simp only [sub_sub_cancel]
    _ = _ := by
      simp only [zeroExtensionOn, ← indicator_smul]
      exact integral_indicator Ω.property.measurableSet

theorem laplacian_eq_sum_coordinateDerivatives {n q : ℕ}
    (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f) (x : Domain n) :
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

theorem kernelConvolution_fderiv {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x v : Domain n) :
    fderiv ℝ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x v =
      ∫ z, fderiv ℝ χ (x - z) v • zeroExtensionOn Ω u z := by
  let L : ℝ →L[ℝ] Ambient q →L[ℝ] Ambient q := ContinuousLinearMap.lsmul ℝ ℝ
  have hzero := (zeroExtensionOn_integrable Ω u hu).locallyIntegrable
  have hderiv := hcχ.hasFDerivAt_convolution_right L.flip hzero
    (hχ.of_le (by simp)) x
  rw [convolution_flip] at hderiv
  change fderiv ℝ (χ ⋆[L, volume] zeroExtensionOn Ω u) x v = _
  rw [hderiv.fderiv,
    convolution_precompR_apply L.flip hzero (hcχ.fderiv ℝ)
      (hχ.continuous_fderiv (by simp)) x v]
  rfl

end
end HolderToCK
end
