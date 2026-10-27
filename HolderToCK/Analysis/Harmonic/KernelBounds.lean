module

public import HolderToCK.Analysis.Harmonic.KernelDerivatives
public import HarmonicMaps.Analysis.MollificationChangeVariables
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Dimension and order bounds for the scaled kernel

Compact support bounds every actual derivative of the fixed kernel. The
positive-radius dilation produces the exact power `h^(-n-k)` in its native
multilinear operator norm.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

noncomputable section

theorem scaledMollifierKernel_derivative_bound (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : PositiveRadius) (z : Domain n),
      ‖iteratedFDeriv ℝ k (scaledMollifierKernel n h) z‖ ≤
        C * (h.val ^ (n + k))⁻¹ := by
  have hcont : Continuous (iteratedFDeriv ℝ k (fixedMollifierKernel n)) :=
    (fixedMollifierKernel_contDiff n).continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨C, hC⟩ := ((fixedMollifierKernel_hasCompactSupport n).iteratedFDeriv k).exists_bound_of_continuous hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro h z
  have hfixed : ContDiff ℝ k (fixedMollifierKernel n) :=
    (fixedMollifierKernel_contDiff n).of_le (mod_cast le_top)
  have hcomp : ContDiff ℝ k (fun z : Domain n => fixedMollifierKernel n (h.val⁻¹ • z)) :=
    hfixed.comp (contDiff_id.const_smul _)
  have hscaled : scaledMollifierKernel n h =
      (h.val ^ n)⁻¹ • (fun z : Domain n => fixedMollifierKernel n (h.val⁻¹ • z)) := rfl
  rw [hscaled, iteratedFDeriv_const_smul_apply hcomp.contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul h.val⁻¹ hfixed) z]
  rw [norm_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg h.property.le n)),
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr h.property.le) k)]
  have hcoeff : (h.val ^ n)⁻¹ * (h.val⁻¹) ^ k = (h.val ^ (n + k))⁻¹ := by
    rw [← inv_pow, ← pow_add, inv_pow]
  calc
    _ = (h.val ^ (n + k))⁻¹ *
        ‖iteratedFDeriv ℝ k (fixedMollifierKernel n) (h.val⁻¹ • z)‖ := by
      rw [← mul_assoc, hcoeff]
    _ ≤ (h.val ^ (n + k))⁻¹ * max C 1 :=
      mul_le_mul_of_nonneg_left ((hC _).trans (le_max_left _ _))
        (inv_nonneg.mpr (pow_nonneg h.property.le _))
    _ = _ := mul_comm _ _


theorem kernelConvolution_iteratedFDeriv_norm_le {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ C) (x : Domain n) :
    ‖iteratedFDeriv ℝ k (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x‖ ≤
      C * ∫ z in Ω.val, ‖u z‖ := by
  have hInt := zeroExtensionOn_integrable Ω u hu
  have hmass : (∫ z, ‖zeroExtensionOn Ω u z‖) = ∫ z in Ω.val, ‖u z‖ := by
    have heq : (fun z => ‖zeroExtensionOn Ω u z‖) =
        Ω.val.indicator (fun z => ‖u z‖) := by
      funext z
      by_cases hz : z ∈ Ω.val
      · simp only [zeroExtensionOn, indicator_of_mem hz]
      · simp only [zeroExtensionOn, indicator_of_notMem hz, norm_zero]
    rw [heq, integral_indicator Ω.property.measurableSet]
  have hmasspos : 0 ≤ ∫ z in Ω.val, ‖u z‖ := integral_nonneg (fun _ => norm_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hmasspos)
  intro v
  rw [kernelConvolution_iteratedFDeriv_apply Ω u hu hχ hcχ k]
  have hprod : 0 ≤ ∏ i : Fin k, ‖v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hpoint (z : Domain n) :
      ‖iteratedFDeriv ℝ k χ (x - z) v • zeroExtensionOn Ω u z‖ ≤
        (C * ∏ i : Fin k, ‖v i‖) * ‖zeroExtensionOn Ω u z‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (((iteratedFDeriv ℝ k χ (x - z)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hbound _) hprod)) (norm_nonneg _)
  calc
    _ ≤ ∫ z, (C * ∏ i : Fin k, ‖v i‖) * ‖zeroExtensionOn Ω u z‖ :=
      norm_integral_le_of_norm_le (hInt.norm.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = (C * ∫ z in Ω.val, ‖u z‖) * ∏ i : Fin k, ‖v i‖ := by
      rw [integral_const_mul, hmass]
      ring

end
end HolderToCK
end
