module

public import HarmonicMaps.Analysis.MollificationL2Convergence
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Global bounds of the actual convolution of a bounded L2 field

The unit-mass nonnegative kernel preserves a genuine almost-everywhere
value bound. A global Lipschitz bound for the actual compact smooth kernel,
combined with the original L1 norm, gives a global Lipschitz bound for its
convolution. No weak derivative of the zero-extended field is used.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped Topology ContDiff Convolution

namespace StationaryHarmonicMaps.Analysis

private theorem exists_compact_smooth_lipschitz_bound {n : ℕ}
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ (K : ℝ) (hK : 0 ≤ K), LipschitzWith (⟨K, hK⟩ : NNReal) χ := by
  have hD : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (hcχ.fderiv ℝ).exists_bound_of_continuous hD
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨K, hK0, ?_⟩
  exact lipschitzWith_of_nnnorm_fderiv_le (hχ.differentiable (by simp))
    (fun x => by exact_mod_cast hK x)

private theorem norm_fixed_average_le_of_ae_bound {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) {B : ℝ} (hbound : ∀ᵐ x ∂volume, ‖F x‖ ≤ B)
    (h : PositiveRadius) (x : Domain n) :
    ‖∫ y, fixedMollifierKernel n y • F (x - h.val • y)‖ ≤ B := by
  have hsample : ∀ᵐ y ∂volume, ‖F (x - h.val • y)‖ ≤ B :=
    ((Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume h.property.ne')).ae hbound
  have hi := weighted_shift_integrable hF h x
  calc
    _ ≤ ∫ y, ‖fixedMollifierKernel n y • F (x - h.val • y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, fixedMollifierKernel n y * B :=
      integral_mono_ae hi.norm ((fixedMollifierKernel_integrable n).mul_const B)
        (hsample.mono fun y hy => by
          dsimp only
          rw [norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y)]
          exact mul_le_mul_of_nonneg_left hy (fixedMollifierKernel_nonneg n y))
    _ = B := by rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]

private theorem convolution_lipschitz_bound {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (χ : Domain n → ℝ) (hχ : Continuous χ)
    (K : ℝ) (hK : ∀ z, ‖χ z‖ ≤ K) (C : NNReal) (hLip : LipschitzWith C χ)
    (x y : Domain n) :
    dist (∫ z, χ z • F (x - z)) (∫ z, χ z • F (y - z)) ≤
      (C : ℝ) * (∫ z, ‖F z‖) * dist x y := by
  have hflip (w : Domain n) : (∫ z, χ z • F (w - z)) = ∫ z, χ (w - z) • F z := by
    have H := congrFun (convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (f := χ) (g := F) (μ := volume)) w
    exact H.symm
  have hI (w : Domain n) : Integrable (fun z => χ (w - z) • F z) volume :=
    hF.bdd_smul K (hχ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => hK _)
  have heq : (∫ z, χ (x - z) • F z) - (∫ z, χ (y - z) • F z) =
      ∫ z, (χ (x - z) - χ (y - z)) • F z := by
    rw [← integral_sub (hI x) (hI y)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => (sub_smul _ _ _).symm
  have hdiff : Integrable (fun z => (χ (x - z) - χ (y - z)) • F z) volume := by
    exact ((hI x).sub (hI y)).congr (Eventually.of_forall fun z => (sub_smul _ _ _).symm)
  rw [hflip x, hflip y, dist_eq_norm, heq]
  calc
    _ ≤ ∫ z, ‖(χ (x - z) - χ (y - z)) • F z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ((C : ℝ) * dist x y) * ‖F z‖ :=
      integral_mono hdiff.norm (hF.norm.const_mul _) (fun z => by
        rw [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Real.dist_eq, dist_sub_right] using hLip.dist_le_mul (x - z) (y - z))
    _ = _ := by rw [integral_const_mul]; ring

/-- Every positive-scale literal average has an actual global value and common Lipschitz bound. -/
theorem exists_bounded_fixed_mollification_bounds (n : ℕ) (h : PositiveRadius)
    (B M : ℝ) (_hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (q : ℕ) (F : Domain n → Ambient q),
      Integrable F volume → MemLp F 2 volume →
      (∀ᵐ x ∂volume, ‖F x‖ ≤ B) → (∫ x, ‖F x‖) ≤ M →
      let m := fun x => ∫ y, fixedMollifierKernel n y • F (x - h.val • y)
      ContDiff ℝ ∞ m ∧ MemLp m 2 volume ∧ (∀ x, ‖m x‖ ≤ B) ∧
      ∀ x y, dist (m x) (m y) ≤ L * dist x y := by
  let χ := scaledMollifierKernel n h
  have hχ : ContDiff ℝ ∞ χ := scaledMollifierKernel_contDiff n h
  have hcχ : HasCompactSupport χ := scaledMollifierKernel_hasCompactSupport n h
  obtain ⟨K, _hK0, hK⟩ := exists_compact_smooth_lipschitz_bound χ hχ hcχ
  obtain ⟨A, hA⟩ := hcχ.exists_bound_of_continuous hχ.continuous
  have hK0 : 0 ≤ K := _hK0
  refine ⟨K * M, mul_nonneg hK0 hM, ?_⟩
  intro q F hF hF2 hbound hnorm
  refine ⟨fixedKernelAverage_contDiff hF h, fixedKernelAverage_memLp hF hF2 h,
    norm_fixed_average_le_of_ae_bound hF hbound h, ?_⟩
  intro x y
  dsimp only
  rw [fixedKernelAverage_eq_scaledConvolution F h x, fixedKernelAverage_eq_scaledConvolution F h y]
  exact (convolution_lipschitz_bound hF χ hχ.continuous A hA ⟨K, hK0⟩ hK x y).trans
    (by
      have H := mul_le_mul_of_nonneg_left hnorm hK0
      exact mul_le_mul_of_nonneg_right H dist_nonneg)

end StationaryHarmonicMaps.Analysis

end
