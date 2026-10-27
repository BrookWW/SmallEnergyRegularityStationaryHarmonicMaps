module

public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Smooth cutoffs of finite Sobolev maps

Multiplication by a smooth compactly supported scalar function preserves the
actual weak gradient. The product rule follows by testing the original weak
identity with the product of the cutoff and the scalar test.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

/-- The classical coordinate product rule for two smooth scalar functions. -/
theorem coordinateDerivative_mul {n : ℕ} {f g : Domain n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) (x : Domain n) :
    coordinateDerivative (fun y => f y * g y) (hf.mul hg) i x =
      coordinateDerivative f hf i x * g x + f x * coordinateDerivative g hg i x := by
  have h := ((hf.differentiable (by simp) x).hasFDerivAt.mul
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y * g y) x = _ at h
  simp only [coordinateDerivative, h, add_apply, smul_apply, smul_eq_mul]
  ring

/-- A compact smooth cutoff has the genuine Sobolev product gradient. -/
theorem MemW12.smoothCutoff_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    MemW12 (ballDomain a R) (fun x => χ x • u x)
      (fun x i => coordinateDerivative χ hχ i x • u x + χ x • Du x i) := by
  let μ := volume.restrict (Metric.ball a R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a R).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hχL : MemLp χ ∞ μ := hχ.continuous.memLp_top_of_hasCompactSupport hcχ μ
  have hdχL (i : Fin n) : MemLp (coordinateDerivative χ hχ i) ∞ μ :=
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  have huL : MemLp (fun x => χ x • u x) 2 μ := hu.2.1.smul hχL
  have hDuL (i : Fin n) : MemLp
      (fun x => coordinateDerivative χ hχ i x • u x + χ x • Du x i) 2 μ :=
    (hu.2.1.smul (r := (2 : ℝ≥0∞)) (hdχL i)).add ((hu.2.2 i).smul (r := (2 : ℝ≥0∞)) hχL)
  have huI : IntegrableOn (fun x => χ x • u x) (Metric.ball a R) :=
    huL.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hDuI (i : Fin n) : IntegrableOn
      (fun x => coordinateDerivative χ hχ i x • u x + χ x • Du x i) (Metric.ball a R) :=
    (hDuL i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨⟨huI.locallyIntegrableOn,
    fun i => (hDuI i).locallyIntegrableOn, ?_⟩,
    huL, hDuL⟩
  intro i φ hφ hcφ hsφ
  have hprod : ContDiff ℝ ∞ (fun x => φ x * χ x) := hφ.mul hχ
  have hcprod : HasCompactSupport (fun x => φ x * χ x) := hcφ.mul_right
  have hsprod : tsupport (fun x => φ x * χ x) ⊆ (ballDomain a R).val :=
    tsupport_mul_subset_left.trans hsφ
  have hibp := hu.1.2.2 i (fun x => φ x * χ x) hprod hcprod hsprod
  have hφL : MemLp φ ∞ μ := hφ.continuous.memLp_top_of_hasCompactSupport hcφ μ
  have hdφL : MemLp (coordinateDerivative φ hφ i) ∞ μ :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  have hA : Integrable (fun x => coordinateDerivative φ hφ i x • (χ x • u x)) μ :=
    (huL.smul (r := (2 : ℝ≥0∞)) hdφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hB : Integrable (fun x => φ x • (coordinateDerivative χ hχ i x • u x)) μ :=
    ((hu.2.1.smul (r := (2 : ℝ≥0∞)) (hdχL i)).smul (r := (2 : ℝ≥0∞)) hφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hC : Integrable (fun x => φ x • (χ x • Du x i)) μ :=
    (((hu.2.2 i).smul (r := (2 : ℝ≥0∞)) hχL).smul (r := (2 : ℝ≥0∞)) hφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp_rw [coordinateDerivative_mul hφ hχ, add_smul, mul_smul] at hibp
  change (∫ x, coordinateDerivative φ hφ i x • (χ x • u x) +
    φ x • (coordinateDerivative χ hχ i x • u x) ∂μ) =
    -(∫ x, φ x • (χ x • Du x i) ∂μ) at hibp
  rw [integral_add hA hB] at hibp
  change (∫ x, coordinateDerivative φ hφ i x • (χ x • u x) ∂μ) =
    -(∫ x, φ x • (coordinateDerivative χ hχ i x • u x + χ x • Du x i) ∂μ)
  simp_rw [smul_add]
  rw [integral_add hB hC]
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = ((∫ x, coordinateDerivative φ hφ i x • (χ x • u x) ∂μ) +
        ∫ x, φ x • (coordinateDerivative χ hχ i x • u x) ∂μ) +
        ∫ x, φ x • (χ x • Du x i) ∂μ := (add_assoc _ _ _).symm
    _ = 0 := by rw [hibp, neg_add_cancel]

end HarmonicMaps
