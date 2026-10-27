module

public import HolderToCK.Analysis.Poisson.KernelCancellation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Fundamental solution boundary terms against continuous test functions

The normalized flux samples the test function at the shrinking sphere. The
Hessian boundary term retains the diagonal point mass with coefficient `1 / n`.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem sphereTestIntegral_continuous {n : ℕ} {φ : Domain n → ℝ}
    (hφ : Continuous φ) {w : Metric.sphere (0 : Domain n) 1 → ℝ}
    (hw : Continuous w) :
    Continuous (fun r : ℝ => ∫ θ : Metric.sphere (0 : Domain n) 1,
      w θ * φ (r • θ.val) ∂(volume : Measure (Domain n)).toSphere) := by
  have hc : Continuous (fun p : ℝ × Metric.sphere (0 : Domain n) 1 =>
      w p.2 * φ (p.1 • p.2.val)) := by
    exact (hw.comp continuous_snd).mul
      (hφ.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (Domain n)).toSphere)
      (f := fun r θ => w θ * φ (r • θ.val)) hc isCompact_univ

theorem normalizedSphereTestIntegral_tendsto {n : ℕ} (hn : 0 < n)
    {φ : Domain n → ℝ} (hφ : Continuous φ) :
    Tendsto (fun r : ℝ => (euclideanSphereArea n)⁻¹ *
      ∫ θ : Metric.sphere (0 : Domain n) 1, φ (r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) (𝓝 0) (𝓝 (φ 0)) := by
  have hc := (sphereTestIntegral_continuous hφ (continuous_const :
    Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => (1 : ℝ)))).const_mul
      (euclideanSphereArea n)⁻¹
  have ht := hc.continuousAt.tendsto (x := (0 : ℝ))
  have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
  have hmass : (volume : Measure (Domain n)).toSphere.real univ = euclideanSphereArea n := rfl
  simpa only [one_mul, zero_smul, integral_const, smul_eq_mul,
    hmass, inv_mul_cancel_left₀ hS] using ht

theorem hessianSphereTestIntegral_tendsto {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {φ : Domain n → ℝ} (hφ : Continuous φ) :
    Tendsto (fun r : ℝ => (euclideanSphereArea n)⁻¹ *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        θ.val i * θ.val j * φ (r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere)
      (𝓝 0) (𝓝 ((if i = j then 1 else 0) / (n : ℝ) * φ 0)) := by
  have hw : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 =>
      θ.val i * θ.val j) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val)
  have ht := ((sphereTestIntegral_continuous hφ hw).const_mul
    (euclideanSphereArea n)⁻¹).continuousAt.tendsto (x := (0 : ℝ))
  have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
  simp only [zero_smul, integral_mul_const, sphereCoordinateProduct_moment hn i j] at ht
  convert ht using 1
  field_simp

theorem fundamentalPower_testFlux {n : ℕ} (hn : 3 ≤ n) (R : PositiveRadius)
    (φ : Domain n → ℝ) :
    (∫ θ : Metric.sphere (0 : Domain n) 1,
      fderiv ℝ fundamentalPowerExpression (R.val • θ.val) θ.val * φ (R.val • θ.val)
      ∂(ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
      (euclideanSphereArea n)⁻¹ * ∫ θ : Metric.sphere (0 : Domain n) 1,
        φ (R.val • θ.val) ∂(volume : Measure (Domain n)).toSphere := by
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      fderiv ℝ fundamentalPowerExpression (R.val • θ.val) θ.val * φ (R.val • θ.val)) =
      (fun θ => ((euclideanSphereArea n)⁻¹ * R.val ^ (-(n : ℝ)) * R.val) *
        φ (R.val • θ.val)) := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    have hθ0 : θ.val ≠ 0 := norm_pos_iff.mp (by rw [hθ]; exact one_pos)
    rw [(fundamentalPower_hasFDerivAt hn _ (smul_ne_zero R.property.ne' hθ0)).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg R.property.le, hθ, mul_one, real_inner_smul_left,
      real_inner_self_eq_norm_sq, one_pow]
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _),
    smul_eq_mul, integral_const_mul, Real.rpow_neg R.property.le, Real.rpow_natCast]
  have hpow : R.val ^ n = R.val ^ (n - 1) * R.val := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 0 < n), pow_succ]
  rw [hpow]
  field_simp [pow_ne_zero _ R.property.ne', R.property.ne']

theorem fundamentalPower_valueBoundary {n : ℕ} (hn : 3 ≤ n) (R : PositiveRadius)
    (ψ : Domain n → ℝ) :
    (∫ θ : Metric.sphere (0 : Domain n) 1,
      fundamentalPowerExpression (R.val • θ.val) * ψ (R.val • θ.val)
      ∂(ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
      ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ * R.val *
        ∫ θ : Metric.sphere (0 : Domain n) 1,
          ψ (R.val • θ.val) ∂(volume : Measure (Domain n)).toSphere := by
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      fundamentalPowerExpression (R.val • θ.val) * ψ (R.val • θ.val)) =
      (fun θ => (((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ *
        R.val ^ (2 - (n : ℝ))) * ψ (R.val • θ.val)) := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [fundamentalPowerExpression, normSq_real_rpow,
      show 2 * ((2 - (n : ℝ)) / 2) = 2 - (n : ℝ) by ring,
      norm_smul, Real.norm_of_nonneg R.property.le, hθ, mul_one]
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _),
    smul_eq_mul, integral_const_mul]
  have hpow : R.val ^ (n - 1) * R.val ^ (2 - (n : ℝ)) = R.val := by
    rw [← Real.rpow_natCast, ← Real.rpow_add R.property]
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (by omega : 1 ≤ n) :
        ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ))
    rw [hn1, show (n : ℝ) - 1 + (2 - (n : ℝ)) = 1 by ring, Real.rpow_one]
  calc
    _ = ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ *
        (R.val ^ (n - 1) * R.val ^ (2 - (n : ℝ))) *
        (∫ θ : Metric.sphere (0 : Domain n) 1, ψ (R.val • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) := by ring
    _ = _ := by rw [hpow]

theorem fundamentalPower_valueBoundary_tendsto {n : ℕ} {ψ : Domain n → ℝ}
    (hψ : Continuous ψ) :
    Tendsto (fun r : ℝ => ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ * r *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ψ (r • θ.val) ∂(volume : Measure (Domain n)).toSphere) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun r : ℝ =>
      ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ * r *
      ∫ θ : Metric.sphere (0 : Domain n) 1, 1 * ψ (r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) :=
    (continuous_const.mul continuous_id).mul
      (sphereTestIntegral_continuous hψ continuous_const)
  have ht := hc.continuousAt.tendsto (x := (0 : ℝ))
  simpa only [one_mul, mul_zero, zero_mul] using ht

theorem fundamentalLog_testFlux (R : PositiveRadius) (φ : Domain 2 → ℝ) :
    (∫ θ : Metric.sphere (0 : Domain 2) 1,
      fderiv ℝ fundamentalLogExpression (R.val • θ.val) θ.val * φ (R.val • θ.val)
      ∂(ENNReal.ofReal R.val • (volume : Measure (Domain 2)).toSphere)) =
      (euclideanSphereArea 2)⁻¹ * ∫ θ : Metric.sphere (0 : Domain 2) 1,
        φ (R.val • θ.val) ∂(volume : Measure (Domain 2)).toSphere := by
  have heq : (fun θ : Metric.sphere (0 : Domain 2) 1 =>
      fderiv ℝ fundamentalLogExpression (R.val • θ.val) θ.val * φ (R.val • θ.val)) =
      (fun θ => ((euclideanSphereArea 2)⁻¹ * R.val ^ (-(2 : ℝ)) * R.val) *
        φ (R.val • θ.val)) := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    have hθ0 : θ.val ≠ 0 := norm_pos_iff.mp (by rw [hθ]; exact one_pos)
    rw [(fundamentalLog_hasFDerivAt _ (smul_ne_zero R.property.ne' hθ0)).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg R.property.le, hθ, mul_one, real_inner_smul_left,
      real_inner_self_eq_norm_sq, one_pow]
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal R.property.le,
    smul_eq_mul, integral_const_mul, Real.rpow_neg R.property.le, Real.rpow_two]
  field_simp [R.property.ne']

theorem fundamentalLog_valueBoundary (R : PositiveRadius) (ψ : Domain 2 → ℝ) :
    (∫ θ : Metric.sphere (0 : Domain 2) 1,
      fundamentalLogExpression (R.val • θ.val) * ψ (R.val • θ.val)
      ∂(ENNReal.ofReal R.val • (volume : Measure (Domain 2)).toSphere)) =
      (2 * Real.pi)⁻¹ * (R.val * Real.log R.val) *
        ∫ θ : Metric.sphere (0 : Domain 2) 1,
          ψ (R.val • θ.val) ∂(volume : Measure (Domain 2)).toSphere := by
  have heq : (fun θ : Metric.sphere (0 : Domain 2) 1 =>
      fundamentalLogExpression (R.val • θ.val) * ψ (R.val • θ.val)) =
      (fun θ => ((2 * Real.pi)⁻¹ * Real.log R.val) * ψ (R.val • θ.val)) := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [fundamentalLogExpression, norm_smul, Real.norm_of_nonneg R.property.le,
      hθ, mul_one]
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal R.property.le,
    smul_eq_mul, integral_const_mul]
  ring

theorem fundamentalLog_valueBoundary_tendsto {ψ : Domain 2 → ℝ}
    (hψ : Continuous ψ) :
    Tendsto (fun r : ℝ => (2 * Real.pi)⁻¹ * (r * Real.log r) *
      ∫ θ : Metric.sphere (0 : Domain 2) 1,
        ψ (r • θ.val) ∂(volume : Measure (Domain 2)).toSphere) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun r : ℝ => r * Real.log r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hI := (sphereTestIntegral_continuous hψ (continuous_const : Continuous
    (fun _ : Metric.sphere (0 : Domain 2) 1 => (1 : ℝ)))).continuousAt.tendsto
      (x := (0 : ℝ))
  have ht := (hlog.const_mul (2 * Real.pi)⁻¹).mul (hI.mono_left nhdsWithin_le_nhds)
  simpa only [one_mul, mul_zero, zero_mul] using ht

theorem radialColumn_testBoundary {n : ℕ} (hn : 0 < n) (R : PositiveRadius)
    (i j : Fin n) (φ : Domain n → ℝ) :
    (∫ θ : Metric.sphere (0 : Domain n) 1,
      ((euclideanSphereArea n)⁻¹ * ‖R.val • θ.val‖ ^ (-(n : ℝ)) *
        (R.val • θ.val) i) * θ.val j * φ (R.val • θ.val)
      ∂(ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
      (euclideanSphereArea n)⁻¹ *
        ∫ θ : Metric.sphere (0 : Domain n) 1,
          θ.val i * θ.val j * φ (R.val • θ.val)
          ∂(volume : Measure (Domain n)).toSphere := by
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      ((euclideanSphereArea n)⁻¹ * ‖R.val • θ.val‖ ^ (-(n : ℝ)) *
        (R.val • θ.val) i) * θ.val j * φ (R.val • θ.val)) =
      (fun θ => ((euclideanSphereArea n)⁻¹ * R.val ^ (-(n : ℝ)) * R.val) *
        (θ.val i * θ.val j * φ (R.val • θ.val))) := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [norm_smul, Real.norm_of_nonneg R.property.le, hθ, mul_one,
      PiLp.smul_apply, smul_eq_mul]
    ring
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _),
    smul_eq_mul, integral_const_mul, Real.rpow_neg R.property.le, Real.rpow_natCast]
  have hpow : R.val ^ n = R.val ^ (n - 1) * R.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  rw [hpow]
  field_simp [pow_ne_zero _ R.property.ne', R.property.ne']

end HolderToCK
end
