module

public import StationaryHarmonicMaps.Analysis.SobolevL1Poincare
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import HarmonicMaps.EnergyLemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sobolev mean oscillation controlled by the actual Lp HS-gradient average

Cauchy-Schwarz bounds the sum of column norms by the HS norm with factor
sqrt(n). The L1 Sobolev Poincare inequality and forward finite-measure Holder
inequality then give the mean-oscillation estimate for every 1 ≤ p ≤ 2.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators

namespace StationaryHarmonicMaps

/-- The sum of coordinate-column norms is bounded by the genuine HS norm. -/
theorem sum_column_norm_le_sqrt_dimension_mul_hs {n q : ℕ} (A : Gradient n q) :
    (∑ i : Fin n, ‖A i‖) ≤ Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq A) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _i : Fin n => (1 : ℝ)) (fun i => ‖A i‖)
  have hsq : (∑ i : Fin n, ‖A i‖) ^ 2 ≤ (n : ℝ) * hsNormSq A := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hsNormSq] using hcs
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _i _hi => norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    Real.sq_sqrt (hsNormSq_nonneg A)] using hsq

/-- The ball integral version uses the displayed weak gradient's HS norm. -/
theorem sobolev_poincare_l1_hs_ball {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (∫ x in Metric.ball a r, ‖u x - (⨍ y in Metric.ball a r, u y)‖) ≤
      ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r *
        ∫ x in Metric.ball a r, Real.sqrt (hsNormSq (Du x)) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hDu (i : Fin n) : MemLp (fun x => Du x i) 2 μ := hu.2.2 i
  have hHS : MemLp (fun x => Real.sqrt (hsNormSq (Du x))) 2 μ := by
    simpa only [hsNormSq] using memLp_sqrt_sum_norm_sq (μ := μ) Du hDu
  have hsum : Integrable (fun x => ∑ i : Fin n, ‖Du x i‖) μ :=
    integrable_finsetSum Finset.univ
      (fun i _ => ((hu.2.2 i).integrable (by norm_num)).norm)
  have hbound : (∫ x, ∑ i : Fin n, ‖Du x i‖ ∂μ) ≤
      Real.sqrt (n : ℝ) * ∫ x, Real.sqrt (hsNormSq (Du x)) ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hsum ((hHS.integrable (by norm_num)).const_mul _)
      (fun x => sum_column_norm_le_sqrt_dimension_mul_hs (Du x))
  have hpoincare := sobolev_poincare_l1_ball a hr hu
  have hresult := hpoincare.trans
    (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1) * r))
  simpa only [mul_assoc, mul_left_comm] using hresult

/-- The ball mean oscillation is controlled by its actual mean HS-gradient norm. -/
theorem sobolev_ballAverage_oscillation_le_mean_hs {n q : ℕ} (a : Domain n)
    {r : ℝ} (hr : 0 < r) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (⨍ x in Metric.ball a r, ‖u x - (⨍ y in Metric.ball a r, u y)‖) ≤
      ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r *
        (⨍ x in Metric.ball a r, Real.sqrt (hsNormSq (Du x))) := by
  have h := mul_le_mul_of_nonneg_left (sobolev_poincare_l1_hs_ball a hr hu)
    (inv_nonneg.mpr (show 0 ≤ volume.real (Metric.ball a r) from ENNReal.toReal_nonneg))
  simpa only [setAverage_eq, smul_eq_mul, mul_assoc, mul_left_comm] using h

/-- The actual Lp gradient average controls Sobolev oscillation, including p=1 and p=2. -/
theorem sobolev_ballAverage_oscillation_le_lp_hs {n q : ℕ} (a : Domain n)
    {r p : ℝ} (hr : 0 < r) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (⨍ x in Metric.ball a r, ‖u x - (⨍ y in Metric.ball a r, u y)‖) ≤
      ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r *
        (⨍ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) ^ (1 / p) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hDu (i : Fin n) : MemLp (fun x => Du x i) 2 μ := hu.2.2 i
  have hHS : MemLp (fun x => Real.sqrt (hsNormSq (Du x))) 2 μ := by
    simpa only [hsNormSq] using memLp_sqrt_sum_norm_sq (μ := μ) Du hDu
  have hHSp := memLp_real_of_memL2 (fun x => Real.sqrt (hsNormSq (Du x))) hp₂ hHS
  have hHolder : (⨍ x in Metric.ball a r, Real.sqrt (hsNormSq (Du x))) ≤
      (⨍ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) ^ (1 / p) := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      ballAverage_norm_le_rpow_ballAverage_norm_rpow
        (fun x => Real.sqrt (hsNormSq (Du x))) a hr hp₁ hHSp
  exact (sobolev_ballAverage_oscillation_le_mean_hs a hr hu).trans
    (mul_le_mul_of_nonneg_left hHolder
      (by positivity : 0 ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r))

end StationaryHarmonicMaps

end
