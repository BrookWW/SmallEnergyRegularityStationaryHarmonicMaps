module

public import StationaryHarmonicMaps.Analysis.LpPoincareBall
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # The actual same-exponent ball Poincare inequality in real Lp norm form -/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Taking the actual p-th root keeps the radius factor linear. -/
theorem sobolev_poincare_lpNorm_ball {n q : ℕ} (a : Domain n) {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    lpNorm (fun x => u x-(⨍ y in Metric.ball a r,u y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball a r)) ≤
      (2*r*Real.sqrt (n : ℝ)) * ((2 : ℝ)^n)^(1/p) *
        lpNorm (fun x => Real.sqrt (hsNormSq (Du x))) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball a r)) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hU : MemLp (fun x => u x-(⨍ y in Metric.ball a r,u y)) 2 μ :=
    hu.2.1.sub (memLp_const _)
  have hG : MemLp (fun x => Real.sqrt (hsNormSq (Du x))) 2 μ := memLp_sqrt_sum_norm_sq Du hu.2.2
  have H := sobolev_poincare_lp_ball a hr hp hp₂ hu
  have HR := Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p) H (one_div_nonneg.mpr hp0.le)
  have hI : 0 ≤ ∫ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x)))^p :=
    integral_nonneg fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2*r*Real.sqrt (n : ℝ)) _)
      (by positivity)) hI,
    Real.mul_rpow (Real.rpow_nonneg (by positivity : 0 ≤ 2*r*Real.sqrt (n : ℝ)) _) (by positivity)] at HR
  simp only [one_div,Real.rpow_rpow_inv (by positivity : 0 ≤ 2*r*Real.sqrt (n : ℝ)) hp0.ne'] at HR
  rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hU.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hG.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_of_nonneg (Real.sqrt_nonneg _),one_div] using HR

end StationaryHarmonicMaps.Analysis

end
