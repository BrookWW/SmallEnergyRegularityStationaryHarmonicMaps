module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Finite-measure Hölder bounds for literal norm integrals

The comparison is in the forward direction from a larger integrability
exponent to a smaller one. Positive finite set averages have Hölder constant
one. All integrals and powers are the actual Bochner norm integrals, rather
than an assumed Sobolev or mean-oscillation conclusion.
-/

public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StationaryHarmonicMaps

section FiniteMeasure

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} [IsFiniteMeasure μ]

/-- Finite-measure exponent comparison, expressed as roots of real norm integrals. -/
theorem integral_norm_rpow_root_le_of_exponent_le (f : X → E)
    {r p : ℝ} (hr : 0 < r) (hrp : r ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, ‖f x‖ ^ r ∂μ) ^ (1 / r) ≤
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) *
        (μ.real univ) ^ (1 / r - 1 / p) := by
  have hp : 0 < p := hr.trans_le hrp
  have hexp : 0 ≤ 1 / r - 1 / p :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hr hrp)
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (ENNReal.ofReal_le_ofReal hrp) hf.aestronglyMeasurable
  simp only [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hp.le] at hle
  have hfinite : eLpNorm f (ENNReal.ofReal p) μ *
      (μ univ) ^ (1 / r - 1 / p) ≠ ∞ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ univ))
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    toReal_eLpNorm hf.aestronglyMeasurable,
    toReal_eLpNorm hf.aestronglyMeasurable] at hreal
  rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hr).ne' (by simp)
      hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hp).ne' (by simp)
      hf.aestronglyMeasurable] at hreal
  simpa only [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hp.le,
    one_div, measureReal_def] using hreal

/-- Hölder's finite-measure bound includes the exponent-one endpoint. -/
theorem integral_norm_le_measure_rpow_mul_lp_integral (f : X → E)
    {p : ℝ} (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ (μ.real univ) ^ (1 - 1 / p) *
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  have h := integral_norm_rpow_root_le_of_exponent_le f
    (by norm_num : (0 : ℝ) < 1) hp hf
  simpa only [Real.rpow_one, one_div_one, mul_comm] using h

/-- Membership at a real exponent supplies the actual power integrability. -/
theorem integrable_norm_rpow_of_memLp_real (f : X → E)
    {p : ℝ} (hp : 0 ≤ p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    Integrable (fun x => ‖f x‖ ^ p) μ := by
  simpa only [ENNReal.toReal_ofReal hp] using hf.integrable_norm_rpow'

/-- On finite measure, L² membership gives membership at every smaller real exponent. -/
theorem memLp_real_of_memL2 (f : X → E) {p : ℝ}
    (hp : p ≤ 2) (hf : MemLp f 2 μ) : MemLp f (ENNReal.ofReal p) μ := by
  apply hf.mono_exponent
  simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp

/-- The lower real powers of an L² function are genuinely integrable. -/
theorem integrable_norm_rpow_of_memL2 (f : X → E) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₂ : p ≤ 2) (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖f x‖ ^ p) μ :=
  integrable_norm_rpow_of_memLp_real f hp₀ (memLp_real_of_memL2 f hp₂ hf)

/-- The forward L²-to-Lᵖ integral estimate keeps its finite-measure factor. -/
theorem integral_norm_rpow_le_of_memL2 (f : X → E) {p : ℝ}
    (hp : 0 < p) (hp₂ : p ≤ 2) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ p ∂μ) ≤ (μ.real univ) ^ (1 - p / 2) *
      (∫ x, ‖f x‖ ^ 2 ∂μ) ^ (p / 2) := by
  have hf₂ : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hroot := integral_norm_rpow_root_le_of_exponent_le f hp hp₂ hf₂
  have hpower := Real.rpow_le_rpow
    (Real.rpow_nonneg (integral_nonneg fun _x => Real.rpow_nonneg (norm_nonneg _) p) _)
    hroot hp.le
  have hIp : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg fun _x => Real.rpow_nonneg (norm_nonneg _) p
  have hI₂ : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun _x => Real.rpow_nonneg (norm_nonneg _) _
  have hμ : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  simp only [one_div] at hpower
  rw [Real.rpow_inv_rpow hIp hp.ne',
    Real.mul_rpow (Real.rpow_nonneg hI₂ _) (Real.rpow_nonneg hμ _),
    ← Real.rpow_mul hI₂, ← Real.rpow_mul hμ] at hpower
  have hexponent : (p⁻¹ - (2 : ℝ)⁻¹) * p = 1 - p / 2 := by
    field_simp [hp.ne']
  rw [hexponent] at hpower
  have htwo : (2 : ℝ)⁻¹ * p = p / 2 := by ring
  rw [htwo] at hpower
  simpa only [Real.rpow_two, mul_comm] using hpower

end FiniteMeasure

section ColumnNorm

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {n : ℕ}

/-- Columnwise L² data give L² membership for the genuine square-sum norm. -/
theorem memLp_sqrt_sum_norm_sq (D : X → Fin n → E)
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 μ) :
    MemLp (fun x => Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) 2 μ := by
  have hsum : Integrable (fun x => ∑ i : Fin n, ‖D x i‖ ^ 2) μ := by
    apply integrable_finsetSum
    intro i _hi
    exact (hD i).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hmeas : AEStronglyMeasurable
      (fun x => Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hsum.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hnorm (x : X) : ‖Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)‖ =
      Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2) :=
    Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hsquare (x : X) : (Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) ^ 2 =
      ∑ i : Fin n, ‖D x i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _i _hi => sq_nonneg _)
  simpa only [hnorm, hsquare] using hsum

/-- The actual square-sum norm has every lower positive integral power. -/
theorem integrable_sqrt_sum_norm_sq_rpow [IsFiniteMeasure μ]
    (D : X → Fin n → E) {p : ℝ} (hp : 0 ≤ p) (hp₂ : p ≤ 2)
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 μ) :
    Integrable (fun x => (Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) ^ p) μ := by
  have h := integrable_norm_rpow_of_memL2
    (fun x => Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) hp hp₂
    (memLp_sqrt_sum_norm_sq D hD)
  simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using h

/-- The forward lower-power bound uses the square-sum density, not a Pi norm. -/
theorem integral_sqrt_sum_norm_sq_rpow_le [IsFiniteMeasure μ]
    (D : X → Fin n → E) {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 μ) :
    (∫ x, (Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) ^ p ∂μ) ≤
      (μ.real univ) ^ (1 - p / 2) *
        (∫ x, ∑ i : Fin n, ‖D x i‖ ^ 2 ∂μ) ^ (p / 2) := by
  have h := integral_norm_rpow_le_of_memL2
    (fun x => Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) hp hp₂
    (memLp_sqrt_sum_norm_sq D hD)
  have hnorm (x : X) : ‖Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)‖ =
      Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2) :=
    Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hsquare (x : X) : (Real.sqrt (∑ i : Fin n, ‖D x i‖ ^ 2)) ^ 2 =
      ∑ i : Fin n, ‖D x i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _i _hi => sq_nonneg _)
  simpa only [hnorm, hsquare] using h

end ColumnNorm

section SetAverages

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {s : Set X}

/-- The positive finite-set average is controlled by its integral Lᵖ norm. -/
theorem setAverage_norm_le_measure_rpow_mul_lp_integral (f : X → E)
    {p : ℝ} (hp : 1 ≤ p) (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞)
    (hf : MemLp f (ENNReal.ofReal p) (μ.restrict s)) :
    (⨍ x in s, ‖f x‖ ∂μ) ≤ (μ.real s) ^ (-(1 / p)) *
      (∫ x in s, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  letI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
  have hμ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hs
  have hbound := integral_norm_le_measure_rpow_mul_lp_integral f hp hf
  rw [measureReal_restrict_apply_univ] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hμ.le)
  have hscale : (μ.real s)⁻¹ * (μ.real s) ^ (1 - 1 / p) =
      (μ.real s) ^ (-(1 / p)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hμ]
    congr 1
    ring
  rw [← mul_assoc, hscale] at hmul
  simpa only [setAverage_eq, smul_eq_mul] using hmul

/-- Hölder for positive finite-set averages has constant one. -/
theorem setAverage_norm_le_rpow_setAverage_norm_rpow (f : X → E)
    {p : ℝ} (hp : 1 ≤ p) (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞)
    (hf : MemLp f (ENNReal.ofReal p) (μ.restrict s)) :
    (⨍ x in s, ‖f x‖ ∂μ) ≤ (⨍ x in s, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  have hbound := setAverage_norm_le_measure_rpow_mul_lp_integral f hp hs₀ hs hf
  have hmass : 0 ≤ (μ.real s)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hnormp : 0 ≤ ∫ x in s, ‖f x‖ ^ p ∂μ :=
    integral_nonneg fun _x => Real.rpow_nonneg (norm_nonneg _) p
  rw [setAverage_eq μ (fun x => ‖f x‖ ^ p), smul_eq_mul,
    Real.mul_rpow hmass hnormp, ← Real.rpow_neg_eq_inv_rpow]
  exact hbound

/-- Positive Euclidean balls give the same constant-one average bound. -/
theorem ballAverage_norm_le_rpow_ballAverage_norm_rpow
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → E)
    (x : EuclideanSpace ℝ (Fin n)) {r p : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball x r))) :
    (⨍ y in Metric.ball x r, ‖f y‖) ≤
      (⨍ y in Metric.ball x r, ‖f y‖ ^ p) ^ (1 / p) :=
  setAverage_norm_le_rpow_setAverage_norm_rpow f hp
    (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top hf

end SetAverages

end StationaryHarmonicMaps

end
