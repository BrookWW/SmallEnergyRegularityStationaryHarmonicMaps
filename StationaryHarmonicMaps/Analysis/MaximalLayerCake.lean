module

public import StationaryHarmonicMaps.Analysis.DyadicMaximalFinite
public import StationaryHarmonicMaps.Analysis.DyadicMaximalWeakType

/-!
# Actual truncated level integrals for the maximal moment estimate

The level integral arising from the genuine density truncation is
computed using its true positive interval and the ordinary power
antiderivative. The exponent p-2 is integrable at zero exactly when
p is greater than one.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual positive-level truncation integral has its exact p-moment coefficient. -/
theorem lintegral_truncated_rpow_level_eq {p : ℝ} (hp : 1 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(p-2)) *
      (if ENNReal.ofReal (t/2) < ENNReal.ofReal a then ENNReal.ofReal a else 0)) =
      ENNReal.ofReal ((2 : ℝ)^(p-1)/(p-1)) * (ENNReal.ofReal a)^p := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  by_cases ha0 : a=0
  · subst a
    simp only [ENNReal.ofReal_zero,not_lt_zero,ite_false,mul_zero,lintegral_zero,
      ENNReal.zero_rpow_of_pos hp0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hcond (t : ℝ) : ENNReal.ofReal (t/2) < ENNReal.ofReal a ↔ t < 2*a := by
    rw [ENNReal.ofReal_lt_ofReal_iff hap]
    constructor <;> intro H <;> linarith only [H]
  have hEq : (fun t : ℝ => ENNReal.ofReal (t^(p-2)) *
      (if ENNReal.ofReal (t/2) < ENNReal.ofReal a then ENNReal.ofReal a else 0)) =
      (Iio (2*a)).indicator (fun t => ENNReal.ofReal a * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*a
    · rw [if_pos ((hcond t).mpr ht),indicator_of_mem (s := Iio (2*a)) ht,mul_comm]
    · rw [if_neg (fun H => ht ((hcond t).mp H)),indicator_of_notMem (s := Iio (2*a)) ht,mul_zero]
  have hSet : Iio (2*a) ∩ Ioi (0 : ℝ) = Ioo 0 (2*a) := by
    ext t
    simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
    exact and_comm
  have hI : IntegrableOn (fun t : ℝ => t^(p-2)) (Ioo 0 (2*a)) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p-2)
      (a := 0) (b := 2*a)).1.mono_set Ioo_subset_Ioc_self
  have hNN : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (2*a)), 0 ≤ t^(p-2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hReal : (∫ t in Ioo (0 : ℝ) (2*a), t^(p-2)) = (2*a)^(p-1)/(p-1) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ)≤2*a),
      integral_rpow (Or.inl (by linarith : -1 < p-2)),
      show p-2+1=p-1 by ring,Real.zero_rpow (by linarith : p-1≠0),sub_zero]
  have hPow : a*a^(p-1)=a^p := by
    calc
      _ = a^(1 : ℝ)*a^(p-1) := by rw [Real.rpow_one]
      _ = a^(1+(p-1)) := (Real.rpow_add hap _ _).symm
      _ = _ := by congr 1;ring
  have hAlgebra : a*((2*a)^(p-1)/(p-1)) = ((2 : ℝ)^(p-1)/(p-1))*a^p := by
    calc
      _ = ((2 : ℝ)^(p-1)/(p-1))*(a*a^(p-1)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) ha]
        ring
      _ = _ := by rw [hPow]
  have hC : 0 ≤ (2 : ℝ)^(p-1)/(p-1) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_pos.mpr hp).le
  calc
    _ = ENNReal.ofReal a * ∫⁻ t in Ioo (0 : ℝ) (2*a), ENNReal.ofReal (t^(p-2)) := by
      rw [hEq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
        hSet,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal a * ENNReal.ofReal (∫ t in Ioo (0 : ℝ) (2*a), t^(p-2)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hI hNN]
    _ = ENNReal.ofReal (a*((2*a)^(p-1)/(p-1))) := by
      rw [hReal,ENNReal.ofReal_mul ha]
    _ = _ := by
      rw [hAlgebra,ENNReal.ofReal_mul hC,ENNReal.ofReal_rpow_of_nonneg ha hp0.le]

/-- Genuine Tonelli and the actual finite original moment compute the complete truncated-density level integral. -/
theorem lintegral_truncated_density_rpow_eq {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 1 < p) (hfin : (∫⁻ y, (f y)^p) < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(p-2)) *
      ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0) =
      ENNReal.ofReal ((2 : ℝ)^(p-1)/(p-1)) * ∫⁻ y, (f y)^p := by
  classical
  let ν := volume.restrict (Ioi (0 : ℝ))
  let J := fun (t : ℝ) (y : Domain n) => ENNReal.ofReal (t^(p-2)) *
    (if ENNReal.ofReal (t/2) < f y then f y else 0)
  have hTrunc : Measurable (fun z : ℝ × ℝ≥0∞ =>
      if ENNReal.ofReal (z.1/2) < z.2 then z.2 else 0) :=
    Measurable.ite (measurableSet_lt ((measurable_fst.div_const 2).ennreal_ofReal)
      measurable_snd) measurable_snd measurable_const
  have hPair : AEMeasurable (fun z : ℝ × Domain n => (z.1,f z.2)) (ν.prod volume) :=
    measurable_fst.aemeasurable.prodMk hf.comp_snd
  have hWeight : Measurable (fun z : ℝ × Domain n => ENNReal.ofReal (z.1^(p-2))) :=
    (measurable_fst.pow_const (p-2)).ennreal_ofReal
  have hJoint : AEMeasurable (Function.uncurry J) (ν.prod volume) :=
    hWeight.aemeasurable.mul (hTrunc.comp_aemeasurable hPair)
  have hFinite : ∀ᵐ y ∂volume, f y ≠ ∞ :=
    ae_ne_top_of_finite_positive_moment volume f hf (lt_trans zero_lt_one hp) hfin
  calc
    _ = ∫⁻ t, (∫⁻ y, J t y) ∂ν := by
      apply lintegral_congr
      intro t
      exact (lintegral_const_mul' (ENNReal.ofReal (t^(p-2)))
        (fun y => if ENNReal.ofReal (t/2) < f y then f y else 0) ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ y, (∫⁻ t, J t y ∂ν) := lintegral_lintegral_swap hJoint
    _ = ∫⁻ y, ENNReal.ofReal ((2 : ℝ)^(p-1)/(p-1)) * (f y)^p := by
      apply lintegral_congr_ae
      filter_upwards [hFinite] with y hy
      have H := lintegral_truncated_rpow_level_eq hp (a := (f y).toReal) ENNReal.toReal_nonneg
      simpa only [ENNReal.ofReal_toReal hy] using H
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end StationaryHarmonicMaps.Analysis

end
