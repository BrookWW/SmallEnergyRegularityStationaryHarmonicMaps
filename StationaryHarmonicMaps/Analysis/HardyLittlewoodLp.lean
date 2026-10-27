module

public import StationaryHarmonicMaps.Analysis.MaximalLayerCake

/-!
# Actual strong moments of the extended dyadic maximal function

The genuine truncated Vitali bound and the actual positive-level
integral give a uniform p-moment for every two-sided finite window.
Monotone convergence recovers the literal extended full supremum.
Its almost-everywhere finiteness is proved only after the moment bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem maximal_level_weight_identity {A p t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    ENNReal.ofReal (A/(t/2)) * ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal (2*A) * ENNReal.ofReal (t^(p-2)) := by
  have hPow : t^(p-1)=t*t^(p-2) := by
    calc
      _ = t^((1 : ℝ)+(p-2)) := by congr 1;ring
      _ = t^(1 : ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [← ENNReal.ofReal_mul (div_nonneg hA (half_pos ht).le),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ)≤2) hA)]
  congr 1
  rw [hPow]
  field_simp [ht.ne']

/-- Actual p-moments of finite windows obey a uniform strong bound supplied by genuine truncation and layer cake. -/
theorem lintegral_dyadicBallMaximalWindow_rpow_le {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 1 < p) (hfin : (∫⁻ y, (f y)^p) < ∞) (N : ℕ) :
    (∫⁻ x, (dyadicBallMaximalWindow f N x)^p) ≤
      ENNReal.ofReal (((2 : ℝ)^p*p/(p-1))*(5 : ℝ)^n) * ∫⁻ y, (f y)^p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let g := fun x => (dyadicBallMaximalWindow f N x).toReal
  have hFinite (x : Domain n) : dyadicBallMaximalWindow f N x ≠ ∞ :=
    dyadicBallMaximalWindow_ne_top_of_moment f hp.le hfin N x
  have hg : Measurable g := (measurable_dyadicBallMaximalWindow f hf N).ennreal_toReal
  have hMom : (∫⁻ x, (dyadicBallMaximalWindow f N x)^p) =
      ∫⁻ x, ENNReal.ofReal ((g x)^p) := by
    apply lintegral_congr
    intro x
    dsimp only [g]
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,
      ENNReal.ofReal_toReal (hFinite x)]
  have hTail (t : ℝ) (ht : 0 < t) : volume {x | t < g x} ≤
      ENNReal.ofReal ((5 : ℝ)^n/(t/2)) *
        ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0 := by
    have hSet : {x | t < g x} = {x | ENNReal.ofReal t < dyadicBallMaximalWindow f N x} := by
      ext x
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hFinite x)).symm
    have H := dyadicBallMaximalWindow_truncated_weak_one f N (t/2) (half_pos ht)
    rw [show 2*(t/2)=t by ring,← hSet] at H
    exact H
  have hPoint : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      volume {x | t < g x} * ENNReal.ofReal (t^(p-1)) ≤
        ENNReal.ofReal (2*(5 : ℝ)^n) * (ENNReal.ofReal (t^(p-2)) *
          ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ (ENNReal.ofReal ((5 : ℝ)^n/(t/2)) *
          ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0) * ENNReal.ofReal (t^(p-1)) :=
        mul_le_mul_of_nonneg_right (hTail t ht) zero_le
      _ = (ENNReal.ofReal ((5 : ℝ)^n/(t/2)) * ENNReal.ofReal (t^(p-1))) *
          ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0 := by ac_rfl
      _ = _ := by rw [maximal_level_weight_identity (pow_nonneg (by norm_num : (0 : ℝ)≤5) n) ht,mul_assoc]
  have hLayer := lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg : ∀ᵐ x ∂volume, 0 ≤ g x)
    hg.aemeasurable hp0
  have hTwo : 2*(2 : ℝ)^(p-1)=(2 : ℝ)^p := by
    calc
      _ = (2 : ℝ)^(1 : ℝ)*(2 : ℝ)^(p-1) := by rw [Real.rpow_one]
      _ = (2 : ℝ)^((1 : ℝ)+(p-1)) := (Real.rpow_add (by norm_num) _ _).symm
      _ = _ := by congr 1;ring
  have hCoeff : ENNReal.ofReal p * ENNReal.ofReal (2*(5 : ℝ)^n) *
      ENNReal.ofReal ((2 : ℝ)^(p-1)/(p-1)) =
        ENNReal.ofReal (((2 : ℝ)^p*p/(p-1))*(5 : ℝ)^n) := by
    rw [← ENNReal.ofReal_mul hp0.le,← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = (2*(2 : ℝ)^(p-1))*(p/(p-1))*(5 : ℝ)^n := by ring
      _ = _ := by rw [hTwo];ring
  calc
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        volume {x | t < g x} * ENNReal.ofReal (t^(p-1)) := hMom.trans hLayer
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (2*(5 : ℝ)^n) * (ENNReal.ofReal (t^(p-2)) *
          ∫⁻ y, if ENNReal.ofReal (t/2) < f y then f y else 0) :=
      mul_le_mul_of_nonneg_left (lintegral_mono_ae hPoint) zero_le
    _ = ENNReal.ofReal p * (ENNReal.ofReal (2*(5 : ℝ)^n) *
        (ENNReal.ofReal ((2 : ℝ)^(p-1)/(p-1)) * ∫⁻ y, (f y)^p)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_truncated_density_rpow_eq f hf hp hfin]
    _ = _ := by rw [← mul_assoc,← mul_assoc,hCoeff]

/-- Monotone convergence gives the genuine full extended dyadic maximal p-moment bound. -/
theorem lintegral_dyadicBallMaximal_rpow_le {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 1 < p) (hfin : (∫⁻ y, (f y)^p) < ∞) :
    (∫⁻ x, (dyadicBallMaximal f x)^p) ≤
      ENNReal.ofReal (((2 : ℝ)^p*p/(p-1))*(5 : ℝ)^n) * ∫⁻ y, (f y)^p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hPow (x : Domain n) : (dyadicBallMaximal f x)^p =
      ⨆ N : ℕ, (dyadicBallMaximalWindow f N x)^p := by
    rw [← iSup_dyadicBallMaximalWindow f x]
    exact (ENNReal.orderIsoRpow p hp0).map_iSup (fun N => dyadicBallMaximalWindow f N x)
  calc
    _ = ∫⁻ x, ⨆ N : ℕ, (dyadicBallMaximalWindow f N x)^p := lintegral_congr hPow
    _ = ⨆ N : ℕ, ∫⁻ x, (dyadicBallMaximalWindow f N x)^p :=
      lintegral_iSup (fun N => ENNReal.continuous_rpow_const.measurable.comp
        (measurable_dyadicBallMaximalWindow f hf N))
        (fun N M hNM x => ENNReal.rpow_le_rpow (dyadicBallMaximalWindow_monotone f x hNM) hp0.le)
    _ ≤ _ := iSup_le (fun N => lintegral_dyadicBallMaximalWindow_rpow_le f hf hp hfin N)

/-- The literal extended maximal function has actual measurable finite p-moment, genuine AE finiteness and all-real-radius domination. -/
theorem dyadicBallMaximal_strongLp_control {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 1 < p) (hfin : (∫⁻ y, (f y)^p) < ∞) :
    Measurable (dyadicBallMaximal f) ∧
      (∫⁻ x, (dyadicBallMaximal f x)^p) ≤
        ENNReal.ofReal (((2 : ℝ)^p*p/(p-1))*(5 : ℝ)^n) * (∫⁻ y, (f y)^p) ∧
      (∫⁻ x, (dyadicBallMaximal f x)^p) < ∞ ∧
      (∀ᵐ x ∂volume, dyadicBallMaximal f x ≠ ∞) ∧
      ∀ (x : Domain n) (r : PositiveRadius), centeredBallAverageENN f x r ≤
        ENNReal.ofReal ((2 : ℝ)^n)*dyadicBallMaximal f x := by
  have hM := measurable_dyadicBallMaximal f hf
  have hBound := lintegral_dyadicBallMaximal_rpow_le f hf hp hfin
  have hFinite := hBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  exact ⟨hM,hBound,hFinite,ae_ne_top_of_finite_positive_moment volume _ hM.aemeasurable
    (lt_trans zero_lt_one hp) hFinite,centeredBallAverageENN_le_dyadicBallMaximal f⟩

end StationaryHarmonicMaps.Analysis

end
