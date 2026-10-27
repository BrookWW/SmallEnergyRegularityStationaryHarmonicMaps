module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Finite capped moments from an actual weak L1 tail

For an extended nonnegative measurable function, a finite weak L1 tail
makes every positive finite cap have a finite s-moment when s is greater
than one. The cap is finite before its real representative is used. The
positive-level integral has exponent s-2, which is integrable at zero.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- An actual finite weak-L1 tail gives a genuinely finite moment of every literal cap, without a moment assumption on the original function. -/
theorem lintegral_min_rpow_lt_top_of_weak_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ)
    (W : ℝ) (hW : 0≤W)
    (hWeak : ∀ ℓ : ℝ,0<ℓ → μ {x | ENNReal.ofReal ℓ<F x}≤ENNReal.ofReal (W/ℓ))
    {s : ℝ} (hs : 1<s) (T : ℝ) (hT : 0<T) :
    (∫⁻ x,(min (F x) (ENNReal.ofReal T))^s ∂μ)<∞ := by
  let H := fun x=>min (F x) (ENNReal.ofReal T)
  have hHFinite (x : X) : H x≠∞ := ne_of_lt ((min_le_right _ _).trans_lt ENNReal.ofReal_lt_top)
  let f := fun x=>(H x).toReal
  have hf : AEMeasurable f μ := (hF.min aemeasurable_const).ennreal_toReal
  have hf0 (x : X) : 0≤f x := ENNReal.toReal_nonneg
  have hfT (x : X) : f x≤T := by
    have Hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right (F x) (ENNReal.ofReal T))
    simpa only [ENNReal.toReal_ofReal hT.le] using Hle
  have hs0 : 0<s := zero_lt_one.trans hs
  have hMoment : (∫⁻ x,(H x)^s ∂μ)=∫⁻ x,ENNReal.ofReal ((f x)^s) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (hf0 x) hs0.le,ENNReal.ofReal_toReal (hHFinite x)]
  have hLevel (ℓ : ℝ) (hℓ : 0<ℓ) :
      μ {x | ℓ<f x}*ENNReal.ofReal (ℓ^(s-1))≤
        (Iio T).indicator (fun t=>ENNReal.ofReal W*ENNReal.ofReal (t^(s-2))) ℓ := by
    by_cases hℓT : ℓ<T
    · rw [indicator_of_mem (s:=Iio T) hℓT]
      have hSet : {x | ℓ<f x}⊆{x | ENNReal.ofReal ℓ<F x} := by
        intro x hx
        have Hlt : ENNReal.ofReal ℓ<H x := (ENNReal.ofReal_lt_iff_lt_toReal hℓ.le (hHFinite x)).mpr hx
        exact Hlt.trans_le (min_le_left _ _)
      have hPow : ℓ^(s-1)=ℓ*ℓ^(s-2) := by
        calc
          _ = ℓ^((1 : ℝ)+(s-2)) := by congr 1;ring
          _ = _ := by rw [Real.rpow_add hℓ,Real.rpow_one]
      calc
        _ ≤ ENNReal.ofReal (W/ℓ)*ENNReal.ofReal (ℓ^(s-1)) :=
          mul_le_mul_of_nonneg_right ((measure_mono hSet).trans (hWeak ℓ hℓ)) zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (div_nonneg hW hℓ.le),← ENNReal.ofReal_mul hW]
          congr 1
          rw [hPow]
          field_simp [hℓ.ne']
    · have hEmpty : {x | ℓ<f x}=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact not_lt_of_ge ((hfT x).trans (le_of_not_gt hℓT)) hx
      rw [hEmpty,measure_empty,zero_mul,indicator_of_notMem (s:=Iio T) hℓT]
  have hPowerI : IntegrableOn (fun t : ℝ=>t^(s-2)) (Ioo 0 T) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<s-2)
      (a:=0) (b:=T)).1.mono_set Ioo_subset_Ioc_self
  have hPowerNN : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T),0≤t^(s-2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hPowerFinite : (∫⁻ t in Ioo (0 : ℝ) T,ENNReal.ofReal (t^(s-2)))<∞ :=
    (hasFiniteIntegral_iff_ofReal hPowerNN).mp hPowerI.hasFiniteIntegral
  have hMajorant : (∫⁻ t in Ioi (0 : ℝ),
      (Iio T).indicator (fun t=>ENNReal.ofReal W*ENNReal.ofReal (t^(s-2))) t)<∞ := by
    rw [lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
      show Iio T∩Ioi (0 : ℝ)=Ioo 0 T from by ext t;simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo];exact and_comm,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPowerFinite
  have hLayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hf0) hf hs0
  rw [hMoment,hLayer]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((lintegral_mono_ae (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with ℓ hℓ;exact hLevel ℓ hℓ)).trans_lt hMajorant)

end StationaryHarmonicMaps.Analysis

end
