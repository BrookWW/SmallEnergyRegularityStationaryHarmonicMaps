module

public import StationaryHarmonicMaps.Analysis.GoodLambdaCappedMoment

/-!
# Actual good-lambda moment absorption

A finite weak L1 tail first makes every finite cap have finite moment.
The true level inequality then bounds those cap moments uniformly.
Monotone convergence gives the original extended moment, without any
original F moment hypothesis. Infinite G moment is retained as infinity,
with a strictly positive coefficient. No sigma-finite measure assumption
is needed.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual weak-L1 and good-lambda level data control the original extended s-moment, with no finiteness premise on that moment. -/
theorem lintegral_rpow_le_of_goodLambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F G : X → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (W : ℝ) (hW : 0≤W)
    (hWeak : ∀ t : ℝ,0<t → μ {x | ENNReal.ofReal t<F x}≤ENNReal.ofReal (W/t))
    (s A δ ε : ℝ) (hs : 1<s) (hA : 1≤A) (hδ : 0<δ) (hε : 0≤ε)
    (hAbsorb : ε*A^s<1)
    (hGood : ∀ t : ℝ,0<t →
      μ {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)}≤
        ENNReal.ofReal ε*μ {x | ENNReal.ofReal t<F x}) :
    (∫⁻ x,(F x)^s ∂μ)≤
      ENNReal.ofReal (A^s*δ^(-s)/(1-ε*A^s))*(∫⁻ x,(G x)^s ∂μ) := by
  have hs0 : 0<s := zero_lt_one.trans hs
  have hA0 : 0<A := zero_lt_one.trans_le hA
  have hC : 0<A^s*δ^(-s)/(1-ε*A^s) := div_pos
    (mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hδ _)) (sub_pos.mpr hAbsorb)
  by_cases hGMoment : (∫⁻ x,(G x)^s ∂μ)<∞
  · have hCaps : (⨆ N : ℕ,ENNReal.ofReal ((N : ℝ)+1))=∞ := by
      apply top_unique
      rw [← ENNReal.iSup_natCast]
      refine iSup_le fun N=>le_iSup_of_le N ?_
      rw [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
      exact le_self_add
    have hCapSup (x : X) : (⨆ N : ℕ,min (F x) (ENNReal.ofReal ((N : ℝ)+1)))=F x := by
      rw [← inf_iSup_eq,hCaps,inf_top_eq]
    have hPow (x : X) : (F x)^s=⨆ N : ℕ,(min (F x) (ENNReal.ofReal ((N : ℝ)+1)))^s := by
      have H := (ENNReal.orderIsoRpow s hs0).map_iSup (fun N : ℕ=>min (F x) (ENNReal.ofReal ((N : ℝ)+1)))
      rw [hCapSup x] at H
      exact H
    have hMeas (N : ℕ) : AEMeasurable (fun x=>(min (F x) (ENNReal.ofReal ((N : ℝ)+1)))^s) μ :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hF.min aemeasurable_const)
    have hMono : ∀ᵐ x ∂μ,Monotone (fun N : ℕ=>(min (F x) (ENNReal.ofReal ((N : ℝ)+1)))^s) := by
      apply Eventually.of_forall
      intro x N M hNM
      exact ENNReal.rpow_le_rpow (min_le_min le_rfl (ENNReal.ofReal_le_ofReal
        (add_le_add (Nat.cast_le.mpr hNM) le_rfl))) hs0.le
    calc
      _ = ∫⁻ x,⨆ N : ℕ,(min (F x) (ENNReal.ofReal ((N : ℝ)+1)))^s ∂μ := lintegral_congr hPow
      _ = ⨆ N : ℕ,∫⁻ x,(min (F x) (ENNReal.ofReal ((N : ℝ)+1)))^s ∂μ := lintegral_iSup' hMeas hMono
      _ ≤ _ := iSup_le fun N=>lintegral_min_rpow_le_of_goodLambda μ F G hF hG W hW hWeak
        s A δ ε hs hA hδ hε hAbsorb hGood hGMoment ((N : ℝ)+1) (by positivity)
  · have hGTop : (∫⁻ x,(G x)^s ∂μ)=∞ := top_unique (not_lt.mp hGMoment)
    rw [hGTop,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    exact le_top

/-- A finite original G moment and actual weak-L1/good-lambda tails produce a finite original F moment and genuine AE finiteness. -/
theorem finite_rpow_moment_of_goodLambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F G : X → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (W : ℝ) (hW : 0≤W)
    (hWeak : ∀ t : ℝ,0<t → μ {x | ENNReal.ofReal t<F x}≤ENNReal.ofReal (W/t))
    (s A δ ε : ℝ) (hs : 1<s) (hA : 1≤A) (hδ : 0<δ) (hε : 0≤ε)
    (hAbsorb : ε*A^s<1)
    (hGood : ∀ t : ℝ,0<t →
      μ {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)}≤
        ENNReal.ofReal ε*μ {x | ENNReal.ofReal t<F x})
    (hGMoment : (∫⁻ x,(G x)^s ∂μ)<∞) :
    (∫⁻ x,(F x)^s ∂μ)≤
        ENNReal.ofReal (A^s*δ^(-s)/(1-ε*A^s))*(∫⁻ x,(G x)^s ∂μ) ∧
      (∫⁻ x,(F x)^s ∂μ)<∞ ∧ (∀ᵐ x ∂μ,F x≠∞) := by
  have hBound := lintegral_rpow_le_of_goodLambda μ F G hF hG W hW hWeak
    s A δ ε hs hA hδ hε hAbsorb hGood
  have hFinite := hBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGMoment)
  exact ⟨hBound,hFinite,ae_ne_top_of_finite_positive_moment μ F hF (zero_lt_one.trans hs) hFinite⟩

end StationaryHarmonicMaps.Analysis

end
