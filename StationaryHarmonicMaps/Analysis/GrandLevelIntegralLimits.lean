module

public import StationaryHarmonicMaps.Analysis.SmoothGrandMaximalMeasurability
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Actual small-level and large-level integrals of finite grand data

The original measurable extended function is used throughout. Dominated
convergence controls its lower caps and upper tails. Large-level mass is
bounded by that same actual upper tail, with no pointwise real conversion.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual finite extended integral makes the integrals of small constant caps tend to zero. -/
theorem tendsto_lintegral_min_ofReal_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (hJ : Measurable J)
    (hFin : (∫⁻ x,J x ∂μ)≠∞) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x,min (J x) (ENNReal.ofReal (t k)) ∂μ) atTop (𝓝 0) := by
  have hPoint (x : X) : Tendsto (fun k=>min (J x) (ENNReal.ofReal (t k))) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x := J x)).min ((ENNReal.continuous_ofReal.tendsto 0).comp ht)
    simpa only [Function.comp_apply,ENNReal.ofReal_zero,min_zero] using H
  have H := tendsto_lintegral_of_dominated_convergence J
    (fun k=>hJ.min measurable_const)
    (fun _=>Eventually.of_forall fun _=>min_le_left _ _) hFin (Eventually.of_forall hPoint)
  simpa only [lintegral_zero] using H

/-- Actual finite extended integral makes the original upper tails tend to zero as the real level tends to infinity. -/
theorem tendsto_lintegral_upper_level_tail_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (hJ : Measurable J)
    (hFin : (∫⁻ x,J x ∂μ)≠∞) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun k => ∫⁻ x,if ENNReal.ofReal (t k)<J x then J x else 0 ∂μ)
      atTop (𝓝 0) := by
  have hFinite : ∀ᵐ x ∂μ,J x≠∞ := (ae_lt_top' hJ.aemeasurable hFin).mono fun _ hx=>hx.ne
  have hPoint : ∀ᵐ x ∂μ,Tendsto
      (fun k=>if ENNReal.ofReal (t k)<J x then J x else 0) atTop (𝓝 0) := by
    filter_upwards [hFinite] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (eventually_ge_atTop ((J x).toReal))] with k hk
    have hBound : J x≤ENNReal.ofReal (t k) := by
      rw [← ENNReal.ofReal_toReal hx]
      exact ENNReal.ofReal_le_ofReal hk
    exact (if_neg (not_lt.mpr hBound)).symm
  have hMeas (k : ℕ) : Measurable (fun x=>if ENNReal.ofReal (t k)<J x then J x else 0) :=
    hJ.ite (measurableSet_lt measurable_const hJ) measurable_const
  have hBound (k : ℕ) : (fun x=>if ENNReal.ofReal (t k)<J x then J x else 0)≤ᵐ[μ]J :=
    Eventually.of_forall fun x=>by
      dsimp only
      split_ifs <;> simp only [le_refl,zero_le]
  have H := tendsto_lintegral_of_dominated_convergence J hMeas hBound hFin hPoint
  simpa only [lintegral_zero] using H

/-- The original large superlevel mass times its level tends to zero, by the genuine upper-tail bound. -/
theorem tendsto_level_mul_superlevel_measure_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (hJ : Measurable J)
    (hFin : (∫⁻ x,J x ∂μ)≠∞) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun k=>ENNReal.ofReal (t k)*μ {x | ENNReal.ofReal (t k)<J x})
      atTop (𝓝 0) := by
  have hBound (k : ℕ) : ENNReal.ofReal (t k)*μ {x | ENNReal.ofReal (t k)<J x} ≤
      ∫⁻ x,if ENNReal.ofReal (t k)<J x then J x else 0 ∂μ := by
    let S := {x | ENNReal.ofReal (t k)<J x}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hJ
    have hEq : ENNReal.ofReal (t k)*μ S =
        ∫⁻ x,if ENNReal.ofReal (t k)<J x then ENNReal.ofReal (t k) else 0 ∂μ := by
      have hFun : (fun x=>if ENNReal.ofReal (t k)<J x then ENNReal.ofReal (t k) else 0)=
          S.indicator (fun _=>ENNReal.ofReal (t k)) := by
        funext x
        by_cases hx : ENNReal.ofReal (t k)<J x
        · rw [if_pos hx,indicator_of_mem (show x∈S from hx)]
        · rw [if_neg hx,indicator_of_notMem (show x∉S from hx)]
      rw [hFun,lintegral_indicator hS,lintegral_const,Measure.restrict_apply_univ]
    rw [hEq]
    apply lintegral_mono
    intro x
    dsimp only
    split_ifs with hx
    · exact hx.le
    · exact le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_lintegral_upper_level_tail_zero μ J hJ hFin t ht) (fun _=>zero_le) hBound

end StationaryHarmonicMaps.Analysis

end
