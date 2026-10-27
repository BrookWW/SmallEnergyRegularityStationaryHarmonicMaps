module

public import StationaryHarmonicMaps.Analysis.AbsolutelyIntegrableSeries

/-! # Actual real summability from the original finite extended coefficient bound -/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- An actual finite extended bound for the original nonnegative coefficients produces genuine real summability and the same real sum bound. -/
theorem summable_nonnegative_coefficients_of_extended_bound {I : Type*}
    (a : I → ℝ) (ha : ∀ i,0≤a i) (M : ℝ) (hM : 0≤M) (E : ℝ≥0∞) (hE : E≠∞)
    (hBound : (∑' i,ENNReal.ofReal (a i))≤ENNReal.ofReal M*E) :
    Summable a ∧ (∑' i,a i)≤M*E.toReal := by
  let b : I → NNReal := fun i=>NNReal.mk (a i) (ha i)
  have hFinite : (∑' i,ENNReal.ofReal (a i))≠∞ :=
    (hBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hE))).ne
  have hFiniteB : (∑' i,((b i : NNReal) : ℝ≥0∞))≠∞ := by
    simpa only [b,ENNReal.ofReal_eq_coe_nnreal (ha _)] using hFinite
  have hSumB : Summable b := ENNReal.tsum_coe_ne_top_iff_summable.mp hFiniteB
  have hSum : Summable a := by simpa only [b,NNReal.coe_mk] using NNReal.summable_coe.mpr hSumB
  refine ⟨hSum,?_⟩
  have H := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hE)).ne hBound
  rw [← ENNReal.ofReal_tsum_of_nonneg ha hSum,ENNReal.toReal_ofReal (tsum_nonneg ha),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hM] at H
  exact H

end StationaryHarmonicMaps.Analysis

end
