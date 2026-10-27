module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Actual cap and tail bounds from the original good-part identities -/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original AE value control and the actual inside/outside good-part properties give genuine extended cap and error-tail bounds for the same good function. -/
theorem ae_good_part_cap_and_error_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (f g : X → ℝ)
    (C D L : ℝ) (hC : 0≤C) (hL : 0≤L)
    (hValue : ∀ᵐ x ∂μ,ENNReal.ofReal |f x|≤ENNReal.ofReal C*J x)
    (hInside : ∀ x,ENNReal.ofReal L<J x → |g x|≤D*L)
    (hOutside : ∀ x,J x≤ENNReal.ofReal L → g x=f x) :
    let A := max C D
    (∀ᵐ x ∂μ,ENNReal.ofReal |g x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L)) ∧
      (∀ᵐ x ∂μ,ENNReal.ofReal |f x-g x|≤ENNReal.ofReal (2*A)*
        ({y | ENNReal.ofReal L<J y}.indicator J x)) := by
  intro A
  have hA : 0≤A := hC.trans (le_max_left _ _)
  have hCap : ∀ᵐ x ∂μ,ENNReal.ofReal |g x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L) := by
    filter_upwards [hValue] with x hxValue
    by_cases hx : ENNReal.ofReal L<J x
    · rw [min_eq_right hx.le]
      calc
        _ ≤ ENNReal.ofReal (D*L) := ENNReal.ofReal_le_ofReal (hInside x hx)
        _ ≤ ENNReal.ofReal (A*L) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hL)
        _ = _ := ENNReal.ofReal_mul hA
    · rw [min_eq_left (le_of_not_gt hx),hOutside x (le_of_not_gt hx)]
      exact hxValue.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
  refine ⟨hCap,?_⟩
  filter_upwards [hValue,hCap] with x hxValue hxCap
  by_cases hx : ENNReal.ofReal L<J x
  · rw [indicator_of_mem (s := {y : X | ENNReal.ofReal L<J y}) hx]
    have hAValue : ENNReal.ofReal |f x|≤ENNReal.ofReal A*J x := hxValue.trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
    have hAGood : ENNReal.ofReal |g x|≤ENNReal.ofReal A*J x := hxCap.trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le)
    calc
      _ ≤ ENNReal.ofReal (|f x|+|g x|) := ENNReal.ofReal_le_ofReal (abs_sub _ _)
      _ = ENNReal.ofReal |f x|+ENNReal.ofReal |g x| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ ENNReal.ofReal A*J x+ENNReal.ofReal A*J x := add_le_add hAValue hAGood
      _ = ENNReal.ofReal (2*A)*J x := by rw [show 2*A=A+A by ring,ENNReal.ofReal_add hA hA,add_mul]
  · rw [hOutside x (le_of_not_gt hx),sub_self,abs_zero,ENNReal.ofReal_zero,indicator_of_notMem (s := {y : X | ENNReal.ofReal L<J y}) hx,mul_zero]

end StationaryHarmonicMaps.Analysis

end
