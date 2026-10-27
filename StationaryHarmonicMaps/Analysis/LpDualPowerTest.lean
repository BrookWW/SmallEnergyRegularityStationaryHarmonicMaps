module

public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual power-duality tests from original L2 data

The literal norm-power vector is defined at every point by ordinary real
powers and scalar multiplication. Its identities include the zero vector.
Finite measure supplies actual L2 and conjugate-exponent membership.
-/

public section

open MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- The true power-duality vector has the norm, pairing and conjugate-power identities, including at zero. -/
theorem dual_power_vector_identities {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℝ) (hp : 1<p) (v : E) :
    let g := ‖v‖^(p-2) • v
    ‖g‖=‖v‖^(p-1) ∧ inner ℝ v g=‖v‖^p ∧ ‖g‖^(p/(p-1))=‖v‖^p := by
  dsimp only
  have hp0 : 0<p := by linarith
  have hpm : 0<p-1 := by linarith
  have hNorm : ‖‖v‖^(p-2) • v‖=‖v‖^(p-1) := by
    by_cases hv : v=0
    · simp only [hv,norm_zero,smul_zero,Real.zero_rpow hpm.ne']
    · have hvNorm : 0<‖v‖ := norm_pos_iff.mpr hv
      calc
        _ = ‖v‖^(p-2)*‖v‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hvNorm.le _)]
        _ = ‖v‖^(p-2)*‖v‖^(1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖v‖^((p-2)+1) := (Real.rpow_add hvNorm _ _).symm
        _ = _ := by congr 1;ring
  refine ⟨hNorm,?_,?_⟩
  · by_cases hv : v=0
    · simp only [hv,norm_zero,smul_zero,inner_zero_left,Real.zero_rpow hp0.ne']
    · have hvNorm : 0<‖v‖ := norm_pos_iff.mpr hv
      rw [inner_smul_right,real_inner_self_eq_norm_sq,← Real.rpow_two,← Real.rpow_add hvNorm]
      congr 1
      ring
  · rw [hNorm,← Real.rpow_mul (norm_nonneg v)]
    congr 1
    field_simp [hpm.ne']

/-- For finite measure and 1<p<2, the actual duality test belongs both to L2 and to the conjugate exponent. -/
theorem dual_power_test_memLp {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (f : X → E) (hf : MemLp f 2 μ) :
    let G := fun x => ‖f x‖^(p-2) • f x
    MemLp G 2 μ ∧ MemLp G (ENNReal.ofReal (p/(p-1))) μ := by
  let G := fun x => ‖f x‖^(p-2) • f x
  have hp0 : 0<p := by linarith
  have hpm : 0<p-1 := by linarith
  have hr : 0<p/(p-1) := div_pos hp0 hpm
  have hG : AEStronglyMeasurable G μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (p-2)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  have hBound (x : X) : ‖G x‖≤1+‖f x‖ := by
    rw [(dual_power_vector_identities p hpOne (f x)).1]
    by_cases hx : ‖f x‖≤1
    · have H := Real.rpow_le_one (norm_nonneg (f x)) hx hpm.le
      linarith only [H,norm_nonneg (f x)]
    · have H := Real.rpow_le_rpow_of_exponent_le (not_le.mp hx).le
        (show p-1≤(1 : ℝ) by linarith only [hpTwo])
      rw [Real.rpow_one] at H
      linarith only [H]
  have hConst : MemLp (fun _ : X => (1 : ℝ)) 2 μ := memLp_const 1
  have hNormF : MemLp (fun x => ‖f x‖) 2 μ := hf.norm
  have hMajor : MemLp (fun x => (1 : ℝ)+‖f x‖) 2 μ := hConst.add hNormF
  have hGTwo : MemLp G 2 μ := hMajor.of_le hG (Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (by positivity : 0≤(1 : ℝ)+‖f x‖)]
    exact hBound x)
  have hFp : MemLp f (ENNReal.ofReal p) μ := memLp_real_of_memL2 f hpTwo.le hf
  have hIntP : Integrable (fun x => ‖f x‖^p) μ := integrable_norm_rpow_of_memLp_real f hp0.le hFp
  have hIntG : Integrable (fun x => ‖G x‖^(p/(p-1))) μ :=
    hIntP.congr (Eventually.of_forall fun x => (dual_power_vector_identities p hpOne (f x)).2.2.symm)
  have hrZero : ENNReal.ofReal (p/(p-1))≠0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hOne : MemLp (fun x => ‖G x‖^(p/(p-1))) 1 μ := memLp_one_iff_integrable.mpr hIntG
  have hRatio : MemLp (fun x => ‖G x‖^(ENNReal.ofReal (p/(p-1))).toReal)
      (ENNReal.ofReal (p/(p-1))/ENNReal.ofReal (p/(p-1))) μ := by
    simpa only [ENNReal.toReal_ofReal hr.le,ENNReal.div_self hrZero ENNReal.ofReal_ne_top] using hOne
  exact ⟨hGTwo,(memLp_norm_rpow_iff (p := ENNReal.ofReal (p/(p-1)))
    (q := ENNReal.ofReal (p/(p-1))) hG hrZero ENNReal.ofReal_ne_top).mp hRatio⟩

end StationaryHarmonicMaps.Analysis
end
