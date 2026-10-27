module

public import StationaryHarmonicMaps.Geometry.UnitInversion
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Actual L2 transport by the Kelvin--Piola reflection

The full Jacobian formula transports the literal exterior field to the
original punctured unit ball. Its exact weight is |x|^(2n-4), bounded by
one when n is at least two. Measurability and actual L2 membership are
proved for the exterior field; no exterior-energy estimate is assumed.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal RealInnerProductSpace

namespace StationaryHarmonicMaps.Analysis

/-- The actual unit inversion is Borel measurable on its whole carrier. -/
theorem measurable_unit_inversion (n : ℕ) :
    Measurable (inversion (0 : Domain n) 1) := by
  have H : Measurable (fun x : Domain n => (1/‖x‖)^2 • x) :=
    ((measurable_const.div measurable_id.norm).pow_const 2).smul measurable_id
  change Measurable (fun x : Domain n => inversion 0 1 x)
  simpa only [inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero] using H

private theorem radial_reflection_apply {n : ℕ} (x z : Domain n) :
    (ℝ ∙ x)ᗮ.reflection z=z-(2*(inner ℝ x z)/(‖x‖^2)) • x := by
  rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply,neg_sub]
  simp only [two_smul ℕ,mul_div_assoc,mul_smul,two_smul ℝ,RCLike.ofReal_real_eq_id,id_eq]

/-- A genuine measurable original vector field gives a genuine measurable radial reflection. -/
theorem measurable_radial_reflection_field {n : ℕ} (Z : Domain n → Domain n) (hZ : Measurable Z) :
    Measurable (fun x => (ℝ ∙ x)ᗮ.reflection (Z x)) := by
  simp only [radial_reflection_apply]
  exact hZ.sub (((measurable_const.mul (measurable_id.inner hZ)).div
    (measurable_id.norm.pow_const 2)).smul measurable_id)

/-- The literal exterior Piola field has actual L2 membership and no more energy than the original interior field. -/
theorem kelvin_piola_L2_exterior {n : ℕ} (hn : 2≤n)
    (Z : Domain n → Domain n) (hZm : Measurable Z)
    (hZ : MemLp Z 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) :
    let W := fun x : Domain n => -((‖x‖^(2*n-2))⁻¹) •
      (ℝ ∙ x)ᗮ.reflection (Z (inversion (0 : Domain n) 1 x))
    MemLp W 2 (volume.restrict {x : Domain n | 1<‖x‖}) ∧
      (∫ x in {x : Domain n | 1<‖x‖},‖W x‖^2) ≤
        ∫ x in Metric.ball (0 : Domain n) 1,‖Z x‖^2 := by
  intro W
  let I := inversion (0 : Domain n) 1
  let B : Set (Domain n) := Metric.ball (0 : Domain n) 1
  let D : Set (Domain n) := B\{0}
  let O : Set (Domain n) := {x : Domain n | 1<‖x‖}
  have hD : MeasurableSet D := measurableSet_ball.diff (measurableSet_singleton _)
  have hD0 (x : Domain n) (hx : x∈D) : x≠0 := by simpa only [mem_singleton_iff] using hx.2
  have hID : I '' D=O := unit_inversion_image_punctured_ball
  have hDeriv (x : Domain n) (hx : x∈D) : HasFDerivWithinAt I (fderiv ℝ I x) D x :=
    (hasFDerivAt_unit_inversion x (hD0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hIinj : InjOn I D := (inversion_injective (0 : Domain n) (by norm_num : (1 : ℝ)≠0)).injOn
  have hWm : Measurable W :=
    ((measurable_id.norm.pow_const (2*n-2)).inv.neg).smul
      (measurable_radial_reflection_field (fun x => Z (I x)) (hZm.comp (measurable_unit_inversion n)))
  have hPoint (x : Domain n) (hx : x∈D) :
      |(fderiv ℝ I x).det| *‖W (I x)‖^2=‖x‖^(2*n-4)*‖Z x‖^2 := by
    simpa only [W,I,inversion_inversion _ (by norm_num : (1 : ℝ)≠0)] using
      unit_inversion_piola_energy_density hn x (Z x) (hD0 x hx)
  have hChange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hDeriv hIinj
    (fun x => ENNReal.ofReal (‖W x‖^2))
  rw [hID] at hChange
  have hLin : (∫⁻ x in O,ENNReal.ofReal (‖W x‖^2)) ≤
      ∫⁻ x in B,ENNReal.ofReal (‖Z x‖^2) := by
    calc
      _ = ∫⁻ x in D,ENNReal.ofReal (|(fderiv ℝ I x).det| *‖W (I x)‖^2) := by
        rw [hChange]
        apply lintegral_congr
        intro x
        exact (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ = ∫⁻ x in D,ENNReal.ofReal (‖x‖^(2*n-4)*‖Z x‖^2) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hD] with x hx
        rw [hPoint x hx]
      _ ≤ ∫⁻ x in D,ENNReal.ofReal (‖Z x‖^2) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hD] with x hx
        apply ENNReal.ofReal_le_ofReal
        have hNorm : ‖x‖≤1 := (show ‖x‖<1 by simpa only [B,Metric.mem_ball,dist_zero_right] using hx.1).le
        exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hNorm) (sq_nonneg _)).trans_eq (one_mul _)
      _ ≤ _ := lintegral_mono_set sdiff_subset
  have hZI : IntegrableOn (fun x => ‖Z x‖^2) B volume := hZ.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hFinite : (∫⁻ x in B,ENNReal.ofReal (‖Z x‖^2)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg ‖Z x‖)).mp hZI.hasFiniteIntegral
  have hWI : IntegrableOn (fun x => ‖W x‖^2) O volume :=
    ⟨(hWm.norm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg ‖W x‖)).mpr (hLin.trans_lt hFinite)⟩
  refine ⟨(memLp_two_iff_integrable_sq_norm hWm.aestronglyMeasurable).mpr hWI,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hWI (Eventually.of_forall fun x => sq_nonneg ‖W x‖),
    ← ofReal_integral_eq_lintegral_ofReal hZI (Eventually.of_forall fun x => sq_nonneg ‖Z x‖)] at hLin
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => sq_nonneg ‖Z x‖)).mp hLin

end StationaryHarmonicMaps.Analysis

end
