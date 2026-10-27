module

public import StationaryHarmonicMaps.Analysis.KelvinPiolaL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual Piola test pairing under unit inversion

The true radial reflection is unchanged by inversion. The exact Jacobian
and reflection formula transfer an exterior compact-test pairing to the
negative reflected derivative pairing on the original ball. L2 products
supply actual integrability before either integral identity is used.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff RealInnerProductSpace

namespace StationaryHarmonicMaps.Analysis

/-- Inversion preserves the actual radial reflection at every nonzero point. -/
theorem unit_inversion_radial_reflection_eq {n : ℕ} (x : Domain n) (hx : x≠0) :
    (ℝ ∙ inversion (0 : Domain n) 1 x)ᗮ.reflection=(ℝ ∙ x)ᗮ.reflection := by
  have hI : inversion (0 : Domain n) 1 x=(‖x‖^2)⁻¹ • x := by
    simp only [inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero,one_div,inv_pow]
  have hSpan : ℝ ∙ inversion (0 : Domain n) 1 x=ℝ ∙ x := by
    rw [hI]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))) x
  exact congrArg (fun K : Submodule ℝ (Domain n) => Kᗮ.reflection) hSpan

/-- The literal Piola field and true Jacobian have the exact negative pullback pairing. -/
theorem unit_inversion_piola_pairing {n : ℕ} (hn : 2≤n)
    (Z : Domain n → Domain n) (L : Domain n →L[ℝ] ℝ) (x : Domain n) (hx : x≠0) :
    let I := inversion (0 : Domain n) 1
    let W := fun y : Domain n => -((‖y‖^(2*n-2))⁻¹) • (ℝ ∙ y)ᗮ.reflection (Z (I y))
    |(fderiv ℝ I x).det| * L (W (I x)) = -L (fderiv ℝ I x (Z x)) := by
  intro I W
  rw [abs_det_fderiv_unit_inversion x hx]
  simp only [W,I,norm_unit_inversion,inv_pow,inv_inv,
    inversion_inversion _ (by norm_num : (1 : ℝ)≠0),unit_inversion_radial_reflection_eq x hx,map_smul,smul_eq_mul]
  rw [(hasFDerivAt_unit_inversion x hx).fderiv]
  simp only [smul_apply,map_smul,smul_eq_mul]
  have hNorm : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have hExponent : 2*n=(2*n-2)+2 := by omega
  rw [hExponent,pow_add]
  field_simp
  simp only [show 2*n-2+2-2=2*n-2 by omega,LinearIsometryEquiv.coe_coe'']

/-- Original L2 data give both actual compact-test pairings and the signed exterior-to-interior integral identity. -/
theorem kelvin_piola_integral_pairing {n : ℕ} (hn : 2≤n)
    (Z : Domain n → Domain n) (hZm : Measurable Z)
    (hZ : MemLp Z 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    let I := inversion (0 : Domain n) 1
    let W := fun y : Domain n => -((‖y‖^(2*n-2))⁻¹) • (ℝ ∙ y)ᗮ.reflection (Z (I y))
    IntegrableOn (fun x => fderiv ℝ η x (W x)) {x : Domain n | 1<‖x‖} volume ∧
    IntegrableOn (fun x => fderiv ℝ η (I x) (fderiv ℝ I x (Z x))) (Metric.ball (0 : Domain n) 1) volume ∧
    (∫ x in {x : Domain n | 1<‖x‖},fderiv ℝ η x (W x))=
      -(∫ x in Metric.ball (0 : Domain n) 1,fderiv ℝ η (I x) (fderiv ℝ I x (Z x))) := by
  intro I W
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let B : Set (Domain n) := Metric.ball (0 : Domain n) 1
  let D : Set (Domain n) := B\{0}
  let O : Set (Domain n) := {x : Domain n | 1<‖x‖}
  have hD : MeasurableSet D := measurableSet_ball.diff (measurableSet_singleton _)
  have hD0 (x : Domain n) (hx : x∈D) : x≠0 := by simpa only [mem_singleton_iff] using hx.2
  have hID : I '' D=O := unit_inversion_image_punctured_ball
  have hDeriv (x : Domain n) (hx : x∈D) : HasFDerivWithinAt I (fderiv ℝ I x) D x :=
    (hasFDerivAt_unit_inversion x (hD0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hIinj : InjOn I D := (inversion_injective (0 : Domain n) (by norm_num : (1 : ℝ)≠0)).injOn
  have hW := (kelvin_piola_L2_exterior hn Z hZm hZ).1
  have hDη : MemLp (fderiv ℝ η) 2 (volume.restrict O) :=
    (hη.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hcη.fderiv ℝ)
  have hProd : Integrable (fun x => ‖fderiv ℝ η x‖*‖W x‖) (volume.restrict O) :=
    memLp_one_iff_integrable.mp (hW.norm.mul' hDη.norm)
  have hPair : IntegrableOn (fun x => fderiv ℝ η x (W x)) O volume := by
    apply hProd.mono' ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hDη.aestronglyMeasurable.prodMk hW.aestronglyMeasurable))
    exact Eventually.of_forall fun x => ContinuousLinearMap.le_opNorm _ _
  let g : Domain n → ℝ := fun x => fderiv ℝ η (I x) (fderiv ℝ I x (Z x))
  have hPoint : (fun x => |(fderiv ℝ I x).det| * fderiv ℝ η (I x) (W (I x))) =ᵐ[volume.restrict D]
      (fun x => -g x) := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact unit_inversion_piola_pairing hn Z (fderiv ℝ η (I x)) x (hD0 x hx)
  have hTransI := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hDeriv hIinj
    (fun x => fderiv ℝ η x (W x))).mp (by simpa only [hID] using hPair)
  have hNeg : IntegrableOn (fun x => -g x) D volume := hTransI.congr hPoint
  have hAE0 : ∀ᵐ x : Domain n ∂volume,x≠0 := by simp [ae_iff]
  have hDB : D=ᵐ[volume] B := by
    filter_upwards [hAE0] with x hx
    change (x∈B\{0})=(x∈B)
    apply propext
    simp only [Set.mem_sdiff,mem_singleton_iff,hx,not_false_eq_true,and_true]
  have hMeasure := Measure.restrict_congr_set hDB
  have hGI : IntegrableOn g B volume := by
    have H := hNeg.neg
    change Integrable (fun x => -(-g x)) (volume.restrict D) at H
    rw [hMeasure] at H
    exact H.congr (Eventually.of_forall fun x => neg_neg (g x))
  have hChange := integral_image_eq_integral_abs_det_fderiv_smul volume hD hDeriv hIinj
    (fun x => fderiv ℝ η x (W x))
  rw [hID] at hChange
  have hChange' : (∫ x in O,fderiv ℝ η x (W x))=-(∫ x in B,g x) := by
    change (∫ x in O,fderiv ℝ η x (W x))=
      ∫ x,|(fderiv ℝ I x).det| * fderiv ℝ η (I x) (W (I x)) ∂volume.restrict D at hChange
    rw [integral_congr_ae hPoint,integral_neg,hMeasure] at hChange
    exact hChange
  exact ⟨hPair,hGI,hChange'⟩

end StationaryHarmonicMaps.Analysis

end
