module

public import StationaryHarmonicMaps.Analysis.KelvinPiolaL2
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Actual inversion transport away from its center

The genuine Jacobian density is positive on every measurable set avoiding
zero. Inversion therefore transports null sets and actual L2 functions
without requiring a globally measurable original representative. A true
upper radial bound gives the displayed L2 energy constant. These are
value-transport results; no weak derivative or boundary gluing is asserted.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual unit inversion is nonsingular between a measurable punctured set and its genuine image. -/
theorem quasiMeasurePreserving_unit_inversion_on {n : ℕ}
    (S : Set (Domain n)) (hS : MeasurableSet S) (hS0 : ∀ x∈S,x≠0) :
    Measure.QuasiMeasurePreserving (inversion (0 : Domain n) 1)
      (volume.restrict S) (volume.restrict (inversion (0 : Domain n) 1 '' S)) := by
  let I := inversion (0 : Domain n) 1
  have hDeriv (x : Domain n) (hx : x∈S) : HasFDerivWithinAt I (fderiv ℝ I x) S x :=
    (hasFDerivAt_unit_inversion x (hS0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hInj : InjOn I S := (inversion_injective (0 : Domain n) (by norm_num : (1 : ℝ)≠0)).injOn
  let d := fun x : Domain n=>ENNReal.ofReal |(fderiv ℝ I x).det|
  have hd : AEMeasurable d (volume.restrict S) :=
    aemeasurable_ofReal_abs_det_fderivWithin volume hS hDeriv
  have hd0 : ∀ᵐ x ∂volume.restrict S,d x≠0 := by
    filter_upwards [ae_restrict_mem hS] with x hx
    dsimp only [d,I]
    rw [abs_det_fderiv_unit_inversion x (hS0 x hx)]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hS0 x hx)) _))).ne'
  have hAc := withDensity_absolutelyContinuous' hd hd0
  have hMap := map_withDensity_abs_det_fderiv_eq_addHaar volume hS.nullMeasurableSet hDeriv hInj
  refine ⟨measurable_unit_inversion n,?_⟩
  rw [← hMap]
  exact hAc.map (measurable_unit_inversion n)

/-- Positive radial annuli have the genuine reciprocal annuli as their exact inversion images. -/
theorem unit_inversion_image_annulus {n : ℕ} (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    inversion (0 : Domain n) 1 '' {x : Domain n | a<‖x‖ ∧ ‖x‖<b}=
      {y : Domain n | b⁻¹<‖y‖ ∧ ‖y‖<a⁻¹} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [mem_setOf_eq,norm_unit_inversion]
    have hn : 0<‖x‖ := ha.trans hx.1
    exact ⟨(inv_lt_inv₀ hb hn).mpr hx.2,(inv_lt_inv₀ hn ha).mpr hx.1⟩
  · intro hy
    have hyPos : 0<‖y‖ := (inv_pos.mpr hb).trans hy.1
    refine ⟨inversion (0 : Domain n) 1 y,?_,inversion_inversion _ (by norm_num) _⟩
    rw [mem_setOf_eq,norm_unit_inversion]
    constructor
    · have H := (inv_lt_inv₀ (inv_pos.mpr ha) hyPos).mpr hy.2
      simpa only [inv_inv] using H
    · have H := (inv_lt_inv₀ hyPos (inv_pos.mpr hb)).mpr hy.1
      simpa only [inv_inv] using H

/-- The genuine original L2 function pulls back along inversion, with the exact upper-radius Jacobian bound and no global measurability premise. -/
theorem unit_inversion_L2_transport_bounded_set {n m : ℕ}
    (S : Set (Domain n)) (hS : MeasurableSet S) (hS0 : ∀ x∈S,x≠0)
    (b : ℝ) (hb : 0<b) (hBound : ∀ x∈S,‖x‖≤b)
    (u : Domain n → Ambient m)
    (hu : MemLp u 2 (volume.restrict (inversion (0 : Domain n) 1 '' S))) :
    MemLp (fun x=>u (inversion (0 : Domain n) 1 x)) 2 (volume.restrict S) ∧
      (∫ x in S,‖u (inversion (0 : Domain n) 1 x)‖^2)≤
        b^(2*n)*(∫ y in inversion (0 : Domain n) 1 '' S,‖u y‖^2) := by
  let I := inversion (0 : Domain n) 1
  let C := b^(2*n)
  have hC : 0<C := pow_pos hb _
  have hComp : AEStronglyMeasurable (fun x=>u (I x)) (volume.restrict S) :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_unit_inversion_on S hS hS0)
  have hDeriv (x : Domain n) (hx : x∈S) : HasFDerivWithinAt I (fderiv ℝ I x) S x :=
    (hasFDerivAt_unit_inversion x (hS0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hInj : InjOn I S := (inversion_injective (0 : Domain n) (by norm_num : (1 : ℝ)≠0)).injOn
  have hChange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hDeriv hInj
    (fun y=>ENNReal.ofReal (‖u y‖^2))
  have hPoint (x : Domain n) (hx : x∈S) :
      ‖u (I x)‖^2≤C*(|(fderiv ℝ I x).det| *‖u (I x)‖^2) := by
    have hNorm : 0<‖x‖ := norm_pos_iff.mpr (hS0 x hx)
    have hPower : ‖x‖^(2*n)≤C := pow_le_pow_left₀ (norm_nonneg _) (hBound x hx) _
    have hOne : 1≤C*(‖x‖^(2*n))⁻¹ := by
      have H := mul_le_mul_of_nonneg_right hPower (inv_nonneg.mpr (pow_nonneg hNorm.le (2*n)))
      simpa only [mul_inv_cancel₀ (pow_ne_zero _ hNorm.ne')] using H
    rw [abs_det_fderiv_unit_inversion x (hS0 x hx)]
    have H := mul_le_mul_of_nonneg_right hOne (sq_nonneg ‖u (I x)‖)
    simpa only [one_mul,mul_assoc] using H
  have hLin : (∫⁻ x in S,ENNReal.ofReal (‖u (I x)‖^2))≤
      ENNReal.ofReal C*(∫⁻ y in I '' S,ENNReal.ofReal (‖u y‖^2)) := by
    rw [hChange,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    calc
      _ ≤ ENNReal.ofReal (C*(|(fderiv ℝ I x).det| *‖u (I x)‖^2)) :=
        ENNReal.ofReal_le_ofReal (hPoint x hx)
      _ = _ := by rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_mul (abs_nonneg _)]
  have hUI : IntegrableOn (fun y=>‖u y‖^2) (I '' S) volume :=
    hu.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hFinite : (∫⁻ y in I '' S,ENNReal.ofReal (‖u y‖^2))<⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y=>sq_nonneg ‖u y‖)).mp hUI.hasFiniteIntegral
  have hPullI : IntegrableOn (fun x=>‖u (I x)‖^2) S volume :=
    ⟨(continuous_pow 2).comp_aestronglyMeasurable hComp.norm,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x=>sq_nonneg ‖u (I x)‖)).mpr
        (hLin.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFinite))⟩
  refine ⟨(memLp_two_iff_integrable_sq_norm hComp).mpr hPullI,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hPullI (Eventually.of_forall fun x=>sq_nonneg ‖u (I x)‖),
    ← ofReal_integral_eq_lintegral_ofReal hUI (Eventually.of_forall fun x=>sq_nonneg ‖u x‖),
    ← ENNReal.ofReal_mul hC.le] at hLin
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (integral_nonneg fun y=>sq_nonneg ‖u y‖))).mp hLin

private theorem l2_energy_eq_toReal_sq {n m : ℕ} (μ : Measure (Domain n))
    (f : Domain n → Ambient m) (hf : MemLp f 2 μ) :
    (∫ x,‖f x‖^2 ∂μ)=(eLpNorm f 2 μ).toReal^2 := by
  rw [← Lp.norm_toLp f hf]
  have hClass : ‖hf.toLp f‖^2=∫ x,‖(hf.toLp f) x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x=>real_inner_self_eq_norm_sq ((hf.toLp f) x))
  rw [hClass]
  exact integral_congr_ae (hf.coeFn_toLp.symm.mono fun x hx=>congrArg (fun z=>‖z‖^2) hx)

/-- Original strong L2 convergence is transported by actual inversion on every radially bounded punctured measurable set, for the same raw representatives. -/
theorem tendsto_unit_inversion_L2_transport {n m : ℕ}
    (S : Set (Domain n)) (hS : MeasurableSet S) (hS0 : ∀ x∈S,x≠0)
    (b : ℝ) (hb : 0<b) (hBound : ∀ x∈S,‖x‖≤b)
    (u : ℕ → Domain n → Ambient m) (v : Domain n → Ambient m)
    (hu : ∀ k,MemLp (u k) 2 (volume.restrict (inversion (0 : Domain n) 1 '' S)))
    (hv : MemLp v 2 (volume.restrict (inversion (0 : Domain n) 1 '' S)))
    (hStrong : Tendsto (fun k=>eLpNorm (u k-v) 2
      (volume.restrict (inversion (0 : Domain n) 1 '' S))) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm (fun x=>u k (inversion (0 : Domain n) 1 x)-v (inversion (0 : Domain n) 1 x))
      2 (volume.restrict S)) atTop (𝓝 0) := by
  let I := inversion (0 : Domain n) 1
  let μ := volume.restrict (I '' S)
  let ν := volume.restrict S
  let f := fun k=>u k-v
  let g := fun k x=>u k (I x)-v (I x)
  have hF (k : ℕ) : MemLp (f k) 2 μ := (hu k).sub hv
  have hG (k : ℕ) : MemLp (g k) 2 ν :=
    (unit_inversion_L2_transport_bounded_set S hS hS0 b hb hBound (f k) (hF k)).1
  have hToReal : Tendsto (fun k=>(eLpNorm (f k) 2 μ).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero,I,μ,f] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hStrong
  have hOriginal : Tendsto (fun k=>∫ x,‖f k x‖^2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [l2_energy_eq_toReal_sq μ _ (hF _)]
    simpa only [zero_pow (by decide : (2 : ℕ)≠0)] using hToReal.pow 2
  have hUpper : Tendsto (fun k=>b^(2*n)*(∫ x,‖f k x‖^2 ∂μ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hOriginal.const_mul (b^(2*n))
  have hEnergy : Tendsto (fun k=>∫ x,‖g k x‖^2 ∂ν) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun k=>integral_nonneg fun x=>sq_nonneg ‖g k x‖)
      (fun k=>(unit_inversion_L2_transport_bounded_set S hS hS0 b hb hBound (f k) (hF k)).2)
  have hNorm : Tendsto (fun k=>(eLpNorm (g k) 2 ν).toReal) atTop (𝓝 (0 : ℝ)) := by
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp hEnergy
    change Tendsto (fun k=>Real.sqrt (∫ x,‖g k x‖^2 ∂ν)) atTop (𝓝 (Real.sqrt 0)) at H
    simpa only [l2_energy_eq_toReal_sq ν _ (hG _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,Real.sqrt_zero] using H
  have hENN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hNorm
  simpa only [Function.comp_def,ENNReal.ofReal_zero,
    ENNReal.ofReal_toReal (hG _).eLpNorm_ne_top] using hENN

end StationaryHarmonicMaps.Analysis

end
