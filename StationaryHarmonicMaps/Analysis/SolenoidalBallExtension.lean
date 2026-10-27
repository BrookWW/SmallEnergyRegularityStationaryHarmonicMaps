module

public import StationaryHarmonicMaps.Analysis.SolenoidalKelvinExtension
public import HarmonicMaps.Analysis.AffineBallMeasure

/-!
# Solenoidal L2 extension from any ball

Positive affine transport of the original field and actual compact smooth
tests transfers the unit-ball Kelvin construction to every ball. The
Jacobian factors cancel in the energy comparison, so the squared-norm
constant remains two. Only restricted L2 membership and the original
distributional divergence equation are required.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem integral_affine_full {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0<t) (f : Domain n → ℝ) :
    (∫ x,f (a+t • (x-b)))=(t^n)⁻¹*(∫ x,f x) := by
  rw [← (affineBall_measurableEmbedding a b ht.ne').integral_map,
    affineBall_map_volume a b ht,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg ht.le n)),smul_eq_mul]

private theorem memLp_affine_full {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0<t) {f : Domain n → E}
    (hf : MemLp f 2 volume) : MemLp (fun x => f (a+t • (x-b))) 2 volume := by
  have H := hf.smul_measure (c := ENNReal.ofReal ((t^n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_volume a b ht] at H
  exact H.comp_of_map (affineBall_measurableEmbedding a b ht.ne').measurable.aemeasurable

private theorem fderiv_affine_test {n : ℕ} (η : Domain n → ℝ)
    (hη : ContDiff ℝ ∞ η) (a b : Domain n) (t : ℝ) (x z : Domain n) :
    fderiv ℝ (fun y => η (a+t • (y-b))) x z =
      t*fderiv ℝ η (a+t • (x-b)) z := by
  have hA := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const b).const_smul t).const_add a
  have H := (hη.differentiable (by simp) (a+t • (x-b))).hasFDerivAt.comp x hA
  change HasFDerivAt (fun y => η (a+t • (y-b)))
    ((fderiv ℝ η (a+t • (x-b))).comp
      (t • ContinuousLinearMap.id ℝ (Domain n))) x at H
  rw [H.fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

/-- The original L2 divergence-free field on any positive-radius ball has a full-space L2 divergence-free extension with squared-norm bound two. -/
theorem exists_solenoidal_L2_extension_ball {n : ℕ} (hn : 2≤n)
    (a : Domain n) (r : ℝ) (hr : 0<r) (Z : Domain n → Domain n)
    (hZ : MemLp Z 2 (volume.restrict (Metric.ball a r)))
    (hdiv : ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball a r →
      (∫ x in Metric.ball a r,fderiv ℝ η x (Z x))=0) :
    ∃ F : Domain n → Domain n,MemLp F 2 volume ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball a r),F x=Z x) ∧
      (∫ x,‖F x‖^2) ≤ 2*(∫ x in Metric.ball a r,‖Z x‖^2) ∧
      ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
        Integrable (fun x => fderiv ℝ η x (F x)) volume ∧
        (∫ x,fderiv ℝ η x (F x))=0 := by
  let Z₁ : Domain n → Domain n := fun y => Z (a+r • (y-0))
  have hr0 : r≠0 := hr.ne'
  have hZ₁ : MemLp Z₁ 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
    simpa only [div_self hr0] using memLp_affineBall a 0 hr r hZ
  have hDiv₁ : ∀ (ψ : Domain n → ℝ),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Domain n) 1 →
      (∫ y in Metric.ball (0 : Domain n) 1,fderiv ℝ ψ y (Z₁ y))=0 := by
    intro ψ hψ hcψ hsψ
    let η : Domain n → ℝ := fun x => ψ (0+r⁻¹ • (x-a))
    have hη : ContDiff ℝ ∞ η := hψ.comp (affineBall_contDiff 0 a r⁻¹)
    have hcη : HasCompactSupport η := affineBallTest_hasCompactSupport hcψ 0 a (inv_ne_zero hr0)
    have hsη : tsupport η ⊆ Metric.ball a r := by
      simpa only [one_div,inv_inv] using affineBallTest_tsupport_subset 0 a (inv_pos.mpr hr) 1 hsψ
    have H := integral_affineBall a 0 hr r (fun x => fderiv ℝ η x (Z x))
    rw [div_self hr0,hdiv η hη hcη hsη,smul_zero] at H
    have hPoint (y : Domain n) : fderiv ℝ η (a+r • (y-0)) (Z (a+r • (y-0)))=
        r⁻¹*fderiv ℝ ψ y (Z₁ y) := by
      change fderiv ℝ (fun x => ψ (0+r⁻¹ • (x-a))) _ _=_
      rw [fderiv_affine_test ψ hψ]
      simp only [add_sub_cancel_left,sub_zero,zero_add,smul_smul,inv_mul_cancel₀ hr0,one_smul,Z₁]
    have hScale : r⁻¹*(∫ y in Metric.ball (0 : Domain n) 1,fderiv ℝ ψ y (Z₁ y))=0 := by
      rw [← integral_const_mul]
      rw [integral_congr_ae (Eventually.of_forall fun y => (hPoint y).symm)]
      exact H
    exact (mul_eq_zero.mp hScale).resolve_left (inv_ne_zero hr0)
  obtain ⟨U,hU,hUInside,hUEnergy,hUDiv⟩ := exists_solenoidal_L2_extension_unitBall hn Z₁ hZ₁ hDiv₁
  let F : Domain n → Domain n := fun x => U (0+r⁻¹ • (x-a))
  have hF : MemLp F 2 volume := memLp_affine_full 0 a (inv_pos.mpr hr) hU
  have hInside : ∀ᵐ x ∂volume.restrict (Metric.ball a r),F x=Z x := by
    have H := ae_affineBall 0 a (inv_pos.mpr hr) 1 hUInside
    simp only [one_div,inv_inv] at H
    filter_upwards [H] with x hx
    change U (0+r⁻¹ • (x-a))=Z x
    convert hx using 1
    simp only [Z₁,sub_zero,zero_add,smul_smul,mul_inv_cancel₀ hr0,one_smul,add_sub_cancel]
  have hEnergy₁ : (∫ y in Metric.ball (0 : Domain n) 1,‖Z₁ y‖^2)=
      (r^n)⁻¹*(∫ x in Metric.ball a r,‖Z x‖^2) := by
    simpa only [div_self hr0,smul_eq_mul] using integral_affineBall a 0 hr r (fun x => ‖Z x‖^2)
  have hEnergyF : (∫ x,‖F x‖^2)=r^n*(∫ y,‖U y‖^2) := by
    simpa only [inv_pow,inv_inv] using integral_affine_full 0 a (inv_pos.mpr hr) (fun y => ‖U y‖^2)
  have hEnergy : (∫ x,‖F x‖^2)≤2*(∫ x in Metric.ball a r,‖Z x‖^2) := by
    rw [hEnergyF]
    have H := mul_le_mul_of_nonneg_left hUEnergy (pow_nonneg hr.le n)
    rw [hEnergy₁] at H
    have hCancel : r^n*(2*((r^n)⁻¹*(∫ x in Metric.ball a r,‖Z x‖^2)))=
        2*(∫ x in Metric.ball a r,‖Z x‖^2) := by
      field_simp
    rw [hCancel] at H
    exact H
  refine ⟨F,hF,hInside,hEnergy,?_⟩
  intro η hη hcη
  let ψ : Domain n → ℝ := fun y => η (a+r • (y-0))
  have hψ : ContDiff ℝ ∞ ψ := hη.comp (affineBall_contDiff a 0 r)
  have hcψ : HasCompactSupport ψ := affineBallTest_hasCompactSupport hcη a 0 hr0
  obtain ⟨hInt,hZero⟩ := hUDiv ψ hψ hcψ
  have hPoint (x : Domain n) : fderiv ℝ ψ (0+r⁻¹ • (x-a)) (U (0+r⁻¹ • (x-a)))=
      r*fderiv ℝ η x (F x) := by
    change fderiv ℝ (fun y => η (a+r • (y-0))) _ _=_
    rw [fderiv_affine_test η hη]
    simp only [sub_zero,zero_add,smul_smul,mul_inv_cancel₀ hr0,one_smul,add_sub_cancel,F]
  have hIntPull : Integrable (fun x => fderiv ℝ ψ (0+r⁻¹ • (x-a)) (U (0+r⁻¹ • (x-a)))) volume := by
    have H := hInt.smul_measure (c := ENNReal.ofReal (((r⁻¹)^n)⁻¹)) ENNReal.ofReal_ne_top
    rw [← affineBall_map_volume 0 a (inv_pos.mpr hr)] at H
    exact H.comp_measurable (affineBall_measurableEmbedding 0 a (inv_ne_zero hr0)).measurable
  have hPairInt : Integrable (fun x => fderiv ℝ η x (F x)) volume := by
    have H := hIntPull.const_mul r⁻¹
    apply H.congr
    exact Eventually.of_forall fun x => by
      change r⁻¹*(fderiv ℝ ψ (0+r⁻¹ • (x-a)) (U (0+r⁻¹ • (x-a))))=_
      rw [hPoint]
      simp only [← mul_assoc,inv_mul_cancel₀ hr0,one_mul]
  refine ⟨hPairInt,?_⟩
  have H := integral_affine_full 0 a (inv_pos.mpr hr) (fun y => fderiv ℝ ψ y (U y))
  rw [hZero,mul_zero] at H
  have hScale : r*(∫ x,fderiv ℝ η x (F x))=0 := by
    rw [← integral_const_mul,integral_congr_ae (Eventually.of_forall fun x => (hPoint x).symm)]
    exact H
  exact (mul_eq_zero.mp hScale).resolve_left hr0

end StationaryHarmonicMaps.Analysis

end
