/- Copyright (c) 2026. All rights reserved. -/
module

public import HarmonicMaps.Analysis.L2AffineContinuity
public import HarmonicMaps.Analysis.VariableMollificationPullbackEstimates
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Actual bounded radial sampling for Neumann reflection

The fixed dilation window lies in [1/4,1], so its original sampling map is
nonsingular and its inverse Jacobian is at most 4^n. Fubini and finite
measure Jensen give real L2 control of the same raw radial averages.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem radial_window_mass :
    (volume.restrict (Icc (1/4:ℝ) 1)).real univ=3/4 := by
  norm_num [measureReal_def,Measure.restrict_apply,Real.volume_Icc]

private theorem radial_inverse_power_bound {n : ℕ} {t : ℝ} (ht : t∈Icc (1/4:ℝ) 1) :
    |(t^n)⁻¹|≤(4:ℝ)^n := by
  have ht0 : 0<t := lt_of_lt_of_le (by norm_num) ht.1
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _)),← inv_pow]
  apply pow_le_pow_left₀ (inv_nonneg.mpr ht0.le)
  have H := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/4) ht.1
  simpa only [one_div] using (show t⁻¹≤4 by norm_num at H ⊢;exact H)

/-- The actual fixed-window joint radial sampling preserves target null sets. -/
theorem radial_window_quasiMeasurePreserving (n : ℕ) :
    Measure.QuasiMeasurePreserving (fun p : Domain n × ℝ=>p.2 • p.1)
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) volume := by
  apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact Measure.quasiMeasurePreserving_smul volume (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

/-- The original integrable field has a genuinely integrable joint radial pullback. -/
theorem radial_window_joint_integrable {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Domain n → G) (hf : Integrable f volume) :
    Integrable (fun p : Domain n × ℝ=>f (p.2 • p.1))
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) := by
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  have hm : AEStronglyMeasurable (fun p : Domain n × ℝ=>f (p.2 • p.1)) (volume.prod σ) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (radial_window_quasiMeasurePreserving n)
  apply (integrable_prod_iff' hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hf.comp_smul (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))
  · apply (integrable_const ((4:ℝ)^n*(∫x,‖f x‖))).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change ‖∫x,‖f (t • x)‖‖≤(4:ℝ)^n*(∫x,‖f x‖)
    rw [Real.norm_of_nonneg (integral_nonneg fun x=>norm_nonneg (f (t • x))),
      Measure.integral_comp_smul volume (fun x=>‖f x‖) t]
    simp only [Domain,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (radial_inverse_power_bound ht)
      (integral_nonneg fun x=>norm_nonneg (f x))

/-- Nonnegative original radial integrals have the full inverse-Jacobian bound. -/
theorem radial_window_double_integral_le {n : ℕ} (f : Domain n → ℝ)
    (hf : Integrable f volume) (hpos : ∀x,0≤f x) :
    (∫x,(∫t in Icc (1/4:ℝ) 1,f (t • x)))≤(4:ℝ)^n*(∫x,f x) := by
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  have hi := radial_window_joint_integrable f hf
  rw [integral_integral_swap hi]
  have hPoint : ∀ᵐt∂σ,(∫x,f (t • x))≤(4:ℝ)^n*(∫x,f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Measure.integral_comp_smul volume f t]
    simp only [Domain,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (radial_inverse_power_bound ht) (integral_nonneg hpos)
  calc
    _≤∫_t,(4:ℝ)^n*(∫x,f x) ∂σ := integral_mono_ae hi.integral_prod_right (integrable_const _) hPoint
    _=(3/4:ℝ)*((4:ℝ)^n*(∫x,f x)) := by rw [integral_const];change σ.real univ*_= _;rw [radial_window_mass]
    _≤(4:ℝ)^n*(∫x,f x) := mul_le_of_le_one_left
      (mul_nonneg (by positivity) (integral_nonneg hpos)) (by norm_num)

private theorem radial_window_jensen {q : ℕ} (f : ℝ → Ambient q)
    (hf : Integrable f (volume.restrict (Icc (1/4:ℝ) 1)))
    (hsq : Integrable (fun t=>‖f t‖^2) (volume.restrict (Icc (1/4:ℝ) 1))) :
    ‖∫t in Icc (1/4:ℝ) 1,f t‖^2≤∫t in Icc (1/4:ℝ) 1,‖f t‖^2 := by
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  have hMass : σ.real univ=3/4 := radial_window_mass
  letI : NeZero σ := ⟨by
    intro hz
    have H := hMass
    rw [hz] at H
    norm_num [measureReal_def] at H⟩
  have hc : ConvexOn ℝ univ (fun v : Ambient q=>‖v‖^2) :=
    (convexOn_univ_norm (E:=Ambient q)).pow (fun _ _=>norm_nonneg _) 2
  have H := hc.map_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _=>mem_univ _) hf hsq
  simp only [average_eq] at H
  change ‖(σ.real univ)⁻¹ • (∫t,f t ∂σ)‖^2≤(σ.real univ)⁻¹ • (∫t,‖f t‖^2 ∂σ) at H
  rw [hMass] at H
  norm_num [norm_smul,smul_eq_mul] at H
  have hI : 0≤∫t,‖f t‖^2 ∂σ := integral_nonneg fun _=>sq_nonneg _
  nlinarith only [H,hI]

/-- Actual bounded measurable radial weights give L2 averages, with the same raw input and an explicit coefficient-one sampling Jacobian bound. -/
theorem radial_window_weighted_average_L2 {n q : ℕ}
    (w : Domain n × ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hC : 0≤C)
    (hBound : ∀x t,t∈Icc (1/4:ℝ) 1 → ‖w (x,t)‖≤C)
    (u : Domain n → Ambient q) (hu : Integrable u volume) (hu2 : MemLp u 2 volume) :
    Integrable (fun p : Domain n × ℝ=>w p • u (p.2 • p.1))
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) ∧
    Integrable (fun p : Domain n × ℝ=>‖w p • u (p.2 • p.1)‖^2)
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) ∧
    ((∫p,‖w p • u (p.2 • p.1)‖^2 ∂volume.prod (volume.restrict (Icc (1/4:ℝ) 1)))≤
      C^2*(4:ℝ)^n*(∫x,‖u x‖^2)) ∧
    MemLp (fun x=>∫t in Icc (1/4:ℝ) 1,w (x,t) • u (t • x)) 2 volume ∧
      (∫x,‖∫t in Icc (1/4:ℝ) 1,w (x,t) • u (t • x)‖^2)≤
        C^2*(4:ℝ)^n*(∫x,‖u x‖^2) := by
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  have hB : ∀ᵐp∂volume.prod σ,‖w p‖≤C := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)] with p hp
    exact hBound p.1 p.2 hp
  have hRaw := radial_window_joint_integrable u hu
  have hSqRaw := radial_window_joint_integrable (fun x=>‖u x‖^2)
    (hu2.integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hJoint : Integrable (fun p : Domain n × ℝ=>w p • u (p.2 • p.1)) (volume.prod σ) :=
    hRaw.bdd_smul C hw.aestronglyMeasurable hB
  have hSqMeas : AEStronglyMeasurable (fun p : Domain n × ℝ=>‖w p • u (p.2 • p.1)‖^2)
      (volume.prod σ) := hJoint.aestronglyMeasurable.norm.pow 2
  have hSqBound : ∀ᵐp∂volume.prod σ,‖w p • u (p.2 • p.1)‖^2≤C^2*‖u (p.2 • p.1)‖^2 := by
    filter_upwards [hB] with p hp
    rw [norm_smul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp 2) (sq_nonneg _)
  have hJointSq : Integrable (fun p : Domain n × ℝ=>‖w p • u (p.2 • p.1)‖^2) (volume.prod σ) :=
    (hSqRaw.const_mul (C^2)).mono' hSqMeas (hSqBound.mono fun p hp=>(Real.norm_of_nonneg (sq_nonneg _)).trans_le hp)
  have hMeas := hJoint.aestronglyMeasurable.integral_prod_right'
  have hJ : ∀ᵐx∂(volume : Measure (Domain n)),
      ‖∫t,w (x,t) • u (t • x) ∂σ‖^2≤∫t,‖w (x,t) • u (t • x)‖^2 ∂σ := by
    filter_upwards [hJoint.prod_right_ae,hJointSq.prod_right_ae] with x hx hsx
    exact radial_window_jensen (fun t=>w (x,t) • u (t • x)) hx hsx
  have hI : Integrable (fun x=>‖∫t,w (x,t) • u (t • x) ∂σ‖^2) volume :=
    hJointSq.integral_prod_left.mono' (hMeas.norm.pow 2)
      (hJ.mono fun x hx=>(Real.norm_of_nonneg (sq_nonneg _)).trans_le hx)
  have hJointBound : (∫p,‖w p • u (p.2 • p.1)‖^2 ∂volume.prod σ)≤
      C^2*(4:ℝ)^n*(∫x,‖u x‖^2) := by
    calc
      _≤∫p,C^2*‖u (p.2 • p.1)‖^2 ∂volume.prod σ :=
        integral_mono_ae hJointSq (hSqRaw.const_mul (C^2)) hSqBound
      _=C^2*(∫x,(∫t,‖u (t • x)‖^2 ∂σ)) := by
        rw [integral_prod _ (hSqRaw.const_mul (C^2))]
        simp only [integral_const_mul,σ]
      _≤C^2*((4:ℝ)^n*(∫x,‖u x‖^2)) := mul_le_mul_of_nonneg_left
        (radial_window_double_integral_le _ (hu2.integrable_norm_pow (by decide : (2:ℕ)≠0))
          (fun x=>sq_nonneg ‖u x‖)) (pow_nonneg hC 2)
      _=_ := by ring
  refine ⟨hJoint,hJointSq,hJointBound,(memLp_two_iff_integrable_sq_norm hMeas).mpr hI,?_⟩
  calc
    _≤∫x,(∫t,‖w (x,t) • u (t • x)‖^2 ∂σ) := integral_mono_ae hI hJointSq.integral_prod_left hJ
    _=∫p,‖w p • u (p.2 • p.1)‖^2 ∂volume.prod σ := (integral_prod _ hJointSq).symm
    _≤_ := hJointBound

end StationaryHarmonicMaps.Analysis

end
