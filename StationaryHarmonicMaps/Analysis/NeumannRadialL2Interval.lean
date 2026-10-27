/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Sampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual variable radial intervals on the exterior unit annulus

The original L2 field is sampled only along the radial segment from the
inverted point to the unit sphere. Endpoint sphere values contribute no
parameter mass. The actual joint integrals and radial average are controlled
without choosing a new representative of the original field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem inverse_radius_window {n : ℕ} (x : Domain n)
    (hx : 1<‖x‖ ∧ ‖x‖<2) :
    1/4≤(‖x‖⁻¹)^2 ∧ (‖x‖⁻¹)^2≤‖x‖⁻¹ ∧ ‖x‖⁻¹≤1 := by
  have hr : 0<‖x‖ := lt_trans (by norm_num) hx.1
  have hhi : 0<‖x‖⁻¹ := inv_pos.mpr hr
  have hHalf : (1/2:ℝ)≤‖x‖⁻¹ := by
    have H := one_div_le_one_div_of_le hr hx.2.le
    norm_num only [one_div] at H
    exact H
  have hOne : ‖x‖⁻¹≤1 := (inv_le_one₀ hr).mpr hx.1.le
  exact ⟨by nlinarith only [sq_nonneg (‖x‖⁻¹-1/2),hHalf],by nlinarith only [hhi,hOne],hOne⟩

private theorem radial_sample_inside {n : ℕ} (x : Domain n) (t : ℝ)
    (hx : 1<‖x‖ ∧ ‖x‖<2) (ht : 0≤t) (hUpper : t<‖x‖⁻¹) :
    t • x∈ball (0 : Domain n) 1 := by
  rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ht]
  have hr : 0<‖x‖ := lt_trans (by norm_num) hx.1
  have H := mul_lt_mul_of_pos_right hUpper hr
  simpa only [inv_mul_cancel₀ hr.ne'] using H

/-- The actual radial sample agrees with the original ball representative jointly almost everywhere, including arbitrary null-set boundary values. -/
theorem neumann_radial_interval_zeroExtension_ae {n q : ℕ} (a b : ℕ)
    (u : Domain n → Ambient q) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let w := fun p : Domain n × ℝ=>if p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
      then ‖p.1‖^a*p.2^b else 0
    (fun p : Domain n × ℝ=>w p • (ball (0 : Domain n) 1).indicator u (p.2 • p.1))
      =ᵐ[volume.prod (volume.restrict (Icc (1/4:ℝ) 1))]
        (fun p : Domain n × ℝ=>w p • u (p.2 • p.1)) := by
  intro A w
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  have hNotEndpoint : ∀ᵐ(p : Domain n × ℝ)∂volume.prod σ,p.2≠‖p.1‖⁻¹ := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_snd
      ((measurable_norm.comp measurable_fst).inv)).compl)).mpr
    exact Eventually.of_forall fun x=>ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [hNotEndpoint,Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)] with p hp ht
  by_cases hActive : p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
  · have hs := radial_sample_inside p.1 p.2 hActive.1 (by linarith only [ht.1])
      (lt_of_le_of_ne hActive.2.2 hp)
    rw [indicator_of_mem hs u]
  · simp only [w,if_neg hActive,zero_smul]

/-- Variable radial integration on the actual exterior annulus preserves raw L2 data and supplies true joint Fubini data before the output estimate. -/
theorem neumann_radial_interval_L2 {n q : ℕ} (a b : ℕ)
    (u : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let w := fun p : Domain n × ℝ=>if p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
      then ‖p.1‖^a*p.2^b else 0
    let V := fun x : Domain n=>‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • u (t • x))
    Integrable (fun p : Domain n × ℝ=>w p • u (p.2 • p.1))
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) ∧
    Integrable (fun p : Domain n × ℝ=>‖w p • u (p.2 • p.1)‖^2)
      (volume.prod (volume.restrict (Icc (1/4:ℝ) 1))) ∧
    ((∫p,‖w p • u (p.2 • p.1)‖^2 ∂volume.prod (volume.restrict (Icc (1/4:ℝ) 1)))≤
      (2:ℝ)^(2*a)*(4:ℝ)^n*(∫x in ball (0 : Domain n) 1,‖u x‖^2)) ∧
    (∀x∈A,(∫t in Icc (1/4:ℝ) 1,w (x,t) • u (t • x))=V x) ∧
    MemLp V 2 (volume.restrict A) ∧
    (∫x in A,‖V x‖^2)≤(2:ℝ)^(2*a)*(4:ℝ)^n*(∫x in ball (0 : Domain n) 1,‖u x‖^2) := by
  intro A w V
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  let u₀ := (ball (0 : Domain n) 1).indicator u
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hSet : MeasurableSet {p : Domain n × ℝ | p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹} :=
    (hA.preimage measurable_fst).inter ((measurableSet_le (measurable_norm.comp measurable_fst |>.inv |>.pow_const 2) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_norm.comp measurable_fst |>.inv)))
  have hw : Measurable w := Measurable.ite hSet
    ((measurable_norm.comp measurable_fst).pow_const a |>.mul (measurable_snd.pow_const b)) measurable_const
  have hBound (x : Domain n) (t : ℝ) (ht : t∈Icc (1/4:ℝ) 1) : ‖w (x,t)‖≤(2:ℝ)^a := by
    by_cases hx : x∈A ∧ (‖x‖⁻¹)^2≤t ∧ t≤‖x‖⁻¹
    · rw [show w (x,t)=‖x‖^a*t^b from if_pos hx,Real.norm_of_nonneg (mul_nonneg
        (pow_nonneg (norm_nonneg _) _) (pow_nonneg (by linarith only [ht.1]) _))]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _)
        (pow_le_one₀ (by linarith only [ht.1]) ht.2) |>.trans
          (pow_le_pow_left₀ (norm_nonneg _) hx.1.2.le _)
    · simp only [w,if_neg hx,norm_zero]
      positivity
  have hU₂ : MemLp u₀ 2 volume := memLp_zeroExtension measurableSet_ball hu
  have hU₁ : Integrable u₀ volume := by
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Domain n) 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hI : IntegrableOn u (ball (0 : Domain n) 1) volume := hu.integrable (by norm_num)
    exact hI.integrable_indicator measurableSet_ball
  obtain ⟨hJoint₀,hJointSq₀,hBound₀,hAvg₀,hAvgBound₀⟩ :=
    radial_window_weighted_average_L2 w hw ((2:ℝ)^a) (by positivity) hBound u₀ hU₁ hU₂
  have hSame : (fun p : Domain n × ℝ=>w p • u₀ (p.2 • p.1)) =ᵐ[volume.prod σ]
      (fun p : Domain n × ℝ=>w p • u (p.2 • p.1)) :=
    neumann_radial_interval_zeroExtension_ae a b u
  have hSameSq := hSame.mono fun p hp=>congrArg (fun z=>‖z‖^2) hp
  have hZeroEnergy : (∫x,‖u₀ x‖^2)=∫x in ball (0 : Domain n) 1,‖u x‖^2 := by
    have hPoint : (fun x=>‖u₀ x‖^2)=(ball (0 : Domain n) 1).indicator (fun x=>‖u x‖^2) := by
      funext x
      by_cases hx : x∈ball (0 : Domain n) 1
      · simp only [u₀,indicator_of_mem hx]
      · simp only [u₀,indicator_of_notMem hx,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
    rw [hPoint,integral_indicator measurableSet_ball]
  have hConst : ((2:ℝ)^a)^2=(2:ℝ)^(2*a) := by rw [← pow_mul];congr 1;omega
  have hBoundJoint : (∫p,‖w p • u (p.2 • p.1)‖^2 ∂volume.prod σ)≤
      (2:ℝ)^(2*a)*(4:ℝ)^n*(∫x in ball (0 : Domain n) 1,‖u x‖^2) := by
    rw [← integral_congr_ae hSameSq]
    simpa only [hZeroEnergy,hConst] using hBound₀
  have hAverage (f : Domain n → Ambient q) (x : Domain n) (hx : x∈A) :
      (∫t in Icc (1/4:ℝ) 1,w (x,t) • f (t • x))=
        ‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • f (t • x)) := by
    obtain ⟨hl,hlh,hh⟩ := inverse_radius_window x hx
    have hSub : Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹)⊆Icc (1/4:ℝ) 1 := Icc_subset_Icc hl hh
    have hPoint (t : ℝ) : w (x,t) • f (t • x)=
        ‖x‖^a • ((Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹)).indicator (fun t=>t^b • f (t • x)) t) := by
      by_cases ht : t∈Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹)
      · rw [show w (x,t)=‖x‖^a*t^b from if_pos ⟨hx,ht.1,ht.2⟩,indicator_of_mem ht,mul_smul]
      · have hnot : ¬(x∈A ∧ (‖x‖⁻¹)^2≤t ∧ t≤‖x‖⁻¹) := fun h=>ht h.2
        simp only [w,if_neg hnot,indicator_of_notMem ht,zero_smul,smul_zero]
    rw [integral_congr_ae (Eventually.of_forall hPoint),integral_smul,
      setIntegral_indicator measurableSet_Icc,inter_eq_right.mpr hSub,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlh]
  have hAvgSame : (fun x=>∫t,w (x,t) • u₀ (t • x) ∂σ) =ᵐ[volume]
      (fun x=>∫t,w (x,t) • u (t • x) ∂σ) := by
    exact (Measure.ae_ae_of_ae_prod hSame).mono fun x hx=>integral_congr_ae hx
  have hAvg : MemLp (fun x=>∫t,w (x,t) • u (t • x) ∂σ) 2 volume := hAvg₀.ae_eq hAvgSame
  have hLocal : (fun x=>∫t,w (x,t) • u (t • x) ∂σ) =ᵐ[volume.restrict A] V := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact hAverage u x hx
  refine ⟨hJoint₀.congr hSame,hJointSq₀.congr hSameSq,hBoundJoint,hAverage u,
    hAvg.mono_measure Measure.restrict_le_self |>.ae_eq hLocal,?_⟩
  calc
    _=∫x in A,‖∫t,w (x,t) • u (t • x) ∂σ‖^2 :=
      (integral_congr_ae (hLocal.mono fun x hx=>congrArg (fun z=>‖z‖^2) hx)).symm
    _≤∫x,‖∫t,w (x,t) • u (t • x) ∂σ‖^2 :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun x=>sq_nonneg _)
        (hAvg.integrable_norm_pow (by decide : (2:ℕ)≠0))
    _=∫x,‖∫t,w (x,t) • u₀ (t • x) ∂σ‖^2 :=
      (integral_congr_ae (hAvgSame.mono fun x hx=>congrArg (fun z=>‖z‖^2) hx)).symm
    _≤_ := by simpa only [hZeroEnergy,hConst] using hAvgBound₀

/-- The original raw L2 field has genuine fibre integrability on its actual
variable radial interval for almost every exterior-annulus point. -/
theorem neumann_radial_interval_integrable_ae {n q : ℕ} (b : ℕ)
    (u : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ∀ᵐ(x : Domain n)∂volume.restrict {x : Domain n | 1<‖x‖ ∧ ‖x‖<2},
      IntervalIntegrable (fun t : ℝ=>t^b • u (t • x)) volume ((‖x‖⁻¹)^2) (‖x‖⁻¹) := by
  let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hJ := (neumann_radial_interval_L2 0 b u hu).1
  filter_upwards [ae_restrict_mem hA,
    hJ.prod_right_ae.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hInt
  obtain ⟨hl,hlh,hh⟩ := inverse_radius_window x hx
  have hSub : Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹)⊆Icc (1/4:ℝ) 1 := Icc_subset_Icc hl hh
  have hSmall := hInt.mono_measure (Measure.restrict_mono_set volume hSub)
  have hRaw : IntegrableOn (fun t : ℝ=>t^b • u (t • x))
      (Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹)) volume := by
    apply hSmall.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change (if x∈A ∧ (‖x‖⁻¹)^2≤t ∧ t≤‖x‖⁻¹ then ‖x‖^0*t^b else 0) • u (t • x)=t^b • u (t • x)
    rw [if_pos ⟨hx,ht.1,ht.2⟩,pow_zero,one_mul]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlh).mpr (hRaw.mono_set Ioc_subset_Icc_self)

end StationaryHarmonicMaps.Analysis

end
