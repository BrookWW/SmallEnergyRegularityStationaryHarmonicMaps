/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Strong
public import StationaryHarmonicMaps.Analysis.NeumannRadialPairing
public import StationaryHarmonicMaps.Analysis.NeumannRadialGeometry

/-!
# Actual ordinary duality for the radial Neumann correction

The genuine bounded radial interval and its dilation Jacobian give the
ordinary adjoint pairing. The exchanged interval has lower endpoint half
the interior radius and upper endpoint its square. When these reverse,
the original test support makes the entire reversed integral vanish.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem radial_window_adjoint_interval {n q : ℕ} (a : ℕ)
    (u v : Domain n → Ambient q) (hvZero : ∀z,2≤‖z‖ → v z=0)
    (y : Domain n) (hy : y≠0) (hyOne : ‖y‖<1) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let w := fun p : Domain n × ℝ=>if p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
      then ‖p.1‖^a*p.2^a else 0
    (∫t in Icc (1/4:ℝ) 1,|(t^n)⁻¹| *w (t⁻¹ • y,t)*inner ℝ (u y) (v (t⁻¹ • y)))=
      ‖y‖^a*(∫t in ‖y‖/2..‖y‖^2,(t^n)⁻¹*inner ℝ (u y) (v (t⁻¹ • y))) := by
  intro A w
  have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy
  have hPoint (t : ℝ) (ht : t∈Icc (1/4:ℝ) 1) :
      |(t^n)⁻¹| *w (t⁻¹ • y,t)*inner ℝ (u y) (v (t⁻¹ • y))=
        ‖y‖^a*((Ioc (‖y‖/2) (‖y‖^2)).indicator
          (fun t=>(t^n)⁻¹*inner ℝ (u y) (v (t⁻¹ • y))) t) := by
    have htPos : 0<t := lt_of_lt_of_le (by norm_num) ht.1
    have hGeom := neumann_radial_window_after_dilation y hy hyOne t htPos
    have hActive : (t⁻¹ • y∈A ∧ (‖t⁻¹ • y‖⁻¹)^2≤t ∧ t≤‖t⁻¹ • y‖⁻¹) ↔
        t∈Ioc (‖y‖/2) (‖y‖^2) := by
      simpa only [A,mem_setOf_eq,mem_Ioc,inv_pow,and_assoc] using hGeom
    by_cases htI : t∈Ioc (‖y‖/2) (‖y‖^2)
    · rw [show w (t⁻¹ • y,t)=‖t⁻¹ • y‖^a*t^a from if_pos (hActive.mpr htI),
        neumann_radial_equal_power_weight y t htPos a,indicator_of_mem htI,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg htPos.le n))]
      ring
    · rw [show w (t⁻¹ • y,t)=0 from if_neg (fun h=>htI (hActive.mp h)),indicator_of_notMem htI]
      simp only [mul_zero,zero_mul]
  rw [integral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hPoint t ht),integral_const_mul,setIntegral_indicator measurableSet_Ioc]
  by_cases hHalf : 1/2<‖y‖
  · have hLow : (1/4:ℝ)<‖y‖/2 := by linarith only [hHalf]
    have hHigh : ‖y‖^2≤1 := by nlinarith only [hyPos,hyOne]
    have hSub : Ioc (‖y‖/2) (‖y‖^2)⊆Icc (1/4:ℝ) 1 :=
      fun t ht=>⟨(hLow.trans ht.1).le,ht.2.trans hHigh⟩
    rw [inter_eq_right.mpr hSub,← intervalIntegral.integral_of_le (by nlinarith only [hHalf,hyPos])]
  · have hRev : ‖y‖^2≤‖y‖/2 := by nlinarith only [le_of_not_gt hHalf,hyPos]
    have hZero : (∫t in ‖y‖/2..‖y‖^2,(t^n)⁻¹*inner ℝ (u y) (v (t⁻¹ • y)))=0 := by
      calc
        _=∫_t in ‖y‖/2..‖y‖^2,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htI : t∈Icc (‖y‖^2) (‖y‖/2) := by simpa only [uIcc_of_ge hRev] using ht
          have htPos : 0<t := (sq_pos_of_pos hyPos).trans_le htI.1
          have hOut : 2≤‖t⁻¹ • y‖ := by
            rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr htPos.le)]
            have H : 2≤‖y‖/t := (le_div_iff₀ htPos).mpr (by linarith only [htI.2])
            simpa only [div_eq_inv_mul] using H
          dsimp only
          rw [hvZero _ hOut,inner_zero_right,mul_zero]
        _=0 := intervalIntegral.integral_zero
    rw [Ioc_eq_empty (not_lt_of_ge hRev),inter_empty,setIntegral_empty,hZero,mul_zero]

/-- Original B1 L2 data and an actual compact continuous B2 test have genuine
ordinary radial pairings and their exact variable-interval adjoint identity. -/
theorem neumann_radial_interval_duality {n q : ℕ} (hn : 1≤n) (a : ℕ)
    (u v : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : Continuous v) (hcv : HasCompactSupport v) (hsv : tsupport v⊆ball (0 : Domain n) 2) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun x : Domain n=>‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^a • u (t • x))
    let B := fun y : Domain n=>‖y‖^a*(∫t in ‖y‖/2..‖y‖^2,(t^n)⁻¹*inner ℝ (u y) (v (t⁻¹ • y)))
    IntegrableOn (fun x=>inner ℝ (V x) (v x)) A volume ∧
      IntegrableOn B (ball (0 : Domain n) 1) volume ∧
      (∫x in A,inner ℝ (V x) (v x))=∫y in ball (0 : Domain n) 1,B y := by
  intro A V B
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  let w := fun p : Domain n × ℝ=>if p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
    then ‖p.1‖^a*p.2^a else 0
  let u₀ := (ball (0 : Domain n) 1).indicator u
  let f := fun p : Domain n × ℝ=>inner ℝ (w p • u₀ (p.2 • p.1)) (v p.1)
  let g := fun p : Domain n × ℝ=>|(p.2^n)⁻¹| *w (p.2⁻¹ • p.1,p.2)*inner ℝ (u₀ p.1) (v (p.2⁻¹ • p.1))
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hSet : MeasurableSet {p : Domain n × ℝ | p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹} :=
    (hA.preimage measurable_fst).inter ((measurableSet_le (measurable_norm.comp measurable_fst |>.inv |>.pow_const 2) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_norm.comp measurable_fst |>.inv)))
  have hw : Measurable w := Measurable.ite hSet
    ((measurable_norm.comp measurable_fst).pow_const a |>.mul (measurable_snd.pow_const a)) measurable_const
  have hBound (x : Domain n) (t : ℝ) (ht : t∈Icc (1/4:ℝ) 1) : ‖w (x,t)‖≤(2:ℝ)^a := by
    by_cases hx : x∈A ∧ (‖x‖⁻¹)^2≤t ∧ t≤‖x‖⁻¹
    · rw [show w (x,t)=‖x‖^a*t^a from if_pos hx,Real.norm_of_nonneg (mul_nonneg
        (pow_nonneg (norm_nonneg _) _) (pow_nonneg (by linarith only [ht.1]) _))]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _)
        (pow_le_one₀ (by linarith only [ht.1]) ht.2) |>.trans
          (pow_le_pow_left₀ (norm_nonneg _) hx.1.2.le _)
    · simp only [w,if_neg hx,norm_zero]
      positivity
  have hU₁ : Integrable u₀ volume := by
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Domain n) 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hI : IntegrableOn u (ball (0 : Domain n) 1) volume := hu.integrable (by norm_num)
    exact hI.integrable_indicator measurableSet_ball
  obtain ⟨hf,hg,hPair⟩ := neumann_radial_window_pairing_change_variables w hw ((2:ℝ)^a)
    (by positivity) hBound u₀ v hU₁ hv hcv
  obtain ⟨hJU,_hJU2,_hJE,hAv,_hVM,_hVE⟩ := neumann_radial_interval_L2 a a u hu
  have hSame : (fun p : Domain n × ℝ=>w p • u₀ (p.2 • p.1)) =ᵐ[volume.prod σ]
      (fun p : Domain n × ℝ=>w p • u (p.2 • p.1)) :=
    neumann_radial_interval_zeroExtension_ae a a u
  have hJ₀ : Integrable (fun p : Domain n × ℝ=>w p • u₀ (p.2 • p.1)) (volume.prod σ) :=
    hJU.congr hSame.symm
  have hLeft : (fun x=>∫t,f (x,t) ∂σ) =ᵐ[volume]
      A.indicator (fun x=>inner ℝ (V x) (v x)) := by
    filter_upwards [hJ₀.prod_right_ae,Measure.ae_ae_of_ae_prod hSame] with x hx hs
    by_cases hxa : x∈A
    · rw [indicator_of_mem hxa]
      have hI : (∫t,inner ℝ (w (x,t) • u₀ (t • x)) (v x) ∂σ)=
          inner ℝ (∫t,w (x,t) • u₀ (t • x) ∂σ) (v x) := by
        simpa only [real_inner_comm] using integral_inner hx (v x)
      exact hI.trans (congrArg (fun z : Ambient q=>inner ℝ z (v x))
        ((integral_congr_ae hs).trans (hAv x hxa)))
    · rw [indicator_of_notMem hxa]
      have hW (t : ℝ) : w (x,t)=0 := if_neg (fun h=>hxa h.1)
      simp only [f,hW,zero_smul,inner_zero_left,integral_zero]
  have hvZero (z : Domain n) (hz : 2≤‖z‖) : v z=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hNorm : ‖z‖<2 := mem_ball_zero_iff.mp (hsv h)
    exact (not_lt_of_ge hz) hNorm
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hAE0 : ∀ᵐ(y : Domain n)∂volume,y≠0 := by simp [ae_iff]
  have hRight : (fun y=>∫t,g (y,t) ∂σ) =ᵐ[volume]
      (ball (0 : Domain n) 1).indicator B := by
    filter_upwards [hAE0] with y hy
    by_cases hyBall : y∈ball (0 : Domain n) 1
    · rw [indicator_of_mem hyBall]
      have H := radial_window_adjoint_interval a u₀ v hvZero y hy (mem_ball_zero_iff.mp hyBall)
      have hU : u₀ y=u y := indicator_of_mem hyBall u
      simpa only [g,B,σ,hU,w,A] using H
    · rw [indicator_of_notMem hyBall]
      have hU : u₀ y=0 := indicator_of_notMem hyBall u
      simp only [g,hU,inner_zero_left,mul_zero,integral_zero]
  have hLI : IntegrableOn (fun x=>inner ℝ (V x) (v x)) A volume :=
    (integrable_indicator_iff hA).mp (hf.integral_prod_left.congr hLeft)
  have hRI : IntegrableOn B (ball (0 : Domain n) 1) volume :=
    (integrable_indicator_iff measurableSet_ball).mp (hg.integral_prod_left.congr hRight)
  refine ⟨hLI,hRI,?_⟩
  calc
    _=∫x,A.indicator (fun x=>inner ℝ (V x) (v x)) x := (integral_indicator hA).symm
    _=∫x,(∫t,f (x,t) ∂σ) := (integral_congr_ae hLeft).symm
    _=∫y,(∫t,g (y,t) ∂σ) := hPair
    _=∫y,(ball (0 : Domain n) 1).indicator B y := integral_congr_ae hRight
    _=_ := integral_indicator measurableSet_ball

end StationaryHarmonicMaps.Analysis

end
