/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.AlternatingCoexactNearFar
public import StationaryHarmonicMaps.Analysis.CoulombBoundaryCompensatedEnergy
public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration
public import StationaryHarmonicMaps.Analysis.UniformPowerGrowthBounds

/-!
# Complete power growth of the same alternating relative response

Compensated near energy and genuine far harmonic density give a recurrence
for the original unnormalized response energy. Full-ball compensation
supplies its initial value. Real-power iteration and actual recentering
then control every ambient center and every positive radius.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem response_ball_volume_ratio {n : ℕ} (a : Domain n) (r θ : ℝ)
    (hr : 0<r) (hθ : 0<θ) :
    volume.real (ball a (θ*r))*(volume.real (ball a r))⁻¹=θ^n := by
  have hV := (HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num : (0:ℝ)<1)).ne'
  rw [HolderToCK.ball_volume_real a (mul_pos hθ hr),HolderToCK.ball_volume_real a hr,mul_pow]
  field_simp [pow_ne_zero n hr.ne',hV]

/-- Original complete growth of the actual native gradient gives complete
all-center power growth of its same natural alternating coexact response. -/
theorem exists_alternating_coexact_full_real_power_growth (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k))
    (hAlt : ∀z : Ambient m,B z z=0)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃L : ℝ,0<L ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M K : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) →
      ∀ (Q : Domain n → Gradient n k) (v : Domain n → Ambient k),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>B (u x) (Du x i)-Q x i) →
        (∀ (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        ∀ (a : Domain n) (r : ℝ),0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L*η^2*K*r^ν := by
  obtain ⟨C,D,hC,hD,Hsplit⟩ :=
    exists_alternating_coexact_near_far_density_split n hn m k B hAlt ν
  obtain ⟨Ce,hCe,Henergy⟩ := exists_same_boundary_coexact_compensated_energy n hn m k B
  obtain ⟨θ,hθ,hθCap,hSmall⟩ := exists_positive_rpow_bound
    (C:=2*C) (p:=(n:ℝ)-ν) (a:=1/2) (cap:=1/256)
    (by positivity) (sub_pos.mpr hνn) (by norm_num) (by norm_num)
  have hθOne : θ<1 := lt_of_le_of_lt hθCap (by norm_num)
  have hPow : θ^n=θ^((n:ℝ)-ν)*θ^ν := by
    rw [← Real.rpow_natCast,← Real.rpow_add hθ]
    congr 1
    ring
  let ρ := 2*C*θ^n
  have hScale : ρ≤(1/2:ℝ)*θ^ν := by
    have H := mul_le_mul_of_nonneg_right hSmall (Real.rpow_nonneg hθ.le ν)
    simpa only [ρ,hPow,mul_assoc] using H
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hGap : ρ<θ^ν := hScale.trans_lt (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let r₀ : ℝ := 1/8
  have hr₀ : 0<r₀ := by norm_num [r₀]
  let A₀ := D*(2+2*C)
  let B₀ := Ce/r₀^ν
  let L₀ := (B₀+A₀/(θ^ν-ρ))/θ^ν
  let L₁ := 1+B₀+L₀
  have hA₀ : 0<A₀ := by dsimp only [A₀];positivity
  have hB₀ : 0<B₀ := div_pos hCe (Real.rpow_pos_of_pos hr₀ ν)
  have hL₀ : 0<L₀ := by dsimp only [L₀];positivity
  have hL₁ : 0<L₁ := by dsimp only [L₁];positivity
  have hB₀L : B₀≤L₁ := by dsimp only [L₁];linarith only [hL₀]
  have hL₀L : L₀≤L₁ := by dsimp only [L₁];linarith only [hB₀]
  have hCancel : B₀*r₀^ν=Ce := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr₀ ν).ne'
  refine ⟨(2:ℝ)^ν*L₁,mul_pos (Real.rpow_pos_of_pos (by norm_num) ν) hL₁,?_⟩
  intro u Du η M K hu hη hBound hCritical hK hGrowth Q v hQ hv hNatural
  let amp := η^2*K
  have hAmp : 0≤amp := mul_nonneg (sq_nonneg η) hK
  let Q₀ := (ball (0 : Domain n) 1).indicator Q
  have hQI : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball Q hQ)
  have hDuTotal : (∫x in ball (0 : Domain n) 1,hsNormSq (Du x))≤K := by
    have H := hGrowth 0 (mem_ball_self (by norm_num : (0:ℝ)<1)) 1 (by norm_num)
    simpa only [inter_self,Real.one_rpow,mul_one] using H
  have hQTotal : (∫x,hsNormSq (Q₀ x))≤Ce*amp := by
    rw [integral_hsNormSq_indicator _ measurableSet_ball]
    exact (Henergy u Du η M hu hη hBound hCritical Q v hQ hv hNatural).trans
      ((mul_le_mul_of_nonneg_left hDuTotal (by positivity : 0≤Ce*η^2)).trans_eq (by dsimp only [amp];ring))
  have hFullScale : Ce*amp=(B₀*amp)*r₀^ν := by
    calc
      _=(B₀*r₀^ν)*amp := congrArg (fun t : ℝ=>t*amp) hCancel.symm
      _=_ := by ring
  have hInside (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L₁*amp*r^ν := by
    let e := fun t : ℝ=>∫x in ball a t,hsNormSq (Q₀ x)
    have hFull (t : ℝ) : e t≤Ce*amp :=
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _=>hsNormSq_nonneg _) hQI).trans hQTotal
    have hStep (t : ℝ) (ht : 0<t) (htCap : t≤r₀) :
        e (θ*t)≤ρ*e t+(A₀*amp)*t^ν := by
      obtain ⟨g,h,hg0,_hh0,hgI,hhI,hDensity,hNear,hFar⟩ :=
        Hsplit u Du η M K hu hη hBound hCritical hK hGrowth Q v hQ hv hNatural
          a ha t ht htCap
      have hSub : ball a (θ*t)⊆ball a (t/256) :=
        ball_subset_ball (by nlinarith only [hθCap,ht])
      have hFarSmall := hFar.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
      have hFarI : (∫x in ball a (θ*t),h x)≤C*θ^n*(e t+D*amp*t^ν) := by
        calc
          _≤∫_x in ball a (θ*t),C*(volume.real (ball a t))⁻¹*(e t+D*amp*t^ν) := by
            apply integral_mono_ae hhI.integrableOn (integrableOn_const measure_ball_ne_top)
            filter_upwards [hFarSmall] with x hx
            exact hx.trans_eq (by dsimp only [amp,e,Q₀];ring)
          _=(volume.real (ball a (θ*t))*(volume.real (ball a t))⁻¹)*(C*(e t+D*amp*t^ν)) := by
            rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
            ring
          _=C*θ^n*(e t+D*amp*t^ν) := by
            rw [response_ball_volume_ratio a t θ ht hθ]
            ring
      have hNearI : (∫x in ball a (θ*t),g x)≤D*amp*t^ν := by
        have H : (∫x in ball a (θ*t),g x)≤D*η^2*K*t^ν :=
          (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hg0) hgI).trans hNear
        simpa only [amp,mul_assoc] using H
      have hRec : e (θ*t)≤ρ*e t+(D*(2+2*C*θ^n))*amp*t^ν := by
        calc
          _≤∫x in ball a (θ*t),2*g x+2*h x :=
            integral_mono hQI.integrableOn ((hgI.const_mul 2).add (hhI.const_mul 2)).integrableOn hDensity
          _=2*(∫x in ball a (θ*t),g x)+2*(∫x in ball a (θ*t),h x) := by
            rw [integral_add (hgI.integrableOn.const_mul 2) (hhI.integrableOn.const_mul 2),
              integral_const_mul,integral_const_mul]
          _≤2*(D*amp*t^ν)+2*(C*θ^n*(e t+D*amp*t^ν)) :=
            add_le_add (mul_le_mul_of_nonneg_left hNearI (by norm_num))
              (mul_le_mul_of_nonneg_left hFarI (by norm_num))
          _=_ := by dsimp only [ρ];ring
      have hCoeff : D*(2+2*C*θ^n)≤A₀ := by
        have hPowOne := pow_le_one₀ hθ.le hθOne.le (n:=n)
        have H := add_le_add_left
          (mul_le_mul_of_nonneg_left hPowOne (by positivity : 0≤2*C)) 2
        exact mul_le_mul_of_nonneg_left (by simpa only [mul_one,add_comm] using H) hD.le
      exact hRec.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff hAmp) (Real.rpow_nonneg ht.le ν)))
    have hResult : e r≤L₁*amp*r^ν := by
      by_cases hrCap : r≤r₀
      · have hMono (s t : ℝ) (_hs : 0<s) (hst : s≤t) (_ht : t≤r₀) : e s≤e t :=
          integral_mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hst))
            (Eventually.of_forall fun _=>hsNormSq_nonneg _) hQI.integrableOn
        have hBase : e r₀≤(B₀*amp)*r₀^ν := (hFull r₀).trans_eq hFullScale
        have H := all_radius_rpow_bound_of_recurrence e hν hθ hθOne hρ hGap
          (mul_nonneg hA₀.le hAmp) (mul_nonneg hB₀.le hAmp) hr₀ hMono hBase hStep r hr hrCap
        have H' : e r≤L₀*amp*r^ν := H.trans_eq (by dsimp only [L₀];ring)
        exact H'.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hL₀L hAmp) (Real.rpow_nonneg hr.le ν))
      · have hScale : r₀^ν≤r^ν := Real.rpow_le_rpow hr₀.le (not_le.mp hrCap).le hν
        calc
          _≤Ce*amp := hFull r
          _=(B₀*amp)*r₀^ν := hFullScale
          _≤(B₀*amp)*r^ν := mul_le_mul_of_nonneg_left hScale (mul_nonneg hB₀.le hAmp)
          _≤L₁*amp*r^ν := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hB₀L hAmp) (Real.rpow_nonneg hr.le ν)
    exact (setIntegral_hsNormSq_indicator _ measurableSet_ball _ Q).symm.le.trans hResult
  intro a r hr
  have H := integral_hsNormSq_inter_le_of_uniform_power_growth Q (ball (0 : Domain n) 1)
    hQ (L₁*amp) ν (mul_nonneg hL₁.le hAmp) hInside a hr
  exact H.trans_eq (by dsimp only [amp];ring)

end StationaryHarmonicMaps.Analysis

end
