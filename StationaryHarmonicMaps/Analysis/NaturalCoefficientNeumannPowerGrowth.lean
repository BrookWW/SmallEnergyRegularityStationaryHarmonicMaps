/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannInitialResponse
public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannNearFar
public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration
public import StationaryHarmonicMaps.Analysis.UniformPowerGrowthBounds
public import StationaryHarmonicMaps.Analysis.EffectiveCoulombConstants

/-!
# Complete stronger growth of the actual natural-coefficient Neumann response

The original natural critical coefficient and original stronger native map
construct their actual mean-zero Neumann response. Genuine localized and
far fields give its recurrence. The internally produced full-ball energy
supplies the initial value. Real-power iteration and actual recentering
control the same original gradient at every center and every radius.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem natural_response_ball_volume_ratio {n : ℕ} (a : Domain n) (r θ : ℝ)
    (hr : 0<r) (hθ : 0<θ) :
    volume.real (ball a (θ*r))*(volume.real (ball a r))⁻¹=θ^n := by
  have hV := (HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num : (0 : ℝ)<1)).ne'
  rw [HolderToCK.ball_volume_real a (mul_pos hθ hr),HolderToCK.ball_volume_real a hr,mul_pow]
  field_simp [pow_ne_zero n hr.ne',hV]

/-- Original full natural coefficient data and original stronger native
map data construct the actual mean-zero Neumann response and its complete
all-center stronger power growth. No response, initial energy, recurrence
or desired growth bound is assumed. -/
theorem exists_natural_coefficient_neumann_full_power_growth
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃L : ℝ,0<L ∧ ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀(ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-2+γ)) →
      ∃(g : Domain n → Ambient q) (Q : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) g Q ∧
        (∫x in ball (0 : Domain n) 1,g x)=0 ∧
        (∀i,MemLp (fun x=>B (Z x i) (u x)) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
            ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
        ∀(a : Domain n) (r : ℝ),0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) := by
  obtain ⟨C,D,hC,hD,Hsplit⟩ := exists_natural_coefficient_neumann_near_far_split n hn γ hγ hγTwo
  obtain ⟨Ce,hCe,Hinitial⟩ := exists_natural_coefficient_neumann_initial_response n hn γ hγ hγTwo
  let ν := (n : ℝ)-2+γ
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hν : 0≤ν := by dsimp only [ν];linarith only [hnReal,hγ]
  have hνn : ν<(n : ℝ) := by dsimp only [ν];linarith only [hγTwo]
  obtain ⟨θ,hθ,hθCap,hSmall⟩ := exists_positive_rpow_bound
    (C:=2*C) (p:=(n : ℝ)-ν) (a:=1/2) (cap:=1/256)
    (by positivity) (sub_pos.mpr hνn) (by norm_num) (by norm_num)
  have hθOne : θ<1 := lt_of_le_of_lt hθCap (by norm_num)
  have hPow : θ^n=θ^((n : ℝ)-ν)*θ^ν := by
    rw [←Real.rpow_natCast,←Real.rpow_add hθ]
    congr 1
    ring
  let ρ := 2*C*θ^n
  have hScale : ρ≤(1/2 : ℝ)*θ^ν := by
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
  refine ⟨(2 : ℝ)^ν*L₁,mul_pos (Real.rpow_pos_of_pos (by norm_num) ν) hL₁,?_⟩
  intro m k q B Z u Du η Ku hZ hNatural hu hη hCritical hKu hGrowth
  obtain ⟨g,Q,hg,hMean,hRaw,hEnergy,hTests⟩ :=
    Hinitial m k q B Z u Du η Ku hZ hNatural hu hη hCritical hKu hGrowth
  let amp := ‖B‖^2*η^2*Ku
  have hAmp : 0≤amp := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hKu
  let Q₀ := (ball (0 : Domain n) 1).indicator Q
  have hQI : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball Q hg.2.2)
  have hQTotal : (∫x,hsNormSq (Q₀ x))≤Ce*amp := by
    rw [integral_hsNormSq_indicator _ measurableSet_ball]
    exact hEnergy.trans_eq (by dsimp only [amp];ring)
  have hFullScale : Ce*amp=(B₀*amp)*r₀^ν := by
    calc
      _=(B₀*r₀^ν)*amp := congrArg (fun t : ℝ=>t*amp) hCancel.symm
      _=_ := by ring
  have hInside (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L₁*amp*r^ν := by
    let e := fun t : ℝ=>∫x in ball a t,hsNormSq (Q₀ x)
    have hFull (t : ℝ) : e t≤Ce*amp :=
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _=>hsNormSq_nonneg _) hQI).trans hQTotal
    have hStep (t : ℝ) (ht : 0<t) (_htCap : t≤r₀) :
        e (θ*t)≤ρ*e t+(A₀*amp)*t^ν := by
      obtain ⟨near,far,hNear0,_hFar0,hNearI,hFarI,hDensity,hNear,hFar⟩ :=
        Hsplit m k q B Z u Du η Ku hZ hNatural hu hCritical hKu hGrowth g Q hg
          (fun ψ Dψ hψ=>(hTests ψ Dψ hψ).2.2) a ha t ht
      have hSub : ball a (θ*t)⊆ball a (t/256) :=
        ball_subset_ball (by nlinarith only [hθCap,ht])
      have hFarSmall := hFar.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
      have hFarSmallIntegral : (∫x in ball a (θ*t),far x)≤C*θ^n*(e t+D*amp*t^ν) := by
        calc
          _≤∫_x in ball a (θ*t),C*(volume.real (ball a t))⁻¹*(e t+D*amp*t^ν) := by
            apply integral_mono_ae hFarI.integrableOn (integrableOn_const measure_ball_ne_top)
            filter_upwards [hFarSmall] with x hx
            exact hx.trans_eq (by dsimp only [amp,e,Q₀,ν];ring)
          _=(volume.real (ball a (θ*t))*(volume.real (ball a t))⁻¹)*(C*(e t+D*amp*t^ν)) := by
            rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
            ring
          _=C*θ^n*(e t+D*amp*t^ν) := by
            rw [natural_response_ball_volume_ratio a t θ ht hθ]
            ring
      have hNearSmallIntegral : (∫x in ball a (θ*t),near x)≤D*amp*t^ν := by
        have H : (∫x in ball a (θ*t),near x)≤D*‖B‖^2*η^2*Ku*t^((n : ℝ)-2+γ) :=
          (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hNear0) hNearI).trans hNear
        simpa only [amp,ν,mul_assoc] using H
      have hRec : e (θ*t)≤ρ*e t+(D*(2+2*C*θ^n))*amp*t^ν := by
        calc
          _≤∫x in ball a (θ*t),2*near x+2*far x :=
            integral_mono hQI.integrableOn ((hNearI.const_mul 2).add (hFarI.const_mul 2)).integrableOn hDensity
          _=2*(∫x in ball a (θ*t),near x)+2*(∫x in ball a (θ*t),far x) := by
            rw [integral_add (hNearI.integrableOn.const_mul 2) (hFarI.integrableOn.const_mul 2),
              integral_const_mul,integral_const_mul]
          _≤2*(D*amp*t^ν)+2*(C*θ^n*(e t+D*amp*t^ν)) :=
            add_le_add (mul_le_mul_of_nonneg_left hNearSmallIntegral (by norm_num))
              (mul_le_mul_of_nonneg_left hFarSmallIntegral (by norm_num))
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
      · have hScaleRadius : r₀^ν≤r^ν := Real.rpow_le_rpow hr₀.le (not_le.mp hrCap).le hν
        calc
          _≤Ce*amp := hFull r
          _=(B₀*amp)*r₀^ν := hFullScale
          _≤(B₀*amp)*r^ν := mul_le_mul_of_nonneg_left hScaleRadius (mul_nonneg hB₀.le hAmp)
          _≤L₁*amp*r^ν := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hB₀L hAmp) (Real.rpow_nonneg hr.le ν)
    exact (setIntegral_hsNormSq_indicator _ measurableSet_ball _ Q).symm.le.trans hResult
  refine ⟨g,Q,hg,hMean,hRaw,hTests,?_⟩
  intro a r hr
  have H := integral_hsNormSq_inter_le_of_uniform_power_growth Q (ball (0 : Domain n) 1)
    hg.2.2 (L₁*amp) ν (mul_nonneg hL₁.le hAmp) hInside a hr
  exact H.trans_eq (by dsimp only [amp,ν];ring)

@[expose] def effectiveNaturalNeumannPowerConstant (n : ℕ) : ℚ :=
  EffectiveCoulomb.naturalPowerBound n (effectiveNaturalFarConstant n : ℚ)
    (effectiveNaturalNearEnergyConstant n : ℚ) (effectiveNaturalInitialEnergyConstant n : ℚ)

theorem effectiveNaturalNeumannPowerConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveNaturalNeumannPowerConstant n :=
  EffectiveCoulomb.naturalPowerBound_pos n hn (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Original full natural coefficient data and original stronger native
map data construct the actual mean-zero Neumann response and its complete
all-center stronger power growth. No response, initial energy, recurrence
or desired growth bound is assumed. -/
theorem effective_natural_coefficient_neumann_full_power_growth
    (n : ℕ) (hn : 2≤n) :
    ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀(ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-1)) →
      ∃(g : Domain n → Ambient q) (Q : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) g Q ∧
        (∫x in ball (0 : Domain n) 1,g x)=0 ∧
        (∀i,MemLp (fun x=>B (Z x i) (u x)) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
            ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
        ∀(a : Domain n) (r : ℝ),0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤(effectiveNaturalNeumannPowerConstant n : ℝ)*‖B‖^2*η^2*Ku*r^((n : ℝ)-1) := by
  let C : ℝ := effectiveNaturalFarConstant n
  let D : ℝ := effectiveNaturalNearEnergyConstant n
  let Ce : ℝ := effectiveNaturalInitialEnergyConstant n
  have hC : 0 < C := effectiveNaturalFarConstant_pos n
  have hD : 0 < D := effectiveNaturalNearEnergyConstant_pos n
  have hCe : 0 < Ce := effectiveNaturalInitialEnergyConstant_pos n
  have Hsplit := effective_natural_coefficient_neumann_near_far_split n hn
  have Hinitial := effective_natural_coefficient_neumann_initial_response n hn
  let ν := (n : ℝ)-1
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hν : 0≤ν := by dsimp only [ν];linarith only [hnReal]
  have hνn : ν<(n : ℝ) := by dsimp only [ν];linarith
  let t := EffectiveCoulomb.naturalPowerScale (effectiveNaturalFarConstant n : ℚ)
  let θ : ℝ := t
  have ht : 0 < t := EffectiveCoulomb.naturalPowerScale_pos (Nat.cast_nonneg _)
  have hθ : 0 < θ := by
    change 0 < (t : ℝ)
    exact_mod_cast ht
  have hθCap : θ ≤ 1 / 256 := by
    have H : (t : ℝ) ≤ ((1 / 256 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (EffectiveCoulomb.naturalPowerScale_le (Nat.cast_nonneg _))
    norm_num at H ⊢
    exact H
  have hSmall : 2 * C * θ ^ ((n : ℝ) - ν) ≤ 1 / 2 := by
    rw [show (n : ℝ) - ν = 1 by dsimp only [ν]; ring, Real.rpow_one]
    have H : ((2 * (effectiveNaturalFarConstant n : ℚ) * t : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (EffectiveCoulomb.naturalPowerScale_absorbs (Nat.cast_nonneg _))
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] at H
    exact H
  have hθOne : θ<1 := lt_of_le_of_lt hθCap (by norm_num)
  have hPow : θ^n=θ^((n : ℝ)-ν)*θ^ν := by
    rw [←Real.rpow_natCast,←Real.rpow_add hθ]
    congr 1
    ring
  let ρ := 2*C*θ^n
  have hScale : ρ≤(1/2 : ℝ)*θ^ν := by
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
  have hνNat : ν = ((n - 1 : ℕ) : ℝ) := by
    dsimp only [ν]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hβ : B₀ = Ce * (8 : ℝ) ^ (n - 1) := by
    dsimp only [B₀, r₀]
    rw [hνNat, Real.rpow_natCast, one_div_pow, div_div_eq_mul_div, div_one]
  have heq : (effectiveNaturalNeumannPowerConstant n : ℝ) = (2 : ℝ) ^ ν * L₁ := by
    simp only [effectiveNaturalNeumannPowerConstant, EffectiveCoulomb.naturalPowerBound,
      Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, L₁, L₀, A₀, ρ, hβ,
      hνNat, Real.rpow_natCast, C, D, Ce, θ, t]
  rw [heq]
  intro m k q B Z u Du η Ku hZ hNatural hu hη hCritical hKu hGrowth
  obtain ⟨g,Q,hg,hMean,hRaw,hEnergy,hTests⟩ :=
    Hinitial m k q B Z u Du η Ku hZ hNatural hu hη hCritical hKu hGrowth
  let amp := ‖B‖^2*η^2*Ku
  have hAmp : 0≤amp := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hKu
  let Q₀ := (ball (0 : Domain n) 1).indicator Q
  have hQI : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball Q hg.2.2)
  have hQTotal : (∫x,hsNormSq (Q₀ x))≤Ce*amp := by
    rw [integral_hsNormSq_indicator _ measurableSet_ball]
    exact hEnergy.trans_eq (by dsimp only [amp];ring)
  have hFullScale : Ce*amp=(B₀*amp)*r₀^ν := by
    calc
      _=(B₀*r₀^ν)*amp := congrArg (fun t : ℝ=>t*amp) hCancel.symm
      _=_ := by ring
  have hInside (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L₁*amp*r^ν := by
    let e := fun t : ℝ=>∫x in ball a t,hsNormSq (Q₀ x)
    have hFull (t : ℝ) : e t≤Ce*amp :=
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _=>hsNormSq_nonneg _) hQI).trans hQTotal
    have hStep (t : ℝ) (ht : 0<t) (_htCap : t≤r₀) :
        e (θ*t)≤ρ*e t+(A₀*amp)*t^ν := by
      obtain ⟨near,far,hNear0,_hFar0,hNearI,hFarI,hDensity,hNear,hFar⟩ :=
        Hsplit m k q B Z u Du η Ku hZ hNatural hu hCritical hKu hGrowth g Q hg
          (fun ψ Dψ hψ=>(hTests ψ Dψ hψ).2.2) a ha t ht
      have hSub : ball a (θ*t)⊆ball a (t/256) :=
        ball_subset_ball (by nlinarith only [hθCap,ht])
      have hFarSmall := hFar.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
      have hFarSmallIntegral : (∫x in ball a (θ*t),far x)≤C*θ^n*(e t+D*amp*t^ν) := by
        calc
          _≤∫_x in ball a (θ*t),C*(volume.real (ball a t))⁻¹*(e t+D*amp*t^ν) := by
            apply integral_mono_ae hFarI.integrableOn (integrableOn_const measure_ball_ne_top)
            filter_upwards [hFarSmall] with x hx
            exact hx.trans_eq (by dsimp only [amp,e,Q₀,ν];ring)
          _=(volume.real (ball a (θ*t))*(volume.real (ball a t))⁻¹)*(C*(e t+D*amp*t^ν)) := by
            rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
            ring
          _=C*θ^n*(e t+D*amp*t^ν) := by
            rw [natural_response_ball_volume_ratio a t θ ht hθ]
            ring
      have hNearSmallIntegral : (∫x in ball a (θ*t),near x)≤D*amp*t^ν := by
        have H : (∫x in ball a (θ*t),near x)≤D*‖B‖^2*η^2*Ku*t^((n : ℝ)-1) :=
          (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hNear0) hNearI).trans hNear
        simpa only [amp,ν,mul_assoc] using H
      have hRec : e (θ*t)≤ρ*e t+(D*(2+2*C*θ^n))*amp*t^ν := by
        calc
          _≤∫x in ball a (θ*t),2*near x+2*far x :=
            integral_mono hQI.integrableOn ((hNearI.const_mul 2).add (hFarI.const_mul 2)).integrableOn hDensity
          _=2*(∫x in ball a (θ*t),near x)+2*(∫x in ball a (θ*t),far x) := by
            rw [integral_add (hNearI.integrableOn.const_mul 2) (hFarI.integrableOn.const_mul 2),
              integral_const_mul,integral_const_mul]
          _≤2*(D*amp*t^ν)+2*(C*θ^n*(e t+D*amp*t^ν)) :=
            add_le_add (mul_le_mul_of_nonneg_left hNearSmallIntegral (by norm_num))
              (mul_le_mul_of_nonneg_left hFarSmallIntegral (by norm_num))
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
      · have hScaleRadius : r₀^ν≤r^ν := Real.rpow_le_rpow hr₀.le (not_le.mp hrCap).le hν
        calc
          _≤Ce*amp := hFull r
          _=(B₀*amp)*r₀^ν := hFullScale
          _≤(B₀*amp)*r^ν := mul_le_mul_of_nonneg_left hScaleRadius (mul_nonneg hB₀.le hAmp)
          _≤L₁*amp*r^ν := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hB₀L hAmp) (Real.rpow_nonneg hr.le ν)
    exact (setIntegral_hsNormSq_indicator _ measurableSet_ball _ Q).symm.le.trans hResult
  refine ⟨g,Q,hg,hMean,hRaw,hTests,?_⟩
  intro a r hr
  have H := integral_hsNormSq_inter_le_of_uniform_power_growth Q (ball (0 : Domain n) 1)
    hg.2.2 (L₁*amp) ν (mul_nonneg hL₁.le hAmp) hInside a hr
  exact H.trans_eq (by dsimp only [amp,ν];ring)

end StationaryHarmonicMaps.Analysis

end
